use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ResolvedTheoremCallee};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_release_and_expand_statement(
        &self,
        result: &ExecReleaseAndExpandStmtResult,
        position: &SourcePosition<'_>,
        index: usize,
        local: bool,
    ) -> Result<String, LeanCompileError> {
        let ExecReleaseAndExpandStmtResult::Thm(result) = result else {
            return Err(LeanCompileError::unsupported(
                "ReleaseAndExpand/OtherFamily",
            ));
        };
        let ExecReleaseThmStmtResult::Success(proof) = result else {
            return Err(LeanCompileError::new(
                "ReleaseThm/Failed",
                "A failed release is not theorem evidence.",
            ));
        };
        let ResolvedTheoremCallee::UserTheorem(declaration) = &proof.callee else {
            return Err(LeanCompileError::unsupported("ReleaseThm/Callee"));
        };
        let AtomicName::Plain { name } = &proof.call.name else {
            return Err(LeanCompileError::unsupported("ReleaseThm/QualifiedCallee"));
        };
        let (registered, declaration_position, _) = position.visible_theorem(name)?;
        if registered != declaration
            || name != &declaration.name
            || proof.builtin.is_some()
            || proof.function_domain.is_some()
        {
            return Err(LeanCompileError::new(
                "ReleaseThm/CalleeCapture",
                "The captured callee must be the exact preceding compiled user theorem.",
            ));
        }
        if proof.stored_wd.len() != proof.stored.len() {
            return Err(LeanCompileError::new(
                "ReleaseThm/CallerStages",
                "Every returned package needs its original caller WD stage before its store.",
            ));
        }
        let invocation = SourcePosition::new(Some(position), SourceOwner::ThmRelease(proof), 0);
        let (definitions, application, facts) = self.compile_user_theorem_instance(
            &proof.call,
            &proof.type_proofs,
            &proof.type_stores,
            &proof.dom_proofs,
            &proof.dom_stores,
            &proof.conclusions_wd,
            &proof.stored,
            registered,
            &declaration_position,
            &invocation,
        )?;
        let mut emitted = Vec::new();
        for (returned_index, ((fact, wd), store)) in facts
            .iter()
            .zip(&proof.stored_wd)
            .zip(&proof.stored)
            .enumerate()
        {
            // The executor closed the invocation scope before these original
            // caller WD/store pairs. Formation and export use only that cursor.
            let formation = SourcePosition {
                before: 2 * returned_index,
                ..*position
            };
            self.compile_fact_wd(wd, fact, &formation)?;
            let formed = SourcePosition {
                before: 2 * returned_index + 1,
                ..*position
            };
            let proposition = self.fact_proposition(fact, &formed)?;
            let conclusion = conjunction_projection(&application, returned_index, facts.len());
            let evidence = format!(
                "(by\n  {}\n  exact {conclusion}\n)",
                definitions.join("\n").replace('\n', "\n  ")
            );
            let retained_primary = matches!(proof.call.arguments, TheoremCallArguments::Bare)
                && fact.fact_id() == registered.fact.fact_id();
            if !retained_primary {
                emitted.push(self.emit_fact(
                    fact,
                    (proposition.clone(), evidence),
                    index,
                    local,
                    &formed,
                )?);
            }
            let published = SourcePosition {
                before: 2 * returned_index + 2,
                ..*position
            };
            let name = format!("h_{}", fact.fact_id().value());
            let reference = if retained_primary {
                application.clone()
            } else if local {
                name
            } else {
                self.context_application(&name, &published)
            };
            emitted.extend(self.compile_stored_inferences(
                store,
                fact,
                &(proposition, reference),
                &published,
            )?);
        }
        Ok(emitted.join("\n\n"))
    }
}
