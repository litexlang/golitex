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
        if let ExecReleaseAndExpandStmtResult::ZornLemma(result) = result {
            return self.compile_zorn(result, position, index, local);
        }
        if let ExecReleaseAndExpandStmtResult::AxiomOfChoice(result) = result {
            return self.compile_choice(result, position, index, local);
        }
        if let ExecReleaseAndExpandStmtResult::RegularityAxiom(result) = result {
            return self.compile_regularity(result, position, index, local);
        }
        if let ExecReleaseAndExpandStmtResult::ExpandRange(result) = result {
            return self.compile_expand_range_statement(result, position, index, local);
        }
        if let ExecReleaseAndExpandStmtResult::ObjDef(result) = result {
            return self.compile_release_obj_definition(result, position, index, local);
        }
        if let ExecReleaseAndExpandStmtResult::TupleDef(result) = result {
            return self.compile_release_tuple_definition(result, position, index, local);
        }
        if let ExecReleaseAndExpandStmtResult::StructDef(result) = result {
            return self.compile_release_struct_definition(result, position);
        }
        if let ExecReleaseAndExpandStmtResult::CartDef(result) = result {
            return self.compile_release_cart_definition(result, position, index, local);
        }
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
        let invocation = SourcePosition::new(Some(position), SourceOwner::ThmRelease(proof), 0);
        let (definitions, application, facts, retained_fact_id) =
            if matches!(proof.callee, ResolvedTheoremCallee::Builtin) {
                let (definitions, application, facts) = if proof.builtin.as_ref().is_some_and(|b| {
                    b.theorem == crate::builtin_theorem::BuiltinTheoremId::TupleEqualFromCoordinates
                }) {
                    self.compile_builtin_tuple_theorem(proof, &invocation)?
                } else {
                    self.compile_builtin_membership_theorem(
                        &proof.call,
                        proof.builtin.as_ref(),
                        &proof.theorem_derivation,
                        &proof.type_proofs,
                        &proof.type_stores,
                        proof.function_domain.as_ref(),
                        &proof.dom_proofs,
                        &proof.dom_stores,
                        &proof.conclusions_wd,
                        &invocation,
                    )?
                };
                (definitions, application, facts, None)
            } else {
                if proof.builtin.is_some() || proof.function_domain.is_some() {
                    return Err(LeanCompileError::unsupported("ReleaseThm/CalleeCapture"));
                }
                let (registered, reference) =
                    position.user_callee_reference(&proof.call.name, &proof.callee)?;
                let reference =
                    self.compile_local_forall_citation(registered.fact_id(), reference, position)?;
                if proof.stored_wd.len() != proof.stored.len() {
                    return Err(LeanCompileError::new(
                "ReleaseThm/CallerStages",
                "Every returned package needs its original caller WD stage before its store.",
            ));
                }
                let (definitions, application, facts) = self.compile_user_theorem_instance(
                    &proof.call,
                    &proof.type_proofs,
                    &proof.type_stores,
                    &proof.dom_proofs,
                    &proof.dom_stores,
                    &proof.conclusions_wd,
                    &proof.stored,
                    &registered,
                    reference,
                    &invocation,
                )?;
                (definitions, application, facts, Some(registered.fact_id()))
            };
        if proof.stored_wd.len() != facts.len() || proof.stored.len() != facts.len() {
            return Err(LeanCompileError::unsupported("ReleaseThm/CallerStages"));
        }
        let mut emitted = Vec::new();
        for (returned_index, ((fact, wd), store)) in facts
            .iter()
            .zip(&proof.stored_wd)
            .zip(&proof.stored)
            .enumerate()
        {
            self.validate_store(&store.store, fact)?;
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
            let captured_formation =
                SourcePosition::new(Some(&formed), SourceOwner::FactWD(wd), usize::MAX);
            let proposition = self.fact_proposition(fact, &captured_formation)?;
            let conclusion = conjunction_projection(&application, returned_index, facts.len());
            let evidence = format!(
                "(by\n  {}\n  exact {conclusion}\n)",
                definitions.join("\n").replace('\n', "\n  ")
            );
            let retained_primary = matches!(proof.call.arguments, TheoremCallArguments::Bare)
                && Some(fact.fact_id()) == retained_fact_id;
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
