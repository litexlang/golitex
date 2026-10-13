use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_by_induc::ByUnfoldHaveFnByInducApplicationObjectDefinitionProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_recursive_unfold_result(
        &self,
        fact: &EqualFact,
        proof: &ByUnfoldHaveFnByInducApplicationObjectDefinitionProof,
        parent_wd: Option<&EqualFactWellDefinedProof>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::EqualFact(residual)) =
            source_subject(&proof.residual_equal)?
        else {
            return Err(LeanCompileError::unsupported(
                "RecursiveUnfold/ResidualFamily",
            ));
        };
        if residual.left != proof.expanded_body {
            return Err(LeanCompileError::new(
                "RecursiveUnfold/ResidualBody",
                "The residual must start at the selected original expanded body.",
            ));
        }
        let (original, wd, reversed) = if residual.right == fact.right {
            (&fact.left, parent_wd.map(|w| &w.left), false)
        } else if residual.right == fact.left {
            (&fact.right, parent_wd.map(|w| &w.right), true)
        } else {
            return Err(LeanCompileError::new(
                "RecursiveUnfold/ResidualEndpoint",
                "The residual must end at the original equality's other endpoint.",
            ));
        };
        let Obj::FnObj(application) = original else {
            return Err(LeanCompileError::unsupported(
                "RecursiveUnfold/ApplicationSubject",
            ));
        };
        let FnObjHead::Identifier(IdentifierObj::Plain { id, .. }) = application.head.as_ref()
        else {
            return Err(LeanCompileError::unsupported(
                "RecursiveUnfold/ApplicationHead",
            ));
        };
        let (declaration, _, _) = position.visible_recursive_function(id)?;
        if application.body.len() != 1
            || application.body[0].len() != 1
            || proof.selected_case_path.len() != 1
        {
            return Err(LeanCompileError::unsupported(
                "RecursiveUnfold/UnaryLeafPath",
            ));
        }
        let selected = &proof.selected_case_path[0];
        let Some(case) = declaration.statement.cases.get(selected.case_index) else {
            return Err(LeanCompileError::new(
                "RecursiveUnfold/CaseIndex",
                "The recorded path does not index this source declaration.",
            ));
        };
        let crate::ast::stmt::HaveFnByInducCaseBody::EqualTo(body) = &case.body else {
            return Err(LeanCompileError::unsupported("RecursiveUnfold/NestedCases"));
        };
        let parameters = declaration
            .statement
            .fn_set_clause
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect::<Vec<_>>();
        if parameters.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "RecursiveUnfold/ParameterArity",
            ));
        }
        let substitution =
            HashMap::from([(parameters[0].id, application.body[0][0].as_ref().clone())]);
        if !instantiated_object_matches(body, &proof.expanded_body, &substitution)
            || !instantiated_fact_matches(
                &and_chain_as_fact(&case.case_fact),
                &source_subject(&selected.guard)?,
                &substitution,
            )
        {
            return Err(LeanCompileError::new("RecursiveUnfold/SelectedPathSubject", "The selected guard and expanded body differ from the exact source leaf instantiated at these arguments."));
        }
        let scope = SourcePosition::new(Some(position), SourceOwner::RecursiveUnfold(proof), 0);
        let guard = self.compile_verify(&selected.guard, &scope)?;
        let completed = SourcePosition { before: 1, ..scope };
        let residual = self.compile_verify(&proof.residual_equal, &completed)?;
        let emit = |wd: &ObjWellDefinedProof, site: &SourcePosition<'_>| {
            ensure_object(original, wd)?;
            let ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            } = wd
            else {
                return Err(LeanCompileError::unsupported(
                    "RecursiveUnfold/ApplicationFormation",
                ));
            };
            let call_scope = SourcePosition::new(Some(site), SourceOwner::WD(wd), 0);
            let (call, _) = self.compile_fn_call_with_return(application, call, &call_scope)?;
            let stored_id = declaration
                .store_and_infer_result
                .case_defining_fact_ids
                .get(selected.case_index)
                .ok_or_else(|| {
                    LeanCompileError::new(
                        "RecursiveUnfold/CaseProducer",
                        "The selected source leaf has no stored equation producer.",
                    )
                })?;
            let (_, case_equation) = self.cited_fact_reference(*stored_id, position)?;
            let equality = format!("(by\n  let _checked_call := {call}\n  have _checked_case_guard : {} := {}\n  have _selected_beta := {case_equation} _checked_call.val.argument _checked_call.wd.2.1 _checked_case_guard\n  exact _selected_beta.trans {})", guard.0, guard.1, residual.1);
            Ok(if reversed {
                format!("({equality}).symm")
            } else {
                equality
            })
        };
        if let Some(
            wd @ ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(_),
                ..
            },
        ) = wd
        {
            emit(wd, position)
        } else {
            position
                .with_visible_wd(original, &mut |wd, producer| emit(wd, producer))?
                .ok_or_else(|| {
                    LeanCompileError::new(
                        "RecursiveUnfold/WDProducer",
                        "The selected unfold has no original application WD producer.",
                    )
                })
        }
    }
}
