use super::compile_have_fn_cases_result::piecewise_signature;
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_have_fn_equal_case_by_case::ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::well_defined_result::EqualFactWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_piecewise_unfold_result(
        &self,
        fact: &EqualFact,
        proof: &ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof,
        parent_wd: Option<&EqualFactWellDefinedProof>,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::EqualFact(residual)) =
            source_subject(&proof.residual_equal)?
        else {
            return Err(LeanCompileError::unsupported(
                "PiecewiseUnfold/ResidualFamily",
            ));
        };
        if residual.left != proof.expanded_body {
            return Err(LeanCompileError::unsupported(
                "PiecewiseUnfold/ResidualBody",
            ));
        }
        let (original, wd, reversed) = if residual.right == fact.right {
            (&fact.left, parent_wd.map(|p| &p.detailed_ref().left), false)
        } else if residual.right == fact.left {
            (
                &fact.right,
                parent_wd.map(|p| &p.detailed_ref().right),
                true,
            )
        } else {
            return Err(LeanCompileError::unsupported(
                "PiecewiseUnfold/ResidualEndpoint",
            ));
        };
        let Obj::FnObj(application) = original else {
            return Err(LeanCompileError::unsupported("PiecewiseUnfold/Application"));
        };
        let FnObjHead::Identifier(IdentifierObj::Plain { id, .. }) = application.head.as_ref()
        else {
            return Err(LeanCompileError::unsupported("PiecewiseUnfold/Head"));
        };
        let (declaration, _) = position.visible_piecewise_function(id)?;
        let signature = piecewise_signature(declaration);
        let parameters = signature
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect::<Vec<_>>();
        if application.body.len() != 1 || application.body[0].len() != parameters.len() {
            return Err(LeanCompileError::unsupported("PiecewiseUnfold/Arity"));
        }
        let index = proof.matched_case_index;
        let guard = declaration
            .statement
            .cases
            .get(index)
            .ok_or_else(|| LeanCompileError::unsupported("PiecewiseUnfold/CaseIndex"))?;
        let body = declaration
            .statement
            .equal_tos
            .get(index)
            .ok_or_else(|| LeanCompileError::unsupported("PiecewiseUnfold/CaseBody"))?;
        let substitution = parameters
            .iter()
            .zip(&application.body[0])
            .map(|(p, a)| (p.id, a.as_ref().clone()))
            .collect::<HashMap<_, _>>();
        if !instantiated_object_matches(body, &proof.expanded_body, &substitution)
            || !instantiated_fact_matches(
                &and_chain_as_fact(guard),
                &source_subject(&proof.guard)?,
                &substitution,
            )
        {
            return Err(LeanCompileError::unsupported(
                "PiecewiseUnfold/SelectedSubject",
            ));
        }
        let scope = SourcePosition::new(Some(position), SourceOwner::PiecewiseUnfold(proof), 0);
        let guard = self.compile_verify(&proof.guard, &scope)?;
        let residual = self.compile_verify(
            &proof.residual_equal,
            &SourcePosition { before: 1, ..scope },
        )?;
        let emit = |wd: &ObjWellDefinedProof, site: &SourcePosition<'_>| {
            ensure_object(original, wd)?;
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            } = (wd).detailed_ref()
            else {
                return Err(LeanCompileError::unsupported("PiecewiseUnfold/Formation"));
            };
            if !matches!(&call.domain_fn_set,Some(FnObjDomainFnSetEvidence::InFunctionSet {fn_set,..}) if fn_set == &signature)
            {
                return Err(LeanCompileError::unsupported("PiecewiseUnfold/Signature"));
            }
            let call_scope = SourcePosition::new(Some(site), SourceOwner::WD(wd), 0);
            // This validates the actual ordered children, requirements and exact
            // function membership citation before projecting its call theorem.
            let (call_term, _, _) =
                self.compile_fn_first_call_with_member(application, call, &call_scope)?;
            let stored = declaration
                .store_and_infer_result
                .case_defining_fact_ids
                .get(index)
                .ok_or_else(|| LeanCompileError::unsupported("PiecewiseUnfold/EquationProducer"))?;
            let (_, equation) = self.cited_fact_reference(*stored, position)?;
            let mut lines = vec![format!("let _checked_call := {call_term}")];
            let mut arguments = Vec::new();
            let mut requirements = Vec::new();
            for (i, child) in call.child_obj_well_defined.iter().enumerate() {
                let name = format!("_case_arg_{i}");
                lines.push(format!(
                    "let {name} := {}",
                    self.compile_wd(
                        child,
                        &SourcePosition {
                            before: i,
                            ..call_scope
                        }
                    )?
                ));
                arguments.push(name);
            }
            for (i, requirement) in call.requirement_fact_verified.iter().enumerate() {
                let checked = self.compile_verify(
                    requirement,
                    &SourcePosition {
                        before: call.child_obj_well_defined.len() + i,
                        ..call_scope
                    },
                )?;
                let name = format!("_case_requirement_{i}");
                lines.push(format!("have {name} : {} := {}", checked.0, checked.1));
                requirements.push(name);
            }
            let mut args = arguments
                .iter()
                .zip(&requirements)
                .flat_map(|(a, h)| [a.clone(), h.clone()])
                .collect::<Vec<_>>();
            args.extend_from_slice(&requirements[arguments.len()..]);
            lines.push(format!(
                "have _checked_case_guard : {} := {}",
                guard.0, guard.1
            ));
            lines.push(format!(
                "have _selected_beta := {equation} {} _checked_case_guard",
                args.join(" ")
            ));
            lines.push(format!("exact _selected_beta.trans {}", residual.1));
            let equal = format!("(by\n  {})", lines.join("\n").replace('\n', "\n  "));
            Ok(if reversed {
                format!("({equal}).symm")
            } else {
                equal
            })
        };
        if let Some(wd) = wd.filter(|wd| {
            matches!(
                wd.detailed_ref(),
                DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(_),
                    ..
                }
            )
        }) {
            emit(wd, position)
        } else {
            position
                .with_visible_wd(original, &mut |wd, producer| emit(wd, producer))?
                .ok_or_else(|| LeanCompileError::unsupported("PiecewiseUnfold/WDProducer"))
        }
    }
}
