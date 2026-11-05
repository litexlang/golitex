use super::compile_recursive_case_tree::{recursive_leaf_paths, recursive_path_guards, recursive_guard_atoms};
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
            (&fact.left, parent_wd.map(|w| &w.detailed_ref().left), false)
        } else if residual.right == fact.left {
            (
                &fact.right,
                parent_wd.map(|w| &w.detailed_ref().right),
                true,
            )
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
        let FnObjHead::Identifier(identifier) = application.head.as_ref() else {
            return Err(LeanCompileError::unsupported(
                "RecursiveUnfold/ApplicationHead",
            ));
        };
        let (declaration, producer, _) =
            position.visible_recursive_identifier(identifier, &self.runtime)?;
        if application.body.len() != 1 || proof.selected_case_path.is_empty() {
            return Err(LeanCompileError::unsupported("RecursiveUnfold/LeafPath"));
        }
        let path = proof
            .selected_case_path
            .iter()
            .map(|p| p.case_index)
            .collect::<Vec<_>>();
        let source_guards = recursive_path_guards(&declaration.statement.cases, &path)?;
        let leaf_index = recursive_leaf_paths(&declaration.statement.cases)
            .iter()
            .position(|p| *p == path)
            .ok_or_else(|| LeanCompileError::unsupported("RecursiveUnfold/LeafPath"))?;
        let mut cases = declaration.statement.cases.as_slice();
        let mut leaf = None;
        for index in &path {
            match &cases[*index].body {
                crate::ast::stmt::HaveFnByInducCaseBody::EqualTo(body) => leaf = Some(body),
                crate::ast::stmt::HaveFnByInducCaseBody::NestedCases(children) => cases = children,
            }
        }
        let body = leaf.ok_or_else(|| LeanCompileError::unsupported("RecursiveUnfold/LeafPath"))?;
        let parameters = declaration
            .statement
            .fn_set_clause
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect::<Vec<_>>();
        if parameters.len() != application.body[0].len() {
            return Err(LeanCompileError::unsupported(
                "RecursiveUnfold/ParameterArity",
            ));
        }
        let mut substitution = parameters
            .iter()
            .zip(&application.body[0])
            .map(|(p, a)| (p.id, a.as_ref().clone()))
            .collect::<HashMap<_, _>>();
        if substitution
            .insert(
                declaration.statement.name.id,
                Obj::Identifier(identifier.clone()),
            )
            .is_some()
        {
            return Err(LeanCompileError::unsupported(
                "RecursiveUnfold/SelfIdentity",
            ));
        }
        if !instantiated_object_matches(body, &proof.expanded_body, &substitution) {
            return Err(LeanCompileError::unsupported(
                "RecursiveUnfold/SelectedPathSubject",
            ));
        }
        let scope = SourcePosition::new(Some(position), SourceOwner::RecursiveUnfold(proof), 0);
        let mut guards = Vec::new();
        let mut atoms = Vec::new();
        for (index, (source, selected)) in source_guards
            .iter()
            .zip(&proof.selected_case_path)
            .enumerate()
        {
            let actual = source_subject(&selected.guard)?;
            if !instantiated_fact_matches(&and_chain_as_fact(source), &actual, &substitution) {
                return Err(LeanCompileError::unsupported(
                    "RecursiveUnfold/SelectedPathSubject",
                ));
            }
            let site = SourcePosition {
                before: index,
                ..scope
            };
            guards.push(self.compile_verify(&selected.guard, &site)?);
            atoms.push(recursive_guard_atoms(&actual)?);
        }
        let mut guard_declarations = Vec::new();
        let guard = if guards.len() == 1 {
            guards.remove(0)
        } else {
            let mut propositions = Vec::new();
            let mut proofs = Vec::new();
            for (index, atoms) in atoms.iter().enumerate() {
                let site = SourcePosition {
                    before: index + 1,
                    ..scope
                };
                let name = format!(
                    "h_{}",
                    source_subject(&proof.selected_case_path[index].guard)?
                        .fact_id()
                        .value()
                );
                for (i, atom) in atoms.iter().enumerate() {
                    propositions
                        .push(self.fact_proposition(&Fact::AtomicFact(atom.clone()), &site)?);
                    proofs.push(conjunction_projection(&name, i, atoms.len()));
                }
            }
            let proposition = propositions
                .into_iter()
                .rev()
                .reduce(|tail, head| format!("({head}) ∧ ({tail})"))
                .ok_or_else(|| LeanCompileError::unsupported("RecursiveUnfold/LeafPath"))?;
            for (index, (prop, term)) in guards.iter().enumerate() {
                let id = source_subject(&proof.selected_case_path[index].guard)?.fact_id();
                guard_declarations.push(format!("have h_{} : {prop} := {term}", id.value()));
            }
            (
                proposition,
                super::compile_general_recursive_result::and_intro(proofs),
            )
        };
        let guard_declarations = if guard_declarations.is_empty() {
            String::new()
        } else {
            format!(
                "{}\n  ",
                guard_declarations.join("\n").replace('\n', "\n  ")
            )
        };
        let completed = SourcePosition {
            before: proof.selected_case_path.len(),
            ..scope
        };
        let residual = self.compile_verify(&proof.residual_equal, &completed)?;
        let emit = |wd: &ObjWellDefinedProof, site: &SourcePosition<'_>| {
            ensure_object(original, wd)?;
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            } = (wd).detailed_ref()
            else {
                return Err(LeanCompileError::unsupported(
                    "RecursiveUnfold/ApplicationFormation",
                ));
            };
            let call_scope = SourcePosition::new(Some(site), SourceOwner::WD(wd), 0);
            let (checked_call, _, _) = self.compile_fn_call(application, call, &call_scope)?;
            let arity = parameters.len();
            if call.child_obj_well_defined.len() != arity
                || call.requirement_fact_verified.len()
                    != arity + declaration.statement.fn_set_clause.dom_facts.len()
            {
                return Err(LeanCompileError::unsupported(
                    "RecursiveUnfold/CallEvidenceArity",
                ));
            }
            let signature =
                super::compile_have_fn_by_induc_result::recursive_signature(declaration);
            let compact_natural = arity == 1
                && signature.dom_facts.is_empty()
                && Self::function_uses_numeric_interface(&signature)
                && *signature.set_bound_parameters.groups[0].param_type
                    == Obj::StandardSet(StandardSet::N);
            let actual = if compact_natural {
                "_checked_call.val.argument _checked_call.wd.2.1 _checked_case_guard".to_string()
            } else {
                let mut arguments = Vec::new();
                for (index, child) in call.child_obj_well_defined.iter().enumerate() {
                    ensure_object(&application.body[0][index], child)?;
                    arguments.push(self.compile_wd(
                        child,
                        &SourcePosition {
                            before: index,
                            ..call_scope
                        },
                    )?);
                }
                let requirements = call
                    .requirement_fact_verified
                    .iter()
                    .enumerate()
                    .map(|(index, requirement)| {
                        self.compile_verify(
                            requirement,
                            &SourcePosition {
                                before: arity + index,
                                ..call_scope
                            },
                        )
                        .map(|p| p.1)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let mut actual = Vec::new();
                for (argument, member) in arguments.iter().zip(&requirements) {
                    actual.extend([argument.clone(), member.clone()]);
                }
                actual.extend_from_slice(&requirements[arity..]);
                actual.push("_checked_case_guard".into());
                actual.join(" ")
            };
            let stored_id = declaration
                .store_and_infer_result
                .case_defining_fact_ids
                .get(leaf_index)
                .ok_or_else(|| {
                    LeanCompileError::new(
                        "RecursiveUnfold/CaseProducer",
                        "The selected source leaf has no stored equation producer.",
                    )
                })?;
            let case_equation =
                position.declaration_reference(&format!("h_{}", stored_id.value()), &producer)?;
            let equality = format!("(by\n  let _checked_call := {checked_call}\n  {guard_declarations}have _checked_case_guard : {} := {}\n  have _selected_beta := {case_equation} {actual}\n  exact _selected_beta.trans {})", guard.0, guard.1, residual.1);
            Ok(if reversed {
                format!("({equality}).symm")
            } else {
                equality
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
                .ok_or_else(|| {
                    LeanCompileError::new(
                        "RecursiveUnfold/WDProducer",
                        "The selected unfold has no original application WD producer.",
                    )
                })
        }
    }
}
