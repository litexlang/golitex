use super::helper::*;
use super::compile_recursive_case_tree::{recursive_leaf_paths, recursive_path_guards, recursive_guard_atoms};
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::ast::stmt::TemplateDefEnum;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_template::result::EqualitySearchProofByTemplateObjectDefinition;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjDomainFnSetEvidence;
use crate::execute::{ExecHaveFnEqualCaseByCaseStmtResult, ExecHaveFnByInducStmtResult};
use crate::prelude::*;
use std::collections::HashMap;

impl LitexToLeanCompiler {
    pub(super) fn compile_template_case_unfold(
        &self,
        fact: &EqualFact,
        proof: &EqualitySearchProofByTemplateObjectDefinition,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (expanded_body, residual_equal, guard_proofs, path) = match proof {
            EqualitySearchProofByTemplateObjectDefinition::HaveFnEqualCaseByCaseApplication(p) => (
                &p.expanded_body,
                &p.residual_equal,
                vec![&p.guard],
                vec![p.matched_case_index],
            ),
            EqualitySearchProofByTemplateObjectDefinition::HaveFnByInducApplication(p) => (
                &p.expanded_body,
                &p.residual_equal,
                p.selected_case_path
                    .iter()
                    .map(|case| &case.guard)
                    .collect(),
                p.selected_case_path
                    .iter()
                    .map(|case| case.case_index)
                    .collect(),
            ),
            _ => return Err(LeanCompileError::unsupported("TemplateCases/SelectedRoute")),
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(residual)) = source_subject(residual_equal)?
        else {
            return Err(LeanCompileError::unsupported("TemplateCases/Residual"));
        };
        if residual.left != *expanded_body {
            return Err(LeanCompileError::unsupported("TemplateCases/ExpandedBody"));
        }
        let (object, reversed) = if residual.right == fact.right {
            (&fact.left, false)
        } else if residual.right == fact.left {
            (&fact.right, true)
        } else {
            return Err(LeanCompileError::unsupported("TemplateCases/Endpoint"));
        };
        let Obj::FnObj(call) = object else {
            return Err(LeanCompileError::unsupported("TemplateCases/Application"));
        };
        let FnObjHead::InstantiatedTemplateObj(instance) = call.head.as_ref() else {
            return Err(LeanCompileError::unsupported("TemplateCases/Head"));
        };
        let (declaration, producer, _) =
            position.visible_template(&instance.template_name, &self.runtime)?;
        super::compile_template_stmt_result::template_binding(declaration)?;
        let (parameters, expected_guards, expected_body, source_ids, recursive_name, index) = match (
            proof,
            &declaration.statement.template_def_stmt,
            declaration.body.as_ref(),
        ) {
            (
                EqualitySearchProofByTemplateObjectDefinition::HaveFnEqualCaseByCaseApplication(_),
                TemplateDefEnum::HaveFnEqualCaseByCaseStmt(source),
                ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqualCaseByCase(
                    ExecHaveFnEqualCaseByCaseStmtResult::Success(body),
                )),
            ) => (
                &source.fn_set_clause.set_bound_parameters,
                vec![source
                    .cases
                    .get(path[0])
                    .ok_or_else(|| LeanCompileError::unsupported("TemplateCases/CaseIndex"))?],
                source
                    .equal_tos
                    .get(path[0])
                    .ok_or_else(|| LeanCompileError::unsupported("TemplateCases/CaseBody"))?,
                &body.store_and_infer_result.case_defining_fact_ids,
                None,
                path[0],
            ),
            (
                EqualitySearchProofByTemplateObjectDefinition::HaveFnByInducApplication(_),
                TemplateDefEnum::HaveFnByInducStmt(source),
                ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnByInduc(
                    ExecHaveFnByInducStmtResult::Success(body),
                )),
            ) => {
                let guards = recursive_path_guards(&source.cases, &path)?;
                let index = recursive_leaf_paths(&source.cases)
                    .iter()
                    .position(|p| *p == path)
                    .ok_or_else(|| {
                        LeanCompileError::unsupported("TemplateCases/RecursiveLeafPath")
                    })?;
                let mut cases = source.cases.as_slice();
                let mut value = None;
                for index in &path {
                    match &cases[*index].body {
                        crate::ast::stmt::HaveFnByInducCaseBody::EqualTo(body) => {
                            value = Some(body)
                        }
                        crate::ast::stmt::HaveFnByInducCaseBody::NestedCases(children) => {
                            cases = children
                        }
                    }
                }
                (
                    &source.fn_set_clause.set_bound_parameters,
                    guards,
                    value.ok_or_else(|| {
                        LeanCompileError::unsupported("TemplateCases/RecursiveLeafPath")
                    })?,
                    &body.store_and_infer_result.case_defining_fact_ids,
                    Some(source.name.id),
                    index,
                )
            }
            _ => return Err(LeanCompileError::unsupported("TemplateCases/Declaration")),
        };
        let params = parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .collect::<Vec<_>>();
        let header = declaration.statement.template_arg_def.ordered_param_ids();
        if header.len() != instance.args.len()
            || call.body.len() != 1
            || call.body[0].len() != params.len()
        {
            return Err(LeanCompileError::unsupported("TemplateCases/Arity"));
        }
        let mut substitution: HashMap<_, _> = header
            .into_iter()
            .zip(instance.args.iter().cloned())
            .collect();
        for (parameter, value) in params.iter().zip(&call.body[0]) {
            if substitution
                .insert(parameter.id, value.as_ref().clone())
                .is_some()
            {
                return Err(LeanCompileError::unsupported(
                    "TemplateCases/BinderIdentity",
                ));
            }
        }
        if let Some(id) = recursive_name {
            if substitution
                .insert(id, Obj::InstantiatedTemplateObj(instance.clone()))
                .is_some()
            {
                return Err(LeanCompileError::unsupported(
                    "TemplateCases/RecursiveBinderIdentity",
                ));
            }
        }
        if expected_guards.len() != guard_proofs.len()
            || !instantiated_object_matches(expected_body, expanded_body, &substitution)
        {
            return Err(LeanCompileError::unsupported(
                "TemplateCases/SelectedSubject",
            ));
        }
        for (expected, actual) in expected_guards.iter().zip(&guard_proofs) {
            if !instantiated_fact_matches(
                &and_chain_as_fact(expected),
                &source_subject(actual)?,
                &substitution,
            ) {
                return Err(LeanCompileError::unsupported(
                    "TemplateCases/SelectedSubject",
                ));
            }
        }
        let source_id = source_ids
            .get(index)
            .ok_or_else(|| LeanCompileError::unsupported("TemplateCases/EquationSource"))?;
        let published = declaration
            .definition_facts
            .iter()
            .find(|p| &p.source_fact_id == source_id)
            .ok_or_else(|| LeanCompileError::unsupported("TemplateCases/EquationPublication"))?;
        let equation = position.declaration_reference(
            &format!("h_{}", published.store_and_infer.primary_fact_id().value()),
            &producer,
        )?;
        let mut guards = Vec::new();
        let mut declarations = Vec::new();
        let mut propositions = Vec::new();
        let mut terms = Vec::new();
        for original in &guard_proofs {
            let prior = position.search_verify_prior(original)?;
            let guard = self.compile_verify(original, &prior)?;
            if guard_proofs.len() > 1 {
                let actual = source_subject(original)?;
                let name = format!("h_{}", actual.fact_id().value());
                declarations.push(format!("have {name} : {} := {}", guard.0, guard.1));
                let atoms = recursive_guard_atoms(&actual)?;
                let after = SourcePosition {
                    before: prior.before + 1,
                    ..prior
                };
                for (i, atom) in atoms.iter().enumerate() {
                    propositions
                        .push(self.fact_proposition(&Fact::AtomicFact(atom.clone()), &after)?);
                    terms.push(conjunction_projection(&name, i, atoms.len()));
                }
            }
            guards.push(guard);
        }
        let guard = if guards.len() == 1 {
            guards.remove(0)
        } else {
            (
                propositions
                    .into_iter()
                    .rev()
                    .reduce(|tail, head| format!("({head}) ∧ ({tail})"))
                    .ok_or_else(|| {
                        LeanCompileError::unsupported("TemplateCases/RecursiveLeafPath")
                    })?,
                super::compile_general_recursive_result::and_intro(terms),
            )
        };
        let declarations = if declarations.is_empty() {
            String::new()
        } else {
            format!("{}\n  ", declarations.join("\n").replace('\n', "\n  "))
        };
        let residual = self.compile_verify(
            residual_equal,
            &position.search_verify_prior(residual_equal)?,
        )?;
        position.with_visible_wd(object, &mut |wd, producer| {
            ensure_object(object, wd)?;
            let DetailedObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::FnObj(evidence), .. } = wd.detailed_ref() else {
                return Err(LeanCompileError::unsupported("TemplateCases/CallWD"));
            };
            let Some(FnObjDomainFnSetEvidence::TemplateDefinition { fn_set, .. }) = &evidence.domain_fn_set else {
                return Err(LeanCompileError::unsupported("TemplateCases/SelectedSignature"));
            };
            self.validate_template_function(instance, fn_set, None, position)?;
            let template_wd = evidence.child_obj_well_defined.first().ok_or_else(|| LeanCompileError::unsupported("TemplateCases/InstanceWD"))?;
            ensure_object(&Obj::InstantiatedTemplateObj(instance.clone()), template_wd)?;
            let DetailedObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::InstantiatedTemplateObj(template_evidence), .. } = template_wd.detailed_ref() else {
                return Err(LeanCompileError::unsupported("TemplateCases/InstanceWD"));
            };
            let scope = SourcePosition::new(Some(producer), SourceOwner::WD(wd), 0);
            let instance_scope = SourcePosition::new(Some(&scope), SourceOwner::WD(template_wd), 0);
            let mut arguments = self.compile_template_arguments(instance, template_evidence, &instance_scope)?;
            let template_guards = arguments.split_off(2 * instance.args.len());
            let checked_call = self.compile_fn_first_call_with_member(call, evidence, &scope)?.0;
            let mut values = Vec::new();
            for (index, child) in evidence.child_obj_well_defined.iter().enumerate().skip(1) {
                values.push(self.compile_wd(child, &SourcePosition { before: index, ..scope })?);
            }
            let mut requirements = Vec::new();
            for (index, child) in evidence.requirement_fact_verified.iter().enumerate() {
                requirements.push(self.compile_verify(child, &SourcePosition {
                    before: evidence.child_obj_well_defined.len() + index, ..scope })?.1);
            }
            if values.len() != params.len() || requirements.len() < values.len() {
                return Err(LeanCompileError::unsupported("TemplateCases/ArgumentStages"));
            }
            arguments.extend(values.iter().zip(&requirements).flat_map(|(v,h)| [v.clone(),h.clone()]));
            arguments.extend(template_guards);
            arguments.extend_from_slice(&requirements[values.len()..]);
            let term = format!("(by\n  {declarations}let _template_checked_call := {checked_call}\n  have _template_case : {} := {}\n  have _template_beta := {equation} {} _template_case\n  exact _template_beta.trans {}\n)", guard.0, guard.1, arguments.join(" "), residual.1);
            Ok(if reversed { format!("({term}).symm") } else { term })
        })?.ok_or_else(|| LeanCompileError::unsupported("TemplateCases/CallWD"))
    }
}
