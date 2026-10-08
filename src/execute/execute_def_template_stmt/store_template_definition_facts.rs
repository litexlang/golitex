//! Publish successful body stores, retaining template domains and source evidence.

use super::ExecTemplateDefBodyResult;
use crate::ast::fact::{exist_shaped_fact_to_fact, ExistOrAndChainAtomicFact, Fact, ForallFact};
use crate::ast::obj::{IdentifierObj, InstantiatedTemplateObj, Obj};
use crate::ast::stmt::DefTemplateStmt;
use crate::exec_env::ExecEnv;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::{FactId, IdentifierId, Runtime, RuntimeError, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;
use std::collections::{HashMap, HashSet};

// The source lives in the retained body environment; the new forall lives in
// the enclosing statement transaction. This link preserves both identities.
pub struct StoreTemplateDefinitionFactResult {
    pub source_fact_id: FactId,
    pub store_and_infer: StoreFactAndInferResult,
}

impl StoreTemplateDefinitionFactResult {
    fn new(source_fact_id: FactId, store_and_infer: StoreFactAndInferResult) -> Self {
        Self {
            source_fact_id,
            store_and_infer,
        }
    }
}

impl Runtime {
    pub(super) fn store_template_definition_facts(
        &mut self,
        template: &DefTemplateStmt,
        body: &ExecTemplateDefBodyResult,
        local_env: &ExecEnv,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<StoreTemplateDefinitionFactResult>> {
        let (binding_id, source_ids) = definition_binding_and_fact_ids(body);
        let args = template
            .template_arg_def
            .groups
            .iter()
            .flat_map(|group| group.params.iter())
            .map(|param| Obj::Identifier(IdentifierObj::from_bound_name(param)))
            .collect();
        let surface = Obj::InstantiatedTemplateObj(InstantiatedTemplateObj {
            template_name: self.atomic_name_for_plain_prop_ref(template.template_name.clone()),
            args,
        });
        let substitution = HashMap::from([(binding_id, surface)]);
        let mut seen = HashSet::new();
        let mut published = Vec::new();
        for source_fact_id in source_ids {
            if !seen.insert(source_fact_id) {
                continue;
            }
            let source = local_env
                .facts
                .facts_by_id
                .get(&source_fact_id)
                .ok_or_else(|| {
                    RuntimeError::InternalBug(format!(
                    "template definition fact {source_fact_id} is missing from its body environment"
                ))
                })?;
            let instantiated = self.inst_fact(source, &substitution).map_err(|err| {
                RuntimeError::InternalBug(format!("template definition substitution: {err}"))
            })?;
            let quantified = self.quantify_template_definition_fact(template, instantiated)?;
            let stored = self.store_fact_and_infer(&quantified, verify_state)?;
            published.push(StoreTemplateDefinitionFactResult::new(
                source_fact_id,
                stored,
            ));
        }
        Ok(published)
    }

    fn quantify_template_definition_fact(
        &mut self,
        template: &DefTemplateStmt,
        mut fact: Fact,
    ) -> RuntimeResult<Fact> {
        // A counterexample existential is the supported then-clause form of
        // a negated forall; never move template binders inside the negation.
        if let Fact::NotForall(not_forall) = &fact {
            let counterexample = self
                .not_forall_to_counterexample_exist(not_forall)?
                .ok_or_else(|| {
                    RuntimeError::InternalBug(
                        "template definition has no counterexample form for not forall".into(),
                    )
                })?;
            fact = exist_shaped_fact_to_fact(&counterexample);
        }
        let mut typed_parameters = template.template_arg_def.clone();
        let mut dom_facts: Vec<Fact> = template
            .template_arg_dom
            .iter()
            .cloned()
            .map(quantifier_free_fact_to_fact)
            .collect();
        match fact {
            Fact::ForallFact(mut forall) => {
                typed_parameters
                    .groups
                    .extend(forall.typed_parameters.groups);
                dom_facts.extend(forall.dom_facts);
                forall.typed_parameters = typed_parameters;
                forall.dom_facts = dom_facts;
                Ok(Fact::ForallFact(forall))
            }
            Fact::ForallFactWithIff(mut iff) => {
                typed_parameters
                    .groups
                    .extend(iff.forall_fact.typed_parameters.groups);
                dom_facts.extend(iff.forall_fact.dom_facts);
                iff.forall_fact.typed_parameters = typed_parameters;
                iff.forall_fact.dom_facts = dom_facts;
                Ok(Fact::ForallFactWithIff(iff))
            }
            other => {
                let then = match other {
                    Fact::AtomicFact(fact) => ExistOrAndChainAtomicFact::AtomicFact(fact),
                    Fact::AndFact(fact) => ExistOrAndChainAtomicFact::AndFact(fact),
                    Fact::ChainFact(fact) => ExistOrAndChainAtomicFact::ChainFact(fact),
                    Fact::OrFact(fact) => ExistOrAndChainAtomicFact::OrFact(fact),
                    Fact::ExistFact(fact) => ExistOrAndChainAtomicFact::ExistFact(fact),
                    Fact::ExistUniqueFact(fact) => ExistOrAndChainAtomicFact::ExistUniqueFact(fact),
                    Fact::NotExistFact(fact) => ExistOrAndChainAtomicFact::NotExistFact(fact),
                    Fact::ForallFact(_) | Fact::ForallFactWithIff(_) | Fact::NotForall(_) => {
                        unreachable!("universal facts handled before building a then-clause")
                    }
                };
                Ok(Fact::ForallFact(ForallFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    typed_parameters,
                    dom_facts,
                    then_facts: vec![then],
                    line_file: Some(template.line_file.clone()),
                }))
            }
        }
    }
}

fn definition_binding_and_fact_ids(
    body: &ExecTemplateDefBodyResult,
) -> (IdentifierId, Vec<FactId>) {
    match body {
        ExecTemplateDefBodyResult::HaveObjInNonemptySet(result) => (
            result.statement.param_def.ordered_param_ids()[0],
            result.store_and_infer_result.stored_fact_ids.clone(),
        ),
        ExecTemplateDefBodyResult::HaveObjEqual(result) => (
            result.statement.param_def.ordered_param_ids()[0],
            result.store_and_infer_result.stored_fact_ids.clone(),
        ),
        ExecTemplateDefBodyResult::HaveObjByExistFacts(result) => (
            result.statement.param_def.ordered_param_ids()[0],
            result.store_and_infer_result.stored_fact_ids.clone(),
        ),
        ExecTemplateDefBodyResult::HaveByReplacementAxiom(result) => {
            (result.statement.name.id, result.stored_fact_ids.clone())
        }
        ExecTemplateDefBodyResult::ObtainObjFromExistFact(result) => (
            result.statement.equal_tos[0].id,
            result.store_and_infer_result.stored_fact_ids.clone(),
        ),
        ExecTemplateDefBodyResult::ObtainObjFromAtomicFact(result) => (
            result.statement.equal_tos[0].id,
            result.store_and_infer_result.stored_fact_ids.clone(),
        ),
        ExecTemplateDefBodyResult::HaveFnEqual(result) => (
            result.statement.name.id,
            result.store_and_infer_result.stored_fact_ids.clone(),
        ),
        ExecTemplateDefBodyResult::HaveFnEqualCaseByCase(result) => (
            result.statement.name.id,
            result.store_and_infer_result.stored_fact_ids.clone(),
        ),
        ExecTemplateDefBodyResult::HaveFnByForallExistUnique(result) => {
            (result.statement.name.id, result.stored_fact_ids.clone())
        }
        ExecTemplateDefBodyResult::HaveFnByInduc(result) => (
            result.statement.name.id,
            result.store_and_infer_result.stored_fact_ids.clone(),
        ),
        ExecTemplateDefBodyResult::TrustHave(result) => {
            let mut ids = result.defined_param_store_and_infer.stored_fact_ids.clone();
            for stored in &result.body_store_and_infer_results {
                ids.extend(stored.stored_fact_ids());
            }
            (result.statement.param_def.ordered_param_ids()[0], ids)
        }
    }
}
