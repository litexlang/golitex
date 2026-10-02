//! Publish checked struct laws with header, instance and law binders retained.

use crate::ast::fact::{exist_shaped_fact_to_fact, ExistOrAndChainAtomicFact, Fact, ForallFact};
use crate::ast::obj::{IdentifierObj, Obj, StructAndFieldAccessObj, StructObj};
use crate::ast::param::{ParamType, TypedParameterGroup, TypedParameterList};
use crate::ast::stmt::DefStructStmt;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::{FactId, Runtime, RuntimeError, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub struct StoreStructDefinitionFactResult {
    pub source_fact_id: FactId,
    pub store_and_infer: StoreFactAndInferResult,
}

impl Runtime {
    // `struct Op<A>: ... forall x A: exist y A st {...}` publishes
    // `forall A, s &Op<A>, x A: exist y A st {...s.add...}`.
    // Existential witnesses never move outside their enclosing universal.
    pub(super) fn store_struct_definition_facts(
        &mut self,
        definition: &DefStructStmt,
    ) -> RuntimeResult<Vec<StoreStructDefinitionFactResult>> {
        let (mut parameters, domains) = match &definition.param_def_with_dom {
            Some((parameters, domains)) => (parameters.clone(), domains.clone()),
            None => (TypedParameterList { groups: Vec::new() }, Vec::new()),
        };
        let arguments = parameters.groups.iter().flat_map(|g| &g.params)
            .map(|p| Obj::Identifier(IdentifierObj::from_bound_name(p))).collect();
        let carrier = StructObj {
            name: self.atomic_name_for_plain_prop_ref(definition.name.clone()),
            params: arguments,
        };
        let instance = self.fresh_internal_param();
        let instance_obj = Obj::Identifier(IdentifierObj::from_bound_name(&instance));
        let substitution = self.struct_release_subst(&instance_obj, &carrier, definition)
            .map_err(RuntimeError::InternalBug)?;
        parameters.groups.push(TypedParameterGroup {
            params: vec![instance],
            param_type: ParamType::Obj(Obj::StructAndFieldAccessObj(
                StructAndFieldAccessObj::StructObj(carrier),
            )),
        });
        let domains: Vec<Fact> = domains.into_iter().map(quantifier_free_fact_to_fact).collect();
        let mut published = Vec::new();
        for source in &definition.equivalent_facts {
            let instantiated = self.inst_fact(source, &substitution)
                .map_err(|err| RuntimeError::InternalBug(format!("struct law substitution: {err}")))?;
            let quantified = self.quantify_struct_definition_fact(
                &parameters, &domains, instantiated,
            )?;
            let store_and_infer = self.store_fact_and_infer(&quantified)?;
            published.push(StoreStructDefinitionFactResult {
                source_fact_id: source.fact_id(),
                store_and_infer,
            });
        }
        Ok(published)
    }

    fn quantify_struct_definition_fact(
        &mut self,
        parameters: &TypedParameterList,
        domains: &[Fact],
        mut fact: Fact,
    ) -> RuntimeResult<Fact> {
        // As in template publication, retain negation by using its existing
        // counterexample representation, rather than moving binders into it.
        if let Fact::NotForall(negative) = &fact {
            let counterexample = self.not_forall_to_counterexample_exist(negative)?
                .ok_or_else(|| RuntimeError::InternalBug("struct law has no counterexample form".into()))?;
            fact = exist_shaped_fact_to_fact(&counterexample);
        }
        let mut quantified = match fact {
            Fact::ForallFact(mut universal) => {
                let mut groups = parameters.groups.clone();
                groups.extend(universal.typed_parameters.groups);
                universal.typed_parameters.groups = groups;
                let mut combined = domains.to_vec();
                combined.extend(universal.dom_facts);
                universal.dom_facts = combined;
                Fact::ForallFact(universal)
            }
            Fact::ForallFactWithIff(mut iff) => {
                let mut groups = parameters.groups.clone();
                groups.extend(iff.forall_fact.typed_parameters.groups);
                iff.forall_fact.typed_parameters.groups = groups;
                let mut combined = domains.to_vec();
                combined.extend(iff.forall_fact.dom_facts);
                iff.forall_fact.dom_facts = combined;
                Fact::ForallFactWithIff(iff)
            }
            other => {
                let then = match other {
                    Fact::AtomicFact(f) => ExistOrAndChainAtomicFact::AtomicFact(f),
                    Fact::AndFact(f) => ExistOrAndChainAtomicFact::AndFact(f),
                    Fact::ChainFact(f) => ExistOrAndChainAtomicFact::ChainFact(f),
                    Fact::OrFact(f) => ExistOrAndChainAtomicFact::OrFact(f),
                    Fact::ExistFact(f) => ExistOrAndChainAtomicFact::ExistFact(f),
                    Fact::ExistUniqueFact(f) => ExistOrAndChainAtomicFact::ExistUniqueFact(f),
                    Fact::NotExistFact(f) => ExistOrAndChainAtomicFact::NotExistFact(f),
                    Fact::ForallFact(_) | Fact::ForallFactWithIff(_) | Fact::NotForall(_) => unreachable!(),
                };
                Fact::ForallFact(ForallFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    typed_parameters: parameters.clone(),
                    dom_facts: domains.to_vec(),
                    then_facts: vec![then],
                    line_file: None,
                })
            }
        };
        let universal = match &mut quantified {
            Fact::ForallFact(f) => f,
            Fact::ForallFactWithIff(f) => &mut f.forall_fact,
            _ => unreachable!(),
        };
        // Type premises are already required by the binders. Exposing them in
        // the premise list lets existing bounded matching recover parameters
        // used only in carriers (e.g. A from s $in &Op<A>), without guessing.
        let args: Vec<Obj> = universal.typed_parameters.groups.iter().flat_map(|g| &g.params)
            .map(|p| Obj::Identifier(IdentifierObj::from_bound_name(p))).collect();
        let type_facts = self.type_facts_for_typed_arguments(&universal.typed_parameters, &args)
            .map_err(RuntimeError::InternalBug)?;
        universal.dom_facts.extend(type_facts);
        Ok(quantified)
    }
}
