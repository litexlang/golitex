//! Prove that forall instantiation args satisfy param types and dom facts.
//!
//! Called after `match_forall_conclusion_args`. Stage order:
//! 1. for each param: build type fact for the instantiated arg, verify it
//! 2. instantiate each dom fact under subst, verify it
//!
//! Example: `forall x R: x > 0 => x + 1 > 1` with subst `{x: 3}`
//! requires `3 $in R`, then `3 > 0`.

use crate::ast::fact::{
    AtomicFact, Fact, ForallFact, InFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact,
};
use crate::ast::obj::Obj;
use crate::ast::param::{ParamType, TypedParameterList};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    ForallParamTypeRequirementProof, ProveForallInstantiationRequirementsProof,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    // Build the concrete type obligations before any caller assumes the
    // instantiated theorem, predicate, or existential body. A complete
    // substitution is needed when later carrier types mention earlier args.
    pub(crate) fn type_facts_for_typed_arguments(
        &mut self,
        parameters: &TypedParameterList,
        args: &[Obj],
    ) -> Result<Vec<Fact>, String> {
        let ids = parameters.ordered_param_ids();
        if ids.len() != args.len() {
            return Err(format!(
                "expected {} typed argument(s), got {}",
                ids.len(),
                args.len()
            ));
        }
        let subst: HashMap<IdentifierId, Obj> = ids.into_iter().zip(args.iter().cloned()).collect();
        let mut obligations = Vec::with_capacity(args.len());
        for group in &parameters.groups {
            let param_type = self
                .inst_param_type(&group.param_type, &subst)
                .map_err(|error| error.to_string())?;
            for param in &group.params {
                let arg = subst.get(&param.id).expect("typed argument arity checked");
                obligations.push(type_fact_for_instantiated_arg(
                    arg.clone(),
                    &param_type,
                    self.global_ids.allocate_fact_id(),
                ));
            }
        }
        Ok(obligations)
    }

    // Prove param-type obligations then dom obligations for a forall instantiation.
    // Soft miss: Ok(None). Operational failure: Err(...).
    pub(crate) fn prove_forall_instantiation_requirements(
        &mut self,
        forall: &ForallFact,
        subst: &HashMap<IdentifierId, Obj>,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ProveForallInstantiationRequirementsProof>> {
        let mut param_type_requirements = Vec::new();
        for group in &forall.typed_parameters.groups {
            let param_type = match self.inst_param_type(&group.param_type, subst) {
                Ok(param_type) => param_type,
                Err(_) => return Ok(None),
            };
            for param in &group.params {
                let Some(arg) = subst.get(&param.id) else {
                    return Ok(None);
                };
                let type_fact = type_fact_for_instantiated_arg(
                    arg.clone(),
                    &param_type,
                    self.global_ids.allocate_fact_id(),
                );
                let proof = self.verify_fact(&type_fact, verify_state.clone())?;
                if proof.is_failed() {
                    return Ok(None);
                }
                param_type_requirements.push(ForallParamTypeRequirementProof {
                    param_id: param.id,
                    arg: arg.clone(),
                    type_fact,
                    proof,
                });
            }
        }

        let mut dom_facts = Vec::new();
        for dom in &forall.dom_facts {
            let fact = match self.inst_fact(dom, subst) {
                Ok(fact) => fact,
                Err(_) => return Ok(None),
            };
            dom_facts.push(fact);
        }
        let mut proof_of_dom_facts = Vec::with_capacity(dom_facts.len());
        for fact in &dom_facts {
            let proof = self.verify_fact(fact, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proof_of_dom_facts.push(proof);
        }

        Ok(Some(ProveForallInstantiationRequirementsProof {
            param_type_requirements,
            dom_facts,
            proof_of_dom_facts,
        }))
    }
}

// Same shapes as `define_typed_parameters_in_current_env`, but for an already
// chosen instantiation arg instead of a fresh binder.
fn type_fact_for_instantiated_arg(
    arg: Obj,
    param_type: &ParamType,
    fact_id: crate::runtime::FactId,
) -> Fact {
    match param_type {
        ParamType::Obj(param_set) => Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id,
            element: arg,
            set: param_set.clone(),
            line_file: None,
        })),
        ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
            fact_id,
            set: arg,
            line_file: None,
        })),
        ParamType::NonemptySet(_) => {
            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                fact_id,
                set: arg,
                line_file: None,
            }))
        }
        ParamType::FiniteSet(_) => Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id,
            set: arg,
            line_file: None,
        })),
    }
}
