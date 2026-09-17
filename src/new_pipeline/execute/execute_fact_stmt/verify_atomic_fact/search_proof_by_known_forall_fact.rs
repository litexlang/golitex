//! Apply a stored forall's atomic then (or and-component leaf) to a goal atomic.
//!
//! Matching: shared `match_forall_conclusion_args` — bind bare forall params,
//! otherwise strict equal (forall/rewrite off). Nested param occurrences inside
//! compound objs are not matched yet.

use crate::new_pipeline::ast::fact::{AtomicFact, Fact, ForallFact};
use crate::new_pipeline::ast::fact::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity,
};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::exec_env::known_forall_conclusion_memory::{
    atomic_at_forall_location, ForallConclusionCite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    pub fn search_atomic_fact_proof_by_known_forall_fact(
        &mut self,
        goal: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        if !verify_state.can_use_forall_fact {
            return Ok(None);
        }
        let candidates = self.visible_forall_atomic_conclusion_candidates(goal);
        for cite in candidates {
            if let Some(proof) =
                self.try_apply_forall_conclusion_cite(goal, &cite, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    fn visible_forall_atomic_conclusion_candidates(
        &self,
        goal: &AtomicFact,
    ) -> Vec<ForallConclusionCite> {
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            match goal {
                AtomicFact::EqualFact(_) => {
                    out.extend(
                        env.facts
                            .known_forall_conclusions
                            .equal_conclusions
                            .iter()
                            .cloned(),
                    );
                }
                _ => {
                    let key = (goal.prop_name(), atomic_fact_has_positive_polarity(goal));
                    if let Some(entries) =
                        env.facts.known_forall_conclusions.by_atomic_prop.get(&key)
                    {
                        out.extend(entries.iter().cloned());
                    }
                }
            }
        }
        out
    }

    fn try_apply_forall_conclusion_cite(
        &mut self,
        goal: &AtomicFact,
        cite: &ForallConclusionCite,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        let forall = match self.fact_by_id_in_stack(cite.fact_id) {
            Some(Fact::ForallFact(f)) => f.clone(),
            _ => return Ok(None),
        };
        let Some(conclusion) = atomic_at_forall_location(&forall, &cite.location) else {
            return Ok(None);
        };
        // Prop name and polarity must match before trying to instantiate.
        if conclusion.prop_name() != goal.prop_name()
            || atomic_fact_has_positive_polarity(&conclusion)
                != atomic_fact_has_positive_polarity(goal)
        {
            return Ok(None);
        }

        // Step 1: list forall params in declaration order.
        let param_ids = forall.typed_parameters.ordered_param_ids();
        let conclusion_args = atomic_fact_args_ref(&conclusion);
        let goal_args = atomic_fact_args_ref(goal);

        // Step 2–3: bind params / strict-equal non-params; every param must be bound.
        // Example: conclusion `x + 1 > 1`, goal `3 + 1 > 1` with known equalities as needed.
        let Some(matched) =
            self.match_forall_conclusion_args(&conclusion_args, &goal_args, &param_ids)?
        else {
            return Ok(None);
        };

        // Step 4: instantiate forall dom facts with subst, then verify each.
        let subst = subst_from_ordered_params(&param_ids, &matched.forall_parameters_match_what_args);
        let requirement_facts = match self.build_requirement_facts(&forall, &subst)? {
            Some(facts) => facts,
            None => return Ok(None),
        };
        let mut proof_of_requirement_facts = Vec::with_capacity(requirement_facts.len());
        for req in &requirement_facts {
            let proof = self.verify_fact(req, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proof_of_requirement_facts.push(proof);
        }

        Ok(Some(SearchProofByKnownForallFact {
            cite: cite.clone(),
            forall_parameters_match_what_args: matched.forall_parameters_match_what_args,
            arg_match_proofs: matched.arg_match_proofs,
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    fn fact_by_id_in_stack(&self, fact_id: FactId) -> Option<&Fact> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(fact) = env.facts.facts_by_id.get(&fact_id) {
                return Some(fact);
            }
        }
        None
    }

    fn build_requirement_facts(
        &mut self,
        forall: &ForallFact,
        subst: &HashMap<IdentifierId, Obj>,
    ) -> RuntimeResult<Option<Vec<Fact>>> {
        // Param-type obligations deferred until type-fact store is wired.
        let mut requirements = Vec::new();
        for dom in &forall.dom_facts {
            let fact = match self.inst_fact(dom, subst) {
                Ok(fact) => fact,
                Err(_) => return Ok(None),
            };
            requirements.push(fact);
        }
        Ok(Some(requirements))
    }
}

fn subst_from_ordered_params(
    param_ids: &[IdentifierId],
    args: &[Obj],
) -> HashMap<IdentifierId, Obj> {
    let mut subst = HashMap::new();
    for (id, arg) in param_ids.iter().zip(args.iter()) {
        subst.insert(*id, arg.clone());
    }
    subst
}
