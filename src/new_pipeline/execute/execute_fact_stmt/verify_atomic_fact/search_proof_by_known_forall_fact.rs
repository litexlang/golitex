//! Apply a stored forall's atomic then (or and-component leaf) to a goal atomic.
//!
//! Matching: each conclusion arg is either a forall param identifier (bind to
//! the goal arg) or a closed term matching by `ir()`. Nested param occurrences
//! inside compound objs are not matched yet.

use crate::new_pipeline::ast::fact::{AtomicFact, Fact, ForallFact};
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj};
use crate::new_pipeline::ast::param::TypedParameterList;
use crate::new_pipeline::ast::fact::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity,
};
use crate::new_pipeline::exec_env::known_forall_conclusion_memory::{
    atomic_at_forall_location, ForallConclusionCite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};
use std::collections::{HashMap, HashSet};

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
        if conclusion.prop_name() != goal.prop_name()
            || atomic_fact_has_positive_polarity(&conclusion)
                != atomic_fact_has_positive_polarity(goal)
        {
            return Ok(None);
        }

        let param_ids = ordered_param_ids(&forall.typed_parameters);
        let param_set: HashSet<IdentifierId> = param_ids.iter().copied().collect();
        let conclusion_args = atomic_fact_args_ref(&conclusion);
        let goal_args = atomic_fact_args_ref(goal);
        if conclusion_args.len() != goal_args.len() {
            return Ok(None);
        }

        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        for (pattern_arg, goal_arg) in conclusion_args.iter().zip(goal_args.iter()) {
            if !unify_obj_phase1(pattern_arg, goal_arg, &param_set, &mut subst) {
                return Ok(None);
            }
        }
        for id in &param_ids {
            if !subst.contains_key(id) {
                return Ok(None);
            }
        }

        let forall_parameters_match_what_args: Vec<Obj> = param_ids
            .iter()
            .map(|id| subst.get(id).expect("checked").clone())
            .collect();

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
            forall_parameters_match_what_args,
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

fn ordered_param_ids(params: &TypedParameterList) -> Vec<IdentifierId> {
    let mut ids = Vec::new();
    for group in &params.groups {
        for param in &group.params {
            ids.push(param.id);
        }
    }
    ids
}

fn unify_obj_phase1(
    pattern: &Obj,
    goal: &Obj,
    param_ids: &HashSet<IdentifierId>,
    subst: &mut HashMap<IdentifierId, Obj>,
) -> bool {
    if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = pattern {
        if param_ids.contains(id) {
            if let Some(existing) = subst.get(id) {
                return existing.ir() == goal.ir();
            }
            subst.insert(*id, goal.clone());
            return true;
        }
    }
    pattern.ir() == goal.ir()
}

