use crate::ast::fact::{atomic_fact_args_ref, atomic_fact_has_positive_polarity};
use crate::ast::fact::{AtomicFact, EqualFact};
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, EqualFactSearchedProof,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Try the original argument tuple first, then stored equivalent objects
    // from each visible scope. Direct matching retains closed calculation.
    pub fn search_atomic_except_equality_fact_proof_by_known_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownAtomicFact>> {
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Ok(None);
        }

        // Arg equality: known / peel only (no nested builtin / deep search).
        let equality_state =
            verify_state.capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::Direct);

        let lookup_key = (fact.prop_name(), atomic_fact_has_positive_polarity(fact));
        let goal_args = atomic_fact_args_ref(fact);

        let mut equivalents =
            super::super::verify_equality::equivalence_class_graph::EquivalentArguments::new(
                &goal_args,
                self.execution_environments_stack.len(),
            );
        let mut attempted = std::collections::HashSet::new();
        loop {
            let mut candidate = None;
            for env in self.execution_environments_stack.iter().rev() {
                let memory = &env.facts.known_atomic_except_equality_facts;
                let matched = memory.by_prop.get(&lookup_key).into_iter().chain(
                    memory
                        .by_prop
                        .iter()
                        .filter_map(|((predicate, polarity), knowns)| {
                            (*polarity == lookup_key.1
                                && predicate != &lookup_key.0
                                && self
                                    .predicates_share_visible_definition(predicate, &lookup_key.0))
                            .then_some(knowns)
                        }),
                );
                for knowns in matched {
                    if let Some(known) = knowns.iter().find(|known| {
                        !attempted.contains(&known.fact_id())
                            && equivalents.matches(&atomic_fact_args_ref(known))
                    }) {
                        candidate = Some(known.clone());
                        break;
                    }
                }
                if candidate.is_some() {
                    break;
                }
            }
            if let Some(known) = candidate {
                attempted.insert(known.fact_id());
                if let Some(proof) =
                    self.build_known_atomic_proof_with_equality(fact, &known, &equality_state)?
                {
                    return Ok(Some(proof));
                }
                continue;
            }
            if !equivalents.advance(self) {
                break;
            }
        }
        // Direct equality also admits closed calculation. Preserve that
        // residual matching coverage after original and stored-path matches.
        for env_index in (0..self.execution_environments_stack.len()).rev() {
            let memory = &self.execution_environments_stack[env_index]
                .facts
                .known_atomic_except_equality_facts;
            let mut keys = vec![lookup_key.clone()];
            keys.extend(
                memory
                    .by_prop
                    .keys()
                    .filter(|(predicate, polarity)| {
                        *polarity == lookup_key.1
                            && predicate != &lookup_key.0
                            && self.predicates_share_visible_definition(predicate, &lookup_key.0)
                    })
                    .cloned(),
            );
            for key in keys {
                let count = self.execution_environments_stack[env_index]
                    .facts
                    .known_atomic_except_equality_facts
                    .by_prop
                    .get(&key)
                    .map_or(0, Vec::len);
                for index in 0..count {
                    let known = &self.execution_environments_stack[env_index]
                        .facts
                        .known_atomic_except_equality_facts
                        .by_prop[&key][index];
                    if attempted.contains(&known.fact_id())
                        || atomic_fact_args_ref(known).len() != goal_args.len()
                    {
                        continue;
                    }
                    let args = atomic_fact_args_ref(known);
                    if !args.iter().zip(&goal_args).any(|(left, right)| {
                        !super::super::verify_equality::equivalence_class_graph::objects_match_directly(left, right)
                            && crate::prelude::calculate_value_pair(left, right).is_some_and(|(_, equal)| equal)
                    }) {
                        continue;
                    }
                    let known = known.clone();
                    if let Some(proof) =
                        self.build_known_atomic_proof_with_equality(fact, &known, &equality_state)?
                    {
                        return Ok(Some(proof));
                    }
                }
            }
        }

        Ok(None)
    }

    fn build_known_atomic_proof_with_equality(
        &mut self,
        goal: &AtomicFact,
        known: &AtomicFact,
        equality_state: &VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownAtomicFact>> {
        let goal_args = atomic_fact_args_ref(goal);
        let known_args = atomic_fact_args_ref(known);
        if goal_args.len() != known_args.len() {
            return Ok(None);
        }

        let mut why_parameters = Vec::new();
        for (known_arg, goal_arg) in known_args.iter().zip(goal_args.iter()) {
            let Some(why) = self.prove_known_atomic_arg_equal_to_given(
                known_arg,
                goal_arg,
                equality_state.clone(),
            )?
            else {
                return Ok(None);
            };
            why_parameters.push(why);
        }

        Ok(Some(AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
            cite_fact_id: known.fact_id(),
            why_parameters_of_known_fact_are_equal_to_givens: why_parameters,
        }))
    }

    // Prove known_arg = goal_arg with the restricted equality search pipeline.
    fn prove_known_atomic_arg_equal_to_given(
        &mut self,
        known_arg: &Obj,
        goal_arg: &Obj,
        equality_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        let equal_fact = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: known_arg.clone(),
            right: goal_arg.clone(),
            line_file: None,
        };
        self.search_equal_fact_proof(&equal_fact, equality_state)
    }
}
