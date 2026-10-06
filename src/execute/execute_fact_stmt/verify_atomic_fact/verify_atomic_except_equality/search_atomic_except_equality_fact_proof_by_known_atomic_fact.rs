use crate::ast::fact::{atomic_fact_args_ref, atomic_fact_has_positive_polarity};
use crate::ast::fact::{AtomicFact, EqualFact};
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, EqualFactSearchedProof,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Cite a known non-equality atomic by proving each known_arg = goal_arg.
    //
    // Candidates: same prop name, polarity, and arity (no equality-class filter).
    // Argument obligations use KnownFact: pairwise identity/alpha and exact stored paths.
    // Nested MatchingOneArgByOne is still available there (scheduled before rewrite).
    //
    // Example: known `a > 0`, `a = b`, goal `b > 0`.
    // Example: known `a + 1 > 0`, `a = b`, goal `b + 1 > 0` (peel Add, then a = b).
    pub fn search_atomic_except_equality_fact_proof_by_known_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownAtomicFact>> {
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Ok(None);
        }

        // Arg equality: known / peel only (no nested builtin / deep search).
        let equality_state = verify_state.capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::Direct);

        let lookup_key = (fact.prop_name(), atomic_fact_has_positive_polarity(fact));
        let goal_args = atomic_fact_args_ref(fact);

        // Clone candidates first so nested equality search can borrow &mut self.
        let mut candidates: Vec<AtomicFact> = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            let memory = &env.facts.known_atomic_except_equality_facts;
            if let Some(knowns) = memory.by_prop.get(&lookup_key) {
                for known in knowns {
                    if atomic_fact_args_ref(known).len() != goal_args.len() {
                        continue;
                    }
                    candidates.push(known.clone());
                }
            }
        }

        for known in candidates {
            if let Some(proof) =
                self.build_known_atomic_proof_with_equality(fact, &known, &equality_state)?
            {
                return Ok(Some(proof));
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
