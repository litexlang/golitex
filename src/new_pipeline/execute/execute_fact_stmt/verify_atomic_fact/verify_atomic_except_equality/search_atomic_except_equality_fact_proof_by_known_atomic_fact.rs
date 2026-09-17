use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::fact::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity,
};
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, EqualFactSearchedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // One pass: filter known non-equality atomics by equality-class (ObjIR),
    // then prove known_arg = goal_arg for each parameter via equality search.
    //
    // Nested equality: can_use_forall_fact = false, can_use_rewrite = false.
    // Same ObjIR usually proves by EqualIr builtin; class peers by known-equality.
    //
    // Example: known `a > 0`, goal `a > 0` → EqualIr, EqualIr.
    // Example: known `a > 0`, `a = b`, goal `b > 0` → known-equality path, EqualIr.
    pub fn search_atomic_except_equality_fact_proof_by_known_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownAtomicFact>> {
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Ok(None);
        }

        // Arg equality must not invent proofs via forall / rewrite.
        let equality_state = VerifyState {
            can_use_forall_fact: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };
        let _ = verify_state;

        let lookup_key = (
            fact.prop_name(),
            atomic_fact_has_positive_polarity(fact),
        );
        let goal_args = atomic_fact_args_ref(fact);
        let class_per_arg: Vec<Vec<ObjIR>> = goal_args
            .iter()
            .map(|arg| self.known_equality_class_keys(arg))
            .collect();

        // Clone candidates first so nested equality search can borrow &mut self.
        let mut candidates: Vec<AtomicFact> = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            let memory = &env.facts.known_atomic_except_equality_facts;
            if let Some(knowns) = memory.by_prop.get(&lookup_key) {
                for known in knowns {
                    let known_args = atomic_fact_args_ref(known);
                    if known_args.len() != goal_args.len() {
                        continue;
                    }
                    let in_class = known_args
                        .iter()
                        .zip(class_per_arg.iter())
                        .all(|(known_arg, class)| class.contains(&known_arg.ir()));
                    if in_class {
                        candidates.push(known.clone());
                    }
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
            fact_id: self.ids.allocate_fact_id(),
            left: known_arg.clone(),
            right: goal_arg.clone(),
            line_file: None,
        };
        self.search_equal_fact_proof(&equal_fact, equality_state)
    }
}
