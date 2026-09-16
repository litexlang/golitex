use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::exec_env::helper::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity,
};
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, EqualFactSearchedProofByKnownEquality,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Search: cite a stored same-shape atomic whose args are equality-class matches.
    // Example: known `$in(a, S)` and `a = b` prove `$in(b, S)` with cite + path a→b.
    pub fn search_atomic_except_equality_fact_proof_by_known_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownAtomicFact>> {
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Ok(None);
        }

        let lookup_key = (
            fact.prop_name(),
            atomic_fact_has_positive_polarity(fact),
        );
        let goal_args = atomic_fact_args_ref(fact);
        let class_per_arg: Vec<Vec<ObjIR>> = goal_args
            .iter()
            .map(|arg| self.known_equality_class_keys(arg))
            .collect();

        for env in self.execution_environments_stack.iter().rev() {
            let memory = &env.facts.known_atomic_except_equality_facts;
            let hit = memory.by_prop.get(&lookup_key).and_then(|knowns| {
                knowns
                    .iter()
                    .find(|known| {
                        let known_args = atomic_fact_args_ref(known);
                        known_args.len() == goal_args.len()
                            && known_args
                                .iter()
                                .zip(class_per_arg.iter())
                                .all(|(known_arg, class)| class.contains(&known_arg.ir()))
                    })
                    .cloned()
            });

            if let Some(known) = hit {
                return Ok(self.build_known_atomic_proof(fact, &known));
            }
        }

        Ok(None)
    }

    fn build_known_atomic_proof(
        &self,
        goal: &AtomicFact,
        known: &AtomicFact,
    ) -> Option<AtomicExceptEqualityFactSearchProofByKnownAtomicFact> {
        let goal_args = atomic_fact_args_ref(goal);
        let known_args = atomic_fact_args_ref(known);
        if goal_args.len() != known_args.len() {
            return None;
        }

        let mut why_parameters = Vec::new();
        for (known_arg, goal_arg) in known_args.iter().zip(goal_args.iter()) {
            let path = self.known_equality_path(known_arg, goal_arg)?;
            why_parameters.push(EqualFactSearchedProofByKnownEquality { path });
        }

        Some(AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
            cite_fact_id: known.fact_id(),
            why_parameters_of_known_fact_are_equal_to_givens: why_parameters,
        })
    }
}
