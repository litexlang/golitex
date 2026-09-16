use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::exec_env::helper::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity,
};
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchProofByKnownAtomicFact, EqualFactSearchedProofByKnownEquality,
    WhyKnownAtomicParameterMatchesGiven,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Search known non-equality atomics in two passes:
    // 1) exact ObjIR on every arg → cite with EqualIr per parameter
    // 2) else equality-class match → cite with EqualIr or ByKnownEquality paths
    //
    // Example (pass 1): known `$in(a, S)`, goal `$in(a, S)` → EqualIr, EqualIr.
    // Example (pass 2): known `$in(a, S)`, `a = b`, goal `$in(b, S)` → path a→b, EqualIr.
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
        let goal_arg_irs: Vec<ObjIR> = goal_args.iter().map(|arg| arg.ir()).collect();

        // Pass 1: exact ObjIR match (no equality graph).
        for env in self.execution_environments_stack.iter().rev() {
            let memory = &env.facts.known_atomic_except_equality_facts;
            if let Some(knowns) = memory.by_prop.get(&lookup_key) {
                for known in knowns {
                    let known_args = atomic_fact_args_ref(known);
                    if known_args.len() != goal_args.len() {
                        continue;
                    }
                    let exact = known_args
                        .iter()
                        .zip(goal_arg_irs.iter())
                        .all(|(known_arg, goal_ir)| &known_arg.ir() == goal_ir);
                    if exact {
                        return Ok(Some(Self::known_atomic_proof_all_equal_ir(known, goal_args.len())));
                    }
                }
            }
        }

        // Pass 2: equality-class match (compute classes only if pass 1 missed).
        let class_per_arg: Vec<Vec<ObjIR>> = goal_args
            .iter()
            .map(|arg| self.known_equality_class_keys(arg))
            .collect();

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
                        return Ok(self.build_known_atomic_proof_with_equality(fact, known));
                    }
                }
            }
        }

        Ok(None)
    }

    fn known_atomic_proof_all_equal_ir(
        known: &AtomicFact,
        arg_count: usize,
    ) -> AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
        AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
            cite_fact_id: known.fact_id(),
            why_parameters_of_known_fact_are_equal_to_givens: (0..arg_count)
                .map(|_| WhyKnownAtomicParameterMatchesGiven::EqualIr)
                .collect(),
        }
    }

    fn build_known_atomic_proof_with_equality(
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
            why_parameters.push(self.why_known_atomic_arg_matches(known_arg, goal_arg)?);
        }

        Some(AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
            cite_fact_id: known.fact_id(),
            why_parameters_of_known_fact_are_equal_to_givens: why_parameters,
        })
    }

    fn why_known_atomic_arg_matches(
        &self,
        known_arg: &Obj,
        goal_arg: &Obj,
    ) -> Option<WhyKnownAtomicParameterMatchesGiven> {
        if known_arg.ir() == goal_arg.ir() {
            return Some(WhyKnownAtomicParameterMatchesGiven::EqualIr);
        }
        let path = self.known_equality_path(known_arg, goal_arg)?;
        Some(WhyKnownAtomicParameterMatchesGiven::ByKnownEquality(
            EqualFactSearchedProofByKnownEquality { path },
        ))
    }
}
