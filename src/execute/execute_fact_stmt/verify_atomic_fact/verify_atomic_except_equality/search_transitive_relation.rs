use crate::prelude::*;

/// One selected known left edge and the checked remaining edge.
pub struct TransitiveRelationProof {
    pub known_left_fact_id: FactId,
    pub residual_fact: Fact,
    pub proof_of_residual_fact: VerifyFactResult,
}

impl Runtime {
    /// P(a,b), P(b,c) imply P(a,c). The caller owns the builtin or registered
    /// law. Only the existing positive P bucket supplies possible middle terms.
    pub(crate) fn search_transitive_relation(
        &mut self,
        goal: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<TransitiveRelationProof>> {
        let arguments = atomic_fact_args_ref(goal);
        if arguments.len() != 2 || !atomic_fact_has_positive_polarity(goal) {
            return Ok(None);
        }
        let mut candidates = Vec::new();
        let key = (goal.prop_name(), true);
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            {
                for known in knowns {
                    let known_arguments = atomic_fact_args_ref(known);
                    if known_arguments.len() == 2 && known_arguments[0].ir() == arguments[0].ir() {
                        candidates.push(known.clone());
                    }
                }
            }
        }
        for known in &candidates {
            let known_arguments = atomic_fact_args_ref(known);
            if known.prop_name() != goal.prop_name()
                || known_arguments.len() != 2
                || known_arguments[0].ir() != arguments[0].ir()
                || !atomic_fact_has_positive_polarity(known)
            {
                continue;
            }
            let Some(residual) = super::helper::atomic_fact_with_args(
                goal,
                vec![known_arguments[1].clone(), arguments[1].clone()],
                self.global_ids.allocate_fact_id(),
            ) else {
                continue;
            };
            let proof_of_residual_fact =
                self.verify_atomic_fact(&residual, state.without_rewrite())?;
            if proof_of_residual_fact.is_failed() {
                continue;
            }
            return Ok(Some(TransitiveRelationProof::new(
                known.fact_id(),
                residual.into(),
                proof_of_residual_fact,
            )));
        }
        Ok(None)
    }
}

impl TransitiveRelationProof {
    pub fn new(
        known_left_fact_id: FactId,
        residual_fact: Fact,
        proof_of_residual_fact: VerifyFactResult,
    ) -> Self {
        Self {
            known_left_fact_id,
            residual_fact,
            proof_of_residual_fact,
        }
    }
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/registered_transitivity/tests.rs"]
mod tests;
