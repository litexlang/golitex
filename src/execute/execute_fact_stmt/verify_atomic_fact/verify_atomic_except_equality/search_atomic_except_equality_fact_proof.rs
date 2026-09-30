use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Cheap phase: builtin rule → known atomic.
    // Deep phase (can_use_def_and_known_forall_and_known_strategy, round > 0):
    //   with_one_less_round() once, then
    //   verify_by_strategy → by definition → known forall →
    //   (can_use_rewrite) builtin rewrite → known rewrite.
    //
    // Entering builtin / deep each requires round > 0 and passes round - 1.
    // Premise-producing arms also self-gate on the decremented round; cite-only
    // still runs at round 0 inside that call. Strategy cite-only bypasses this
    // entry and calls by_builtin_rule directly.
    // Ok(None) means no proof found; that is not a runtime error.
    pub fn search_atomic_except_equality_fact_proof(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        if let Some(result) = self.search_atomic_except_equality_fact_proof_by_known_atomic_fact(
            fact,
            verify_state.clone(),
        )? {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(result),
            ));
        }

        if verify_state.can_use_builtin_rule_round > 0 {
            if let Some(result) = self.search_atomic_except_equality_fact_proof_by_builtin_rule(
                fact,
                verify_state.with_one_less_round(),
            )? {
                return Ok(Some(AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                    result,
                )));
            }
        }

        if !verify_state.can_use_def_and_known_forall_and_known_strategy {
            return Ok(None);
        }

        let deep_state = verify_state.with_one_less_round();

        if let Some(result) = self.verify_by_strategy_atomic_except_equality(fact)? {
            return Ok(Some(result));
        }

        if let Some(result) =
            self.search_atomic_except_equality_fact_proof_by_definition(fact, deep_state.clone())?
        {
            return Ok(Some(AtomicExceptEqualityFactSearchedProof::ByDefinition(
                result,
            )));
        }

        if let Some(result) = self.search_atomic_except_equality_fact_proof_by_known_forall_fact(
            fact,
            deep_state.clone(),
        )? {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(result),
            ));
        }

        if deep_state.can_use_rewrite {
            if let Some(result) = self.search_atomic_except_equality_fact_proof_by_builtin_rewrite(
                fact,
                deep_state.clone(),
            )? {
                return Ok(Some(
                    AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(result),
                ));
            }

            if let Some(result) =
                self.search_atomic_except_equality_fact_proof_by_known_rewrite(fact, deep_state)?
            {
                return Ok(Some(AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(
                    result,
                )));
            }
        }

        Ok(None)
    }
}
