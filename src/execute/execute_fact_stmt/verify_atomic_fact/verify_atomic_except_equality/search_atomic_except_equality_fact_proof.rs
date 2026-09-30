use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Cheap phase: builtin rule (one shot) → known atomic.
    // Deep phase (can_use_def_and_known_forall_and_known_strategy):
    //   verify_by_strategy (builtin + known strategy, StrategySearch depth) →
    //   by definition → known forall →
    //   (can_use_rewrite) builtin rewrite → known rewrite.
    //
    // Builtin-rule premises inherit after_builtin_rule() (known / direct only).
    // Ok(None) means no proof found; that is not a runtime error.
    pub fn search_atomic_except_equality_fact_proof(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        // Builtin rules always run: cite-only / closed-numeric arms ignore the
        // budget; premise-producing arms self-gate on can_use_builtin_rule.
        if let Some(result) = self
            .search_atomic_except_equality_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(Some(AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                result,
            )));
        }

        if let Some(result) = self.search_atomic_except_equality_fact_proof_by_known_atomic_fact(
            fact,
            verify_state.clone(),
        )? {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(result),
            ));
        }

        if !verify_state.can_use_def_and_known_forall_and_known_strategy {
            return Ok(None);
        }

        if let Some(result) = self.verify_by_strategy_atomic_except_equality(fact)? {
            return Ok(Some(result));
        }

        if let Some(result) =
            self.search_atomic_except_equality_fact_proof_by_definition(fact, verify_state.clone())?
        {
            return Ok(Some(AtomicExceptEqualityFactSearchedProof::ByDefinition(
                result,
            )));
        }

        if let Some(result) = self.search_atomic_except_equality_fact_proof_by_known_forall_fact(
            fact,
            verify_state.clone(),
        )? {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(result),
            ));
        }

        if verify_state.can_use_rewrite {
            if let Some(result) = self.search_atomic_except_equality_fact_proof_by_builtin_rewrite(
                fact,
                verify_state.clone(),
            )? {
                return Ok(Some(
                    AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(result),
                ));
            }

            if let Some(result) =
                self.search_atomic_except_equality_fact_proof_by_known_rewrite(fact, verify_state)?
            {
                return Ok(Some(AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(
                    result,
                )));
            }
        }

        Ok(None)
    }
}
