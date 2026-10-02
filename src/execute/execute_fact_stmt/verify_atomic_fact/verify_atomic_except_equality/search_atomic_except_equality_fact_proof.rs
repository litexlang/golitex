use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Cheap phase: known atomic → known special property → builtin rule.
    // Deep phase (can_use_def_and_known_forall_and_known_strategy, remaining_deep_search_depth > 0):
    //   after_deep_search() once, then
    //   verify_by_strategy → by definition → known forall →
    //   (can_use_rewrite) builtin rewrite → known rewrite.
    //
    // Builtin entry uses its boolean; only deep entry consumes the depth budget.
    // Premise-producing arms disable ordinary recursive builtin entry; known
    // and calculation leaves remain available. Strategy cite-only bypasses
    // this entry and calls by_builtin_rule directly.
    // Ok(None) means no proof found; that is not a runtime error.
    pub fn search_atomic_except_equality_fact_proof(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        if let Some(proof) = self.search_atomic_except_equality_fact_proof_by_known(
            fact, verify_state.clone(),
        )? {
            return Ok(Some(proof));
        }

        if verify_state.can_use_builtin_rule {
            if let Some(result) = self.search_atomic_except_equality_fact_proof_by_builtin_rule(
                fact,
                verify_state.clone(),
            )? {
                return Ok(Some(AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                    result,
                )));
            }
        }

        if !verify_state.can_use_def_and_known_forall_and_known_strategy
            || verify_state.remaining_deep_search_depth == 0
        {
            return Ok(None);
        }

        let deep_state = verify_state.after_deep_search();

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
