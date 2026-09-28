use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Stage order: builtin rule → known atomic → builtin strategy →
    // by definition → known strategy → known forall → (if allowed) builtin rewrite →
    // known rewrite.
    //
    // Why rewrite (after known/search slots): bridge goals that still mention
    // identifiers to closed-numeric / dual forms so specialized builtins can
    // fire, with an explicit certificate (not opaque resolve_obj). See
    // AtomicExceptEqualityFactSearchProofByBuiltinRewrite.
    // Ok(None) means no proof found; that is not a runtime error.
    pub fn search_atomic_except_equality_fact_proof(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
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

        if let Some(result) = self.search_atomic_except_equality_fact_proof_by_builtin_strategy(
            fact,
            verify_state.clone(),
        )? {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(result),
            ));
        }

        if let Some(result) =
            self.search_atomic_except_equality_fact_proof_by_definition(fact, verify_state.clone())?
        {
            return Ok(Some(AtomicExceptEqualityFactSearchedProof::ByDefinition(
                result,
            )));
        }

        if verify_state.can_use_forall_fact {
            if let Some(result) = self
                .search_atomic_except_equality_fact_proof_by_known_strategy(
                    fact,
                    verify_state.clone(),
                )?
            {
                return Ok(Some(
                    AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(result),
                ));
            }

            if let Some(result) = self
                .search_atomic_except_equality_fact_proof_by_known_forall_fact(
                    fact,
                    verify_state.clone(),
                )?
            {
                return Ok(Some(
                    AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(result),
                ));
            }
        }

        if verify_state.can_use_rewrite {
            if let Some(result) = self
                .search_atomic_except_equality_fact_proof_by_builtin_rewrite(
                    fact,
                    verify_state.clone(),
                )?
            {
                return Ok(Some(
                    AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(result),
                ));
            }

            if let Some(result) = self
                .search_atomic_except_equality_fact_proof_by_known_rewrite(
                    fact,
                    verify_state,
                )?
            {
                return Ok(Some(
                    AtomicExceptEqualityFactSearchedProof::ByKnownRewrite(result),
                ));
            }
        }

        Ok(None)
    }
}
