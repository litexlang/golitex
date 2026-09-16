use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Stage order: builtin rule → known atomic → builtin strategy →
    // by definition → known forall → (if allowed) builtin rewrite →
    // known rewrite.
    // Rewrite stages replace legacy opaque resolve_obj with explicit
    // certificates (OrderDual, registered reflexivity/symmetry, …).
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

        if let Some(result) =
            self.search_atomic_except_equality_fact_proof_by_definition(fact, verify_state.clone())?
        {
            return Ok(Some(AtomicExceptEqualityFactSearchedProof::ByDefinition(
                result,
            )));
        }

        if let Some(result) = self.search_atomic_except_equality_fact_proof_by_builtin_strategy(
            fact,
            verify_state.clone(),
        )? {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(result),
            ));
        }

        if verify_state.can_use_forall_fact {
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
