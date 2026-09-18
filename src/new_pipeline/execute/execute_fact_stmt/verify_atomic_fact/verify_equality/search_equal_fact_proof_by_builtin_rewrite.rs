use super::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Builtin equality rewrite dispatcher (one variant ↔ one dedicated search).
    // Mathematical property / examples: see EqualitySearchProofByBuiltinRewrite.
    pub fn search_equal_fact_proof_by_builtin_rewrite(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRewrite>> {
        if let Some(proof) = self
            .search_equal_fact_by_closed_numeric_equal_substitution(fact, verify_state.clone())?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(proof),
            ));
        }
        if let Some(proof) =
            self.search_equal_fact_by_congruence_substitution(fact, verify_state)?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinRewrite::CongruenceSubstitution(proof),
            ));
        }
        Ok(None)
    }
}
