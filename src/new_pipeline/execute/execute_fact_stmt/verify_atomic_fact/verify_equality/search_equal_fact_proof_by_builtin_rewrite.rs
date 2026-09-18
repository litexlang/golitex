use super::by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Builtin equality rewrite dispatcher.
    // Only ClosedNumericEqualSubstitution — see EqualitySearchProofByBuiltinRewrite.
    pub fn search_equal_fact_proof_by_builtin_rewrite(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRewrite>> {
        if let Some(proof) = self
            .search_equal_fact_by_closed_numeric_equal_substitution(fact, verify_state)?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(proof),
            ));
        }
        Ok(None)
    }
}
