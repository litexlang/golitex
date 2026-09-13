use super::search_equal_fact_proof_by_builtin_rule_result::EqualitySearchProofByBuiltinRule;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Try equality builtin rules in order. First hit wins.
    pub fn search_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRule>> {
        if let Some(proof) =
            self.search_equal_fact_proof_by_literally_the_same(fact, verify_state)?
        {
            return Ok(Some(EqualitySearchProofByBuiltinRule::LiterallyTheSame(
                proof,
            )));
        }
        Ok(None)
    }
}
