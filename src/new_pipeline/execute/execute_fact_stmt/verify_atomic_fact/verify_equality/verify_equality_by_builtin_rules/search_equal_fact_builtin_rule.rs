use super::search_equal_fact_builtin_rule_result::EqualitySearchProofByBuiltinRule;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Try equality builtin rules in order. First hit wins.
    // Definitional unfolds live in by_object_definition, not here.
    pub fn search_equal_fact_builtin_rule(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRule>> {
        if let Some(proof) =
            self.search_equal_fact_builtin_rule_equal_ir(fact, verify_state.clone())?
        {
            return Ok(Some(EqualitySearchProofByBuiltinRule::ByEqualIr(proof)));
        }
        if let Some(proof) = self.search_equal_fact_by_calculation(fact, verify_state)? {
            return Ok(Some(EqualitySearchProofByBuiltinRule::Calculation(proof)));
        }
        Ok(None)
    }
}
