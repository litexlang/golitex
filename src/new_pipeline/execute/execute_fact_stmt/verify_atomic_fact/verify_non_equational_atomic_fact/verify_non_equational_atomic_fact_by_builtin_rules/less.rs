use crate::new_pipeline::ast::fact::LessFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum LessFactSearchProofByBuiltinRule {
    // Closed numeric comparison by evaluation, e.g. prove `1 < 2`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {}

impl Runtime {
    pub fn search_less_fact_proof_by_builtin_rule(
        &mut self,
        fact: &LessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
