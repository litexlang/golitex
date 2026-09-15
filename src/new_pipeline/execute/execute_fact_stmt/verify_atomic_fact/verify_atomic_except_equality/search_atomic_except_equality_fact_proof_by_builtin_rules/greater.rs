use crate::new_pipeline::ast::fact::GreaterFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum GreaterFactSearchProofByBuiltinRule {
    // Closed numeric comparison by evaluation, e.g. prove `2 > 1`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {}

impl Runtime {
    pub fn search_greater_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &GreaterFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterFactSearchProofByBuiltinRule>> {
        Ok(None)
    }
}
