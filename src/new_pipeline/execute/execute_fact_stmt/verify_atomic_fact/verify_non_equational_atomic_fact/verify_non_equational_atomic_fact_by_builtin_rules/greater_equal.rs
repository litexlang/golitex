use crate::new_pipeline::ast::fact::GreaterEqualFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum GreaterEqualFactSearchProofByBuiltinRule {
    // Closed numeric comparison by evaluation, e.g. prove `2 >= 1`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Order reflexivity on one object, e.g. prove `x >= x`.
    OrderReflexivity(OrderReflexivityBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {}

pub struct OrderReflexivityBuiltinRuleProof {
    pub repeated_object: Obj,
}

impl Runtime {
    pub fn search_greater_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &GreaterEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterEqualFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
