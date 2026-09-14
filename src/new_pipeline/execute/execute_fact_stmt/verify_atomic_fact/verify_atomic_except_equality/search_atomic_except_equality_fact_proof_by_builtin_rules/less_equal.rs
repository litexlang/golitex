use crate::new_pipeline::ast::fact::LessEqualFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum LessEqualFactSearchProofByBuiltinRule {
    // Closed numeric comparison by evaluation, e.g. prove `1 <= 2`.
    ClosedNumericComparison(ClosedNumericComparisonBuiltinRuleProof),
    // Order reflexivity on one object, e.g. prove `x <= x`.
    OrderReflexivity(OrderReflexivityBuiltinRuleProof),
}

pub struct ClosedNumericComparisonBuiltinRuleProof {}

pub struct OrderReflexivityBuiltinRuleProof {
    pub repeated_object: Obj,
}

impl Runtime {
    // Builtin: `x <= x` holds by reflexivity.
    // Example: prove `a <= a`.
    pub fn search_less_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let _ = verify_state;
        if fact.left == fact.right {
            return Ok(Some(LessEqualFactSearchProofByBuiltinRule::OrderReflexivity(
                OrderReflexivityBuiltinRuleProof {
                    repeated_object: fact.left.clone(),
                },
            )));
        }
        Ok(None)
    }
}
