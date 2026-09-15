use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin ByEqualIr: left and right have the same ObjIR ⇒ equality.
//
// Mathematical property: after binder objs are alpha-normalized into IR
// (`□N` slots), two objects with identical IR are the same identity key.
// Example: prove `{x R: x > 0} = {y R: y > 0}` because both IR as
// `{□0 R: □0 > 0}`.
//
// Proof payload is empty: the compared sides live on the surrounding EqualFact.
pub struct ByEqualIrBuiltinRuleProof {}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equal_ir(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByEqualIrBuiltinRuleProof>> {
        if fact.left.ir() == fact.right.ir() {
            Ok(Some(ByEqualIrBuiltinRuleProof {}))
        } else {
            Ok(None)
        }
    }
}
