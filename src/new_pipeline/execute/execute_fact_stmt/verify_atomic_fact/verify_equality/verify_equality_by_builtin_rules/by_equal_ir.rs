use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin ByEqualIr: left and right have the same ObjIR ⇒ equality.
//
// Mathematical property: identical IR keys denote the same object identity
// for exact match. Plain IR embeds `#id#name`, so two binders that only share
// a letter are not EqualIr-equal. FnSet / SetBuilder alpha equality is handled
// by dedicated builtins (ByFnSetAlphaEqual / ByAnonymousFnAlphaEqual /
// BySetBuilderAlphaEqual / ByEqualToObjWithFreeParamsLookup).
// Example: prove `1 + 0 = 1 + 0` because both sides share the same ObjIR.
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
