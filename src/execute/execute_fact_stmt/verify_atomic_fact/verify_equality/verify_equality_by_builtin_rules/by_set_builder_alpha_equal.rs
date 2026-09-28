use super::alpha_equal_helper::set_builders_alpha_equal;
use crate::ast::fact::EqualFact;
use crate::ast::obj::{Obj, SetFormer};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin BySetBuilderAlphaEqual: two SetBuilder objs are equal when they are
// structurally alpha-equivalent (binders may differ; free structure matches).
//
// Mathematical property: bounded comprehensions `{x S: P}` and `{y S: P}` denote
// the same set when the parameter sets agree and the bodies agree up to
// renaming the bound variable.
// Example: `{x R: x > 0} = {y R: y > 0}`.
//
// Proof payload is empty: the compared sides live on the surrounding EqualFact.
pub struct BySetBuilderAlphaEqualBuiltinRuleProof {}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_set_builder_alpha_equal(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<BySetBuilderAlphaEqualBuiltinRuleProof>> {
        let (Obj::SetFormer(SetFormer::SetBuilder(left)), Obj::SetFormer(SetFormer::SetBuilder(right))) = (&fact.left, &fact.right) else {
            return Ok(None);
        };
        if set_builders_alpha_equal(left, right) {
            Ok(Some(BySetBuilderAlphaEqualBuiltinRuleProof {}))
        } else {
            Ok(None)
        }
    }
}
