use super::alpha_equal_helper::anonymous_fns_alpha_equal;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{Obj, FunctionSpace};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin ByAnonymousFnAlphaEqual: two AnonymousFn objs are equal when they are
// structurally alpha-equivalent (binders may differ; body and signature match).
//
// Mathematical property: defining functions are identified up to binder renaming.
// Example: `fn(x R) R {x + 1} = fn(y R) R {y + 1}`.
//
// Proof payload is empty: the compared sides live on the surrounding EqualFact.
pub struct ByAnonymousFnAlphaEqualBuiltinRuleProof {}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_anonymous_fn_alpha_equal(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByAnonymousFnAlphaEqualBuiltinRuleProof>> {
        let (Obj::FunctionSpace(FunctionSpace::AnonymousFn(left)), Obj::FunctionSpace(FunctionSpace::AnonymousFn(right))) = (&fact.left, &fact.right) else {
            return Ok(None);
        };
        if anonymous_fns_alpha_equal(left, right) {
            Ok(Some(ByAnonymousFnAlphaEqualBuiltinRuleProof {}))
        } else {
            Ok(None)
        }
    }
}
