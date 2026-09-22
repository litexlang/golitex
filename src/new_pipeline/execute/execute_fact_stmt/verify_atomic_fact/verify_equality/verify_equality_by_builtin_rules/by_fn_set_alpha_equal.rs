use super::alpha_equal_helper::fn_sets_alpha_equal;
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{Obj, FunctionSpace};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin ByFnSetAlphaEqual: two FnSet objs are equal when they are
// structurally alpha-equivalent (binders may differ; free structure matches).
//
// Mathematical property: function-spaces are identified up to renaming of
// parameter binders. Domains, domain facts, and return sets must agree under
// that renaming.
// Example: `R -> R = R -> R` even when the two arrows were parsed separately
// (distinct binder IdentifierIds).
//
// Proof payload is empty: the compared sides live on the surrounding EqualFact.
pub struct ByFnSetAlphaEqualBuiltinRuleProof {}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_fn_set_alpha_equal(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByFnSetAlphaEqualBuiltinRuleProof>> {
        let (Obj::FunctionSpace(FunctionSpace::FnSet(left)), Obj::FunctionSpace(FunctionSpace::FnSet(right))) = (&fact.left, &fact.right) else {
            return Ok(None);
        };
        if fn_sets_alpha_equal(left, right) {
            Ok(Some(ByFnSetAlphaEqualBuiltinRuleProof {}))
        } else {
            Ok(None)
        }
    }
}
