use super::helper::{anonymous_fns_alpha_equal, fn_sets_alpha_equal, set_builders_alpha_equal, compound_objs_alpha_equal};
use super::result::*;
use crate::ast::fact::EqualFact;
use crate::ast::obj::{FunctionSpace, Obj, SetFormer};

// First truth-search stage, after the caller has established WD. Exact IR
// identity wins first; otherwise compare binder shapes without any proof search.
// Example: fn(x R) R = fn(y R) R, even with builtin entry disabled. Free identifiers
// must retain their identities; only bound identifiers may be renamed.
pub fn search_equal_fact_proof_by_they_are_the_same(
    fact: &EqualFact,
) -> Option<TheyAreTheSameProof> {
    if fact.left.ir() == fact.right.ir() {
        return Some(SameIrProof::new().into());
    }
    let shape: SameFreeParamShapeProof = match (&fact.left, &fact.right) {
        (
            Obj::FunctionSpace(FunctionSpace::FnSet(left)),
            Obj::FunctionSpace(FunctionSpace::FnSet(right)),
        ) if fn_sets_alpha_equal(left, right) => FnSetAlphaProof::new().into(),
        (
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(left)),
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(right)),
        ) if anonymous_fns_alpha_equal(left, right) => AnonymousFnAlphaProof::new().into(),
        (
            Obj::SetFormer(SetFormer::SetBuilder(left)),
            Obj::SetFormer(SetFormer::SetBuilder(right)),
        ) if set_builders_alpha_equal(left, right) => SetBuilderAlphaProof::new().into(),
        (left, right) if compound_objs_alpha_equal(left, right) => CompoundObjAlphaProof::new().into(),
        _ => return None,
    };
    Some(shape.into())
}
