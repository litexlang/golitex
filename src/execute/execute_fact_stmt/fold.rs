//! Shared signature contract for ordered and unordered folds.
use crate::prelude::*;

/// A fold operates on one carrier through an unconditional binary operation.
/// Example: fn(x, y Z) Z. A narrower return carrier is not the fold carrier.
pub(crate) fn homogeneous_binary_carrier(signature: &FnSet) -> Option<&Obj> {
    if !signature.dom_facts.is_empty() {
        return None;
    }
    let mut parameters = signature
        .set_bound_parameters
        .groups
        .iter()
        .flat_map(|group| group.params.iter().map(move |_| group.param_type.as_ref()));
    let left = parameters.next()?;
    let right = parameters.next()?;
    if parameters.next().is_some() || left.ir() != right.ir() || left.ir() != signature.ret_set.ir()
    {
        return None;
    }
    Some(left)
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/fold_contract/tests.rs"]
mod tests;
