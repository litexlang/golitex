use crate::prelude::*;

/// Operator-level argument shape used to narrow universal conclusion search.
pub type ForallArgumentShape = Vec<(ObjKind, ObjOperatorString)>;

pub fn forall_argument_shape(atomic_fact: &AtomicFact) -> ForallArgumentShape {
    atomic_fact
        .args_ref()
        .into_iter()
        .map(|arg| arg.equality_in_forall_key_part())
        .collect()
}
