use crate::prelude::*;

/// Map any binary order literal to an equivalent [`LessFact`] or [`LessEqualFact`] (strict / weak).
/// Used by numeric builtin and shared congruence reasoning so `>` / `>=` / negated forms need not
/// duplicate `<` / `<=` logic.
pub fn normalize_positive_order_atomic_fact(
    runtime: &Runtime,
    atomic_fact: &AtomicFact,
) -> Option<AtomicFact> {
    match atomic_fact {
        AtomicFact::LessFact(f) => Some(AtomicFact::LessFact(f.clone())),
        AtomicFact::LessEqualFact(f) => Some(AtomicFact::LessEqualFact(f.clone())),
        AtomicFact::GreaterFact(f) => Some(
            runtime
                .new_less_fact(f.right.clone(), f.left.clone(), f.line_file.clone())
                .into(),
        ),
        AtomicFact::GreaterEqualFact(f) => Some(
            runtime
                .new_less_equal_fact(f.right.clone(), f.left.clone(), f.line_file.clone())
                .into(),
        ),
        AtomicFact::NotLessFact(f) => Some(
            runtime
                .new_less_equal_fact(f.right.clone(), f.left.clone(), f.line_file.clone())
                .into(),
        ),
        AtomicFact::NotLessEqualFact(f) => Some(
            runtime
                .new_less_fact(f.right.clone(), f.left.clone(), f.line_file.clone())
                .into(),
        ),
        AtomicFact::NotGreaterFact(f) => Some(
            runtime
                .new_less_equal_fact(f.left.clone(), f.right.clone(), f.line_file.clone())
                .into(),
        ),
        AtomicFact::NotGreaterEqualFact(f) => Some(
            runtime
                .new_less_fact(f.left.clone(), f.right.clone(), f.line_file.clone())
                .into(),
        ),
        _ => None,
    }
}
