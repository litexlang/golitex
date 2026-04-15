use crate::prelude::*;

/// Map any binary order literal to an equivalent [`LessFact`] or [`LessEqualFact`] (strict / weak).
/// Used by numeric builtin and shared congruence reasoning so `>` / `>=` / negated forms need not
/// duplicate `<` / `<=` logic.
pub fn normalize_positive_order_atomic_fact(atomic_fact: &AtomicFact) -> Option<AtomicFact> {
    match atomic_fact {
        AtomicFact::LessFact(f) => Some(AtomicFact::LessFact(f.clone())),
        AtomicFact::LessEqualFact(f) => Some(AtomicFact::LessEqualFact(f.clone())),
        AtomicFact::GreaterFact(f) => {
            Some(LessFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()).into())
        }
        AtomicFact::GreaterEqualFact(f) => {
            Some(LessEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()).into())
        }
        AtomicFact::NotLessFact(f) => {
            Some(LessEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()).into())
        }
        AtomicFact::NotLessEqualFact(f) => {
            Some(LessFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()).into())
        }
        AtomicFact::NotGreaterFact(f) => {
            Some(LessEqualFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into())
        }
        AtomicFact::NotGreaterEqualFact(f) => {
            Some(LessFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into())
        }
        _ => None,
    }
}
