//! Local inference after a fact is stored.
//!
//! Outer dispatch mirrors fact shape (like verify_fact). Atomic inference is a
//! fixed additive stage pipeline — matching rules all fire; it is not
//! first-hit proof search.

pub mod infer_and_fact;
pub mod infer_atomic_fact;
pub mod infer_chain_fact;
pub mod infer_fact;
pub mod infer_not_forall_fact;
