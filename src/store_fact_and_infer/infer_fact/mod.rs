//! Local inference after a fact is stored.
//!
//! Outer dispatch mirrors `Fact` shape. Non-atomic arms are not all "atomic wrappers":
//! - And / Chain adjacent edges: delegate to `infer_atomic_fact` (Chain also has
//!   shape-level transitive closure).
//! - NotForall: shape rewrite to a counterexample exist, then `store_inferred`.
//! - ExistUnique / NotExist: shape rewrite to uniqueness / De Morgan forall.
//! - Or / plain Exist / Forall*: intentionally `NoInfer` unless a shape rule applies.
//!
//! # Legacy → new_pipeline migration (Builtin Inference) — closed
//!
//! | Batch | Legacy source | Status |
//! |---|---|---|
//! | 0 | And / Chain / NotForall / Or / Forall dispatch | done |
//! | 1 | `exist!` uniqueness forall; `not exist` De Morgan forall | done |
//! | 2 | NormalAtomic: expand def + param-type projection | done |
//! | 3 | InFact membership families | done (incl. index_cart) |
//! | 4 | EqualFact fact-generating arms | done (indexes on store; `u-v=0⇒u=v` is verify builtin) |
//! | 5 | Subset/Superset; order→sign; `$is_cart` dim; mul-by-(−1) | done (`N⇒>=0` is verify builtin) |
//! | — | `$fn_eq` / Replacement Obj / Struct eager infer | **won't migrate** (see README) |
//!
//! Details and won't-migrate rationale: `store_fact_and_infer/README.md`.

pub mod infer_and_fact;
pub mod infer_atomic_fact;
pub mod infer_chain_fact;
pub mod infer_exist_shaped_fact;
pub mod infer_fact;
pub mod infer_forall_fact;
pub mod infer_forall_fact_with_iff;
pub mod infer_not_forall_fact;
pub mod infer_or_fact;
