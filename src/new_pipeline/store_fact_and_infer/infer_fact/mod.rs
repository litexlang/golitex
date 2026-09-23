//! Local inference after a fact is stored.
//!
//! Outer dispatch mirrors `Fact` shape. Non-atomic arms are not all "atomic wrappers":
//! - And / Chain adjacent edges: delegate to `infer_atomic_fact` (Chain also has
//!   shape-level transitive closure).
//! - NotForall: shape rewrite to a counterexample exist, then `store_inferred`.
//! - ExistUnique / NotExist: shape rewrite to uniqueness / De Morgan forall.
//! - Or / plain Exist / Forall*: intentionally `NoInfer` unless a shape rule applies.
//!
//! # Legacy → new_pipeline migration batches (Builtin Inference)
//!
//! Move like packing boxes — one batch green before the next.
//!
//! | Batch | Legacy source | Status |
//! |---|---|---|
//! | 0 | And / Chain / NotForall / Or / Forall dispatch | done (framework) |
//! | 1 | `exist!` uniqueness forall; `not exist` De Morgan forall | done |
//! | 2 | NormalAtomic: expand def + param-type projection | done |
//! | 3 | InFact membership families (Manual membership table) | done for N/sign/list/union/intersect/set_minus/cart/range/interval (+ set-builder/power_set); remaining fn_range/index_*/family_*/replacement/finite_seq|seq/struct |
//! | 4 | EqualFact: cart/tuple + `u-v=0` | partial; remaining: set-builder side, anonymous-fn knowledge, numeric value bind, positive-real power (no matrix — not in new_pipeline AST) |
//! | 5 | Subset/Superset forall; order→sign; `$is_cart` dim bound; mul-by-(-1) flip | done |
//! | 6 | FnEqual → ordinary `=`; remaining atomic stubs | pending |

pub mod infer_and_fact;
pub mod infer_atomic_fact;
pub mod infer_chain_fact;
pub mod infer_exist_shaped_fact;
pub mod infer_fact;
pub mod infer_forall_fact;
pub mod infer_forall_fact_with_iff;
pub mod infer_not_forall_fact;
pub mod infer_or_fact;
