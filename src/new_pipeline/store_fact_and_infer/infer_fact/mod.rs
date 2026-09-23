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
//! | 3 | InFact membership families (Manual membership table) | done for N/sign/list/union/intersect/set_minus/cart/range/interval (+ set-builder/power_set) + fn_range/equal-FnSet/finite_seq|seq + family_union/index_union/index_intersect; remaining replacement/index_cart/struct |
//! | 4 | EqualFact: cart/tuple + `u-v=0` + positive-real power | done for fact-generating arms; set-builder/anon/numeric bind live on store indexes (known_equal_to_obj_with_free_params / closed numeric / InFunctionSet on store) |
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
