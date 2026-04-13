// Built-in verification for non-equational atomic facts, split by topic.

mod in_fact_builtin;
mod non_equational_dispatch;
mod not_equal_builtin;
mod number_compare;
mod number_compare_div_elimination;
mod order_normalize;
mod set_relation_duality;
mod type_predicates_builtin;

pub use number_compare::{
    compare_normalized_number_str_to_zero, NumberCompareResult,
};
