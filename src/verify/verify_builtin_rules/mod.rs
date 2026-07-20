// Built-in verification for non-equational atomic facts, split by topic.

mod abs_order_builtin;
mod equality_dispatch;
mod equality_function;
mod equality_numeric;
mod equality_structural;
mod in_fact_builtin;
mod mapping_properties_builtin;
mod non_equational_dispatch;
mod not_equal_builtin;
mod number_compare;
mod number_compare_div_elimination;
mod order_algebra_builtin;
mod order_normalize;
mod order_semantics_builtin;
mod set_relation_duality;
mod type_predicates_builtin;

pub(crate) use in_fact_builtin::{general_cart_member_fn_set, general_cart_member_pointwise_fact};
pub(crate) use number_compare::normalized_decimal_string_is_even_integer;
pub use number_compare::{compare_normalized_number_str_to_zero, NumberCompareResult};
