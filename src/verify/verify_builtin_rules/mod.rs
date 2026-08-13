// Built-in verification for non-equational atomic facts, split by topic.

mod abs_order_builtin;
mod complex_builtin;
mod coprime_builtin;
mod equality_dispatch;
mod equality_function;
mod equality_numeric;
mod equality_structural;
mod in_fact_builtin;
mod mapping_properties_builtin;
mod native_exp_sign_factorial;
mod native_integer_extrema;
mod non_equational_dispatch;
mod not_equal_builtin;
mod number_compare;
mod number_compare_div_elimination;
mod order_algebra_builtin;
mod order_normalize;
mod order_semantics_builtin;
mod prime_builtin;
mod set_relation_duality;
mod trigonometry;
mod type_predicates_builtin;

pub(crate) use in_fact_builtin::{
    builtin_in_fact_result_for_evaluated_number_in_standard_set,
    builtin_not_in_fact_result_for_evaluated_number_in_standard_set,
    choice_function_for_definition_facts, choice_function_for_fact,
    general_cart_member_choice_fact, general_cart_member_fn_set,
    verify_choice_function_for_arg_types,
};
pub(crate) use number_compare::normalized_decimal_string_is_even_integer;
pub use number_compare::{compare_normalized_number_str_to_zero, NumberCompareResult};
pub(crate) use order_normalize::normalize_positive_order_atomic_fact;
