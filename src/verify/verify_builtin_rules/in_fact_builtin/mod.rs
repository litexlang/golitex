use crate::prelude::*;
use crate::verify::{
    compare_normalized_number_str_to_zero, number_is_in_c_star, number_is_in_n, number_is_in_n_pos,
    number_is_in_q_neg, number_is_in_q_pos, number_is_in_q_star, number_is_in_r_neg,
    number_is_in_r_pos, number_is_in_r_star, number_is_in_z, number_is_in_z_neg,
    number_is_in_z_star, verify_equality_by_builtin_rules::objs_match_for_pattern,
    verify_number_in_standard_set::is_integer_after_simplification, NumberCompareResult,
    UseContextVerifyState,
};
use std::collections::HashMap;

mod cart_membership;
mod dispatch;
mod general_cart;
mod numeric_membership;
mod numeric_values;
mod operator_signature;
mod set_membership;
mod structured_membership;

pub(crate) use general_cart::{
    choice_function_for_definition_facts, choice_function_for_fact,
    general_cart_member_choice_fact, general_cart_member_fn_set,
    verify_choice_function_for_arg_types,
};
pub(crate) use numeric_values::{
    builtin_in_fact_result_for_evaluated_number_in_standard_set,
    builtin_not_in_fact_result_for_evaluated_number_in_standard_set,
};
use numeric_values::{
    not_in_fact_verified_by_builtin_rules_result, number_in_set_verified_by_builtin_rules_result,
    number_in_set_verified_by_builtin_rules_result_with_subgoals,
};
