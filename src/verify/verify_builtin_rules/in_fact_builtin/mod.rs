use crate::infer::obj_eligible_for_known_objs_in_fn_sets;
use crate::prelude::*;
use crate::verify::{
    compare_normalized_number_str_to_zero, number_is_in_n, number_is_in_n_pos, number_is_in_q_neg,
    number_is_in_q_nz, number_is_in_q_pos, number_is_in_r_neg, number_is_in_r_nz,
    number_is_in_r_pos, number_is_in_z, number_is_in_z_neg, number_is_in_z_nz,
    verify_equality_by_builtin_rules::verify_equality_by_they_are_the_same,
    verify_number_in_standard_set::is_integer_after_simplification, NumberCompareResult,
    VerifyState,
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

pub(crate) use general_cart::{general_cart_member_fn_set, general_cart_member_pointwise_fact};
use numeric_values::{
    arithmetic_obj_in_r_verified_by_builtin_rules_result,
    builtin_in_fact_result_for_evaluated_number_in_standard_set,
    builtin_not_in_fact_result_for_evaluated_number_in_standard_set,
    not_in_fact_verified_by_builtin_rules_result, number_in_set_verified_by_builtin_rules_result,
};
