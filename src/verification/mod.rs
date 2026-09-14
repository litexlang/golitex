mod atomic;
mod builtin_rules;
mod builtin_strategies;
pub mod builtin_theorem;
mod composite;
mod dispatch;
mod equality;
mod proof_search;
mod quantified;
mod support;
mod well_definedness;

#[cfg(test)]
#[path = "../../tests/unit/verification/equality_dispatch_source.rs"]
pub(in crate::verification) mod equality_dispatch_source;

#[cfg(test)]
#[path = "../../tests/unit/verification/universal_search_source.rs"]
pub(in crate::verification) mod universal_search_source;

#[cfg(test)]
#[path = "../../tests/unit/verification/number_compare_source.rs"]
pub(in crate::verification) mod number_compare_source;

use atomic::numeric_membership as verify_number_in_standard_set;
use equality::patterns as verify_equality_by_builtin_rules;

pub use atomic::atomic_except_equality::AlternateFactSearch;
pub use atomic::numeric_membership::{
    number_is_in_c_star, number_is_in_n, number_is_in_n_pos, number_is_in_q_neg,
    number_is_in_q_pos, number_is_in_q_star, number_is_in_r_neg, number_is_in_r_pos,
    number_is_in_r_star, number_is_in_z, number_is_in_z_neg, number_is_in_z_star,
};
pub use atomic::set_relations as verify_proper_set_relations_builtin;
pub use builtin_rules::{
    choice_function_for_definition_facts, choice_function_for_fact,
    compare_normalized_number_str_to_zero, compare_number_strings, general_cart_member_choice_fact,
    general_cart_member_fn_set, verify_choice_function_for_arg_types, NumberCompareResult,
};
pub use proof_search::builtin_rule_state::BuiltinRuleSearchState;
pub use proof_search::context_state::VerifyState;
pub use proof_search::universal_profile as known_forall_profile;
pub use support::helper::nested_obj_binder_normalized_fact_key;
