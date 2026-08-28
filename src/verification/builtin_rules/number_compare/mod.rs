use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;
use crate::result::{
    OrderReflexivityBuiltinRuleEvidence, RuntimeResolvedNumericComparisonBuiltinRuleEvidence,
};
use crate::verification::verify_equality_by_builtin_rules::objs_match_for_pattern;

mod additive_sign;
mod decimal_comparison;
mod finite_set_cardinality;
mod integer_membership_bounds;
mod known_numeric_bounds;
mod logarithm_order;
mod modulo_bounds;
mod multiplicative_sign;
mod numeric_dispatch;
mod order_equivalences;
mod power_sign;
mod roots_and_absolute_value;
mod subtraction_order;

use decimal_comparison::normalized_decimal_string_is_integer;
pub use decimal_comparison::{
    compare_normalized_number_str_to_zero, compare_number_strings,
    normalized_decimal_string_is_even_integer, NumberCompareResult,
};
