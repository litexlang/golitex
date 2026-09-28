use crate::prelude::*;
use crate::verification::builtin_rules::{
    compare_normalized_number_str_to_zero, normalized_decimal_string_is_even_integer,
    NumberCompareResult,
};
use crate::verification::verify_equality_by_builtin_rules::*;
use crate::verification::verify_number_in_standard_set::is_integer_after_simplification;

mod absolute_value;
mod elementary;
mod finite_set_product;
mod finite_set_sum;
mod iterated_ranges;
mod logarithms;
mod modulo;
mod power_identities;
mod power_inverses;
mod power_rules;
mod reduce;
mod square_root;
mod square_sums;
