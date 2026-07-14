use crate::prelude::*;
use crate::verify::verify_builtin_rules::{
    compare_normalized_number_str_to_zero, normalized_decimal_string_is_even_integer,
    NumberCompareResult,
};
use crate::verify::verify_equality_by_builtin_rules::*;
use crate::verify::verify_number_in_standard_set::is_integer_after_simplification;

mod absolute_value;
mod algebra_context;
mod elementary;
mod finite_set_product;
mod finite_set_sum;
mod iterated_ranges;
mod logarithms;
mod modulo;
mod power_identities;
mod power_inverses;
mod power_rules;
mod square_root;
