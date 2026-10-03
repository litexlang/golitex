mod closed_numeric_expr;
#[cfg(test)]
mod closed_numeric_expr_tests;
mod decimal_arithmetic;
mod decimal_comparison;
mod denominator_clearing;
mod exact_division;
pub mod exact_rational;
pub(crate) mod integer_factorization;
pub(crate) mod exact_radical;
pub(crate) mod exact_complex;
pub(crate) mod pi_multiple;
pub(crate) mod helper;
mod monomial;
mod monomial_collection;
mod normalization;

pub use closed_numeric_expr::{is_closed_numeric_expr, ClosedNumericExpr};
pub use decimal_arithmetic::{
    evaluate_obj_to_normalized_decimal_number, gcd_decimal_str_and_normalize,
    log_integer_power_decimal_str, normalized_decimal_str_is_integer,
    normalized_decimal_str_is_non_negative_integer, sqrt_decimal_str_and_normalize,
    two_objs_equal_by_closed_decimal_calculation,
};
pub use decimal_comparison::{
    compare_closed_numeric_objs, compare_number_strings, NumberCompareResult,
};
pub use normalization::{
    algebraic_normalization_nonzero_requirements, objs_equal_by_rational_expression_evaluation,
    objs_equal_by_complex_expression_evaluation, contains_imaginary_unit,
};

pub(crate) mod closed_scalar_membership;
