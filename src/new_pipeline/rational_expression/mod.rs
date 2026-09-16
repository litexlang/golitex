mod decimal_arithmetic;
mod denominator_clearing;
mod exact_division;
mod exact_rational;
mod helper;
mod monomial;
mod monomial_collection;
mod normalization;

pub use decimal_arithmetic::{
    evaluate_obj_to_normalized_decimal_number, two_objs_equal_by_closed_decimal_calculation,
};
pub use normalization::{
    algebraic_normalization_nonzero_requirements, objs_equal_by_rational_expression_evaluation,
};
