mod decimal_arithmetic;
mod denominator_clearing;
mod exact_rational;
mod monomial;
mod monomial_collection;
mod normalization;

mod exact_division;

pub use decimal_arithmetic::{
    gcd_decimal_str_and_normalize, mul_signed_decimal_str, normalize_decimal_number_string,
};
pub use exact_rational::{
    evaluate_obj_to_exact_rational_for_eval, evaluate_obj_to_exact_rational_obj_for_eval,
};
pub use normalization::{
    algebraic_normalization_nonzero_requirements,
    complex_algebraic_normalization_nonzero_requirements, obj_is_integral_polynomial_fragment,
    objs_equal_by_complex_rational_expression_evaluation,
    objs_equal_by_rational_expression_evaluation,
    objs_form_verified_integral_polynomial_congruence_identity,
    objs_form_verified_integral_polynomial_identity,
};
