mod algebraic_normalization;
mod collect_monomials;
mod evaluate;
mod evaluate_rational;
mod monomial;
mod process_division_after_polynomial_simplification;

mod evaluate_div;

pub use algebraic_normalization::{
    complex_algebraic_normalization_nonzero_requirements, obj_is_integral_polynomial_fragment,
    objs_equal_by_complex_rational_expression_evaluation,
    objs_equal_by_rational_expression_evaluation, objs_form_verified_integral_polynomial_identity,
};
pub use evaluate::{
    gcd_decimal_str_and_normalize, mul_signed_decimal_str, normalize_decimal_number_string,
};
pub use evaluate_rational::{
    evaluate_obj_to_exact_rational_for_eval, evaluate_obj_to_exact_rational_obj_for_eval,
};
