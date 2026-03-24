mod calculate;
mod collect_monomials;
mod monomial;
mod objs_equal_by_rational_expression_simplification;
mod process_division_after_polynomial_simplification;

#[cfg(test)]
mod simplify_polynomial_test;

pub use calculate::{
    add_decimal_str_and_normalize, mod_decimal_str_and_normalize, mul_signed_decimal_str,
    normalize_decimal_result, pow_decimal_str_and_normalize, sub_decimal_str_and_normalize,
};
pub use objs_equal_by_rational_expression_simplification::objs_equal_by_rational_expression_simplification;
