mod calculate;
mod collect_monomials;
mod monomial;
mod objs_equal_by_rational_expression_simplification;
mod process_division_after_polynomial_simplification;

#[cfg(test)]
mod simplify_polynomial_test;

pub use objs_equal_by_rational_expression_simplification::objs_equal_by_rational_expression_simplification;
pub use calculate::{
    add_decimal_str, mod_decimal_str, mul_signed_decimal_str, pow_decimal_str, sub_decimal_str,
};
