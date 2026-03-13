mod calculate;
mod collect_monomials;
mod monomial;
mod simplify_polynomial;

#[cfg(test)]
mod simplify_polynomial_test;

pub use simplify_polynomial::two_objs_equal_by_polynomial_simplification;