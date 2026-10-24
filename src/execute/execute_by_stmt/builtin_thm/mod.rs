mod antiderivatives;
mod builtin_thm;
mod calculus_substitution;
mod continuity;
pub(crate) mod derive_real_sequence;
mod folds;
mod function_derivatives;
mod helper;
mod intersection;
mod membership;
mod number_theory;
mod real_analysis;
mod riemann_integrals;
mod sums;

pub(super) use builtin_thm::prepare_builtin_thm;

#[cfg(test)]
mod tests;

mod sequence_limits;

mod function_limits;

mod sequence_extrema;

pub(crate) mod derive_sequence_extrema_bounded;

mod matrices;
