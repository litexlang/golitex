mod compile_abs_identities;
mod compile_add_zero_from_equalities;
mod compile_aggregate_calculation;
mod compile_builtin_rewrite;
mod compile_calculation;
mod compile_cartesian_definition;
mod compile_closed_range_literal;
mod compile_complex_calculation;
mod compile_congruence;
mod compile_difference_zero;
mod compile_equal_from_known_difference_zero;
mod compile_equality_result;
mod compile_equivalence_class;
mod compile_finite_coordinate_expansion;
mod compile_function_definition;
mod compile_known_special_property;
mod compile_natural_power_laws;
mod compile_order_antisymmetry;
mod compile_positive_power_zero;
mod compile_set_identities;
mod compile_sign_identities;
mod compile_sqrt_square;
mod compile_zero_product;

#[cfg(test)]
mod known_special_property_tests;

mod compile_subtraction_from_addition;

pub(in crate::compile_to_lean) use compile_cartesian_definition::validate_cart_definition;

mod compile_composition_equality;
mod compile_finite_aggregate_calculation;
mod compile_set_minus_identities;
mod compile_union_distribution;

mod compile_seq;

mod compile_exp_log;

mod compile_inverse_trig;
mod compile_trig;

mod compile_complex_observations;
mod compile_fold_identity;

mod compile_fold_calculation;

mod compile_hyperbolic;

mod compile_matrix;
mod compile_matrix_reduction;

mod compile_matrix_evaluation;

mod compile_matrix_residual;
