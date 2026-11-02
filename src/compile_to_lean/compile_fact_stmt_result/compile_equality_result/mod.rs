mod compile_abs_builtin;
mod compile_abs_identities;
mod compile_abs_product_strategy;
mod compile_add_zero_from_equalities;
mod compile_aggregate_calculation;
mod compile_builtin_rewrite;
mod compile_calculation;
mod compile_cartesian_coordinate_strategy;
mod compile_cartesian_definition;
mod compile_cartesian_union;
mod compile_closed_range_literal;
mod compile_complex_calculation;
mod compile_congruence;
mod compile_cos_integer_offset;
mod compile_difference_zero;
mod compile_elementary_arithmetic;
mod compile_elementary_identity;
mod compile_equal_from_known_difference_zero;
mod compile_equality_result;
mod compile_equivalence_class;
mod compile_exponential_logarithm_identity;
mod compile_finite_cardinality;
mod compile_finite_coordinate_expansion;
mod compile_function_definition;
mod compile_integer_elementary;
mod compile_known_special_property;
mod compile_log_algebra;
mod compile_mod_congruence;
mod compile_natural_power_laws;
mod compile_order_antisymmetry;
mod compile_positive_power_zero;
mod compile_returned_function_beta;
mod compile_rounding_bounds;
mod compile_scalar_extra;
mod compile_scalar_identity;
mod compile_set_builtin;
mod compile_set_identities;
mod compile_sign_identities;
mod compile_sqrt_builtin;
mod compile_sqrt_square;
mod compile_template_tuple_beta;
mod compile_transcendental_builtin;
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

mod compile_complex_builtin;
mod compile_complex_observations;
mod compile_fold_identity;

mod compile_finite_fold_calculation;
mod compile_fold_calculation;

mod compile_hyperbolic;

mod compile_matrix;
mod compile_matrix_reduction;

mod compile_matrix_evaluation;

mod compile_matrix_residual;
mod compile_native_matrix_law;

mod compile_homogeneous_cart;

mod compile_trig_principal;

mod compile_power_builtin;

mod compile_integer_power_laws;

mod compile_function_application_strategy;
