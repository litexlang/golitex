mod compile_additive_inference;
mod compile_assumption_stmt_result;
mod compile_builtin_cart_membership;
mod compile_builtin_continuity_theorem;
mod compile_builtin_dense_order_theorem;
mod compile_builtin_finite_subset_theorem;
mod compile_builtin_fold_theorem;
mod compile_builtin_function_limit_theorem;
mod compile_builtin_function_membership;
mod compile_builtin_membership_theorem;
mod compile_builtin_norm_theorem;
mod compile_builtin_number_theory_theorem;
mod compile_builtin_reduced_fraction_theorem;
mod compile_builtin_sequence_limit_theorem;
mod compile_builtin_tuple_theorem;
mod compile_by_stmt_result;
mod compile_callee_constructor;
mod compile_captured_function;
mod compile_cart_coordinate_inferences;
mod compile_chain_closures;
mod compile_claim_stmt_result;
mod compile_compound_fact;
mod compile_compound_stores;
mod compile_def_abstract_prop_stmt_result;
mod compile_def_prop_stmt_result;
mod compile_def_struct_stmt_result;
mod compile_def_thm_stmt_result;
mod compile_define_obj_stmt_result;
mod compile_definition_stmt_result;
mod compile_dependent_struct;
mod compile_division_inference;
mod compile_dvd_inferences;
mod compile_equality_inferences;
mod compile_eval_aggregate_value;
mod compile_eval_closed_value;
mod compile_eval_function_value;
mod compile_eval_integer_value;
mod compile_eval_log_value;
mod compile_eval_matrix_value;
mod compile_eval_radical_value;
mod compile_eval_real_value;
mod compile_eval_stmt_result;
mod compile_expand_range_stmt_result;
mod compile_fact_stmt_result;
mod compile_family_intersection_member;
mod compile_finite_function_membership;
mod compile_finite_product_pointwise;
mod compile_frobenius_scale_law;
mod compile_function_continuity;
mod compile_function_continuity_binary;
mod compile_function_continuity_composition;
mod compile_function_continuity_definition;
mod compile_function_continuity_unary;
mod compile_function_domain;
mod compile_function_limit;
mod compile_function_limit_binary;
mod compile_function_limit_constant;
mod compile_function_limit_definition;
mod compile_function_limit_eventual;
mod compile_function_limit_local;
mod compile_function_limit_order;
mod compile_function_limit_projections;
mod compile_function_limit_sides;
mod compile_function_limit_squeeze;
mod compile_function_limit_unary;
mod compile_function_template;
mod compile_have_fn_by_exist_result;
mod compile_have_fn_by_induc_result;
mod compile_have_fn_equal_stmt_result;
mod compile_have_obj_by_exist_facts_result;
mod compile_have_obj_equal_stmt_result;
mod compile_have_obj_in_nonempty_set_stmt_result;
mod compile_identifier_definition;
mod compile_indexed_set_membership;
mod compile_inferred_obj;
mod compile_infinite_function_limit;
mod compile_integer_interval_inference;
mod compile_intersection_inference;
mod compile_known_application;
mod compile_let_stmt_result;
mod compile_local_assumptions;
mod compile_matrix_adjugate_laws;
mod compile_matrix_algebra_laws;
mod compile_matrix_apply_laws;
mod compile_matrix_inverse_laws;
mod compile_matrix_simple_laws;
mod compile_matrix_transform_laws;
mod compile_nonzero_factor_inference;
mod compile_obtain_constructor;
mod compile_obtain_obj_from_atomic_fact_stmt_result;
mod compile_obtain_obj_from_exist_fact_stmt_result;
mod compile_order_bound_inferences;
mod compile_positive_power_inference;
mod compile_prime_inferences;
mod compile_prop_clause_instance;
mod compile_real_accumulation;
mod compile_real_limit_accumulation;
mod compile_recursive_unfold_result;
mod compile_register_stmt_result;
mod compile_release_and_expand_result;
mod compile_release_cart_def_result;
mod compile_release_obj_def_result;
mod compile_release_regularity_result;
mod compile_release_struct_def_result;
mod compile_release_tuple_def_result;
mod compile_replacement_result;
mod compile_returned_function;
mod compile_riemann_definition;
mod compile_riemann_integral;
mod compile_run;
mod compile_sequence_inference;
mod compile_set_minus_inference;
mod compile_sketch_stmt_result;
mod compile_stmt_result;
mod compile_store_result;
mod compile_strategy;
mod compile_struct_conditions;
mod compile_struct_field_value;
mod compile_struct_fields;
mod compile_struct_header;
mod compile_struct_membership;
mod compile_struct_projection;
mod compile_struct_raw_value;
mod compile_subset_inferences;
mod compile_subtractive_inference;
mod compile_template_callee_constructor;
mod compile_template_case_unfold;
mod compile_template_function;
mod compile_template_obtain;
mod compile_template_record;
mod compile_template_stmt_result;
mod compile_trace_laws;
mod compile_transitive_relation;
mod compile_tuple_coordinate_inference;
mod compile_tuple_coordinate_membership;
mod compile_vector_laws;
mod compile_witness_stmt_result;
mod helper;
mod lean_compile_error;
mod litex_to_lean_compiler;
mod module_source_position;
mod names;
mod source_position;
mod source_queries;

pub use compile_run::compile_run;
pub use lean_compile_error::LeanCompileError;
pub use litex_to_lean_compiler::LitexToLeanCompiler;

#[cfg(test)]
mod abs_function_normalization_tests;
#[cfg(test)]
mod abs_natural_power_tests;
#[cfg(test)]
mod add_zero_from_equalities_tests;
#[cfg(test)]
mod claim_tests;
#[cfg(test)]
mod concrete_prop_tests;
#[cfg(test)]
mod equality_known_forall_tests;
#[cfg(test)]
mod function_call_tests;
#[cfg(test)]
mod function_return_tests;
#[cfg(test)]
mod induction_tests;
#[cfg(test)]
mod numeric_function_call_tests;
#[cfg(test)]
mod or_fact_tests;
#[cfg(test)]
mod positive_function_target_tests;
#[cfg(test)]
mod positive_membership_tests;
#[cfg(test)]
mod positive_order_strategy_tests;
#[cfg(test)]
mod positive_power_cursor_tests;
#[cfg(test)]
mod positive_power_inference_tests;
#[cfg(test)]
mod prop_domain_tests;
#[cfg(test)]
mod rational_call_leaf_tests;
#[cfg(test)]
mod recursive_function_tests;
#[cfg(test)]
mod release_theorem_tests;
#[cfg(test)]
mod selected_arithmetic_tests;
#[cfg(test)]
mod set_tests;
#[cfg(test)]
mod tests;

mod compile_builder_constructor;

mod compile_have_fn_cases_result;
mod compile_piecewise_unfold_result;
mod piecewise_evidence;

mod compile_mapping_properties;

mod compile_function_range;

mod compile_range_preimage;

mod compile_function_preimage;
mod compile_preimage_constructor;
mod compile_preimage_inference;
mod compile_preimage_membership;
mod compile_preimage_subset;

mod compile_composition;

mod compile_release_choice_result;

mod compile_release_zorn_result;

#[cfg(test)]
mod finite_set_stat_tests;

#[cfg(test)]
mod aggregate_tests;

mod compile_real_interval_inference;

mod compile_basic_predicates;

mod compile_matrix;

mod compile_matrix_entrywise;

mod compile_matrix_scale;

mod compile_builtin_determinant_theorem;
mod compile_builtin_matrix_power_theorem;
mod compile_builtin_rank_theorem;
mod compile_finite_inner_product;
mod compile_matrix_adjugate;
mod compile_matrix_apply;
mod compile_matrix_cofactor;
mod compile_matrix_determinant;
mod compile_matrix_diagonal;
mod compile_matrix_inverse;
mod compile_matrix_minor;
mod compile_matrix_multiply;
mod compile_matrix_norm;
mod compile_matrix_outer;
mod compile_matrix_power;
mod compile_matrix_rank;
mod compile_matrix_square_scalar;
mod compile_matrix_trace;

mod compile_builtin_extremum_certificate_theorem;
mod compile_builtin_extremum_theorem;
mod compile_builtin_sequence_extremum_theorem;
mod compile_curl;
mod compile_derivative_interior;
mod compile_divergence;
mod compile_function_derivative;
mod compile_function_derivative_definition;
mod compile_gradient;
mod compile_hessian;
mod compile_jacobian;
mod compile_laplacian;
mod compile_multivariable_scalar_limit;
mod compile_multivariable_vector_limit;
mod compile_partial_derivative;
mod compile_pointwise_derivative;
mod compile_real_extrema;
mod compile_real_set_bounds;
mod compile_scalar_differential;
mod compile_second_partial;
mod compile_sequence_analysis;
mod compile_sequence_epsilon;
mod compile_sequence_extremum;
mod compile_sequence_extremum_definition;
mod compile_sequence_limit;
mod compile_total_differential;

mod compile_call_prefix;
mod compile_constant_function_range;
mod compile_finite_complete_domain;
mod compile_function_graph_empty;
mod compile_function_graph_nonempty;
mod compile_function_space_nonempty;
mod compile_function_space_singleton;
mod compile_power_set_inference;

mod compile_builtin_enumeration_sum_theorem;
mod compile_builtin_finite_index_theorem;
mod compile_builtin_finite_sum_theorem;
mod compile_builtin_finite_summand_theorem;
mod compile_builtin_indexed_choice_theorem;
mod compile_builtin_inner_positive_theorem;
mod compile_builtin_intersection_facts_theorem;
mod compile_builtin_range_sum_theorem;
