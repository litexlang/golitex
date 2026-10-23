mod compile_additive_inference;
mod compile_builtin_cart_membership;
mod compile_builtin_function_membership;
mod compile_builtin_membership_theorem;
mod compile_builtin_tuple_theorem;
mod compile_by_stmt_result;
mod compile_callee_constructor;
mod compile_cart_coordinate_inferences;
mod compile_chain_closures;
mod compile_claim_stmt_result;
mod compile_compound_fact;
mod compile_compound_stores;
mod compile_def_prop_stmt_result;
mod compile_def_thm_stmt_result;
mod compile_define_obj_stmt_result;
mod compile_definition_stmt_result;
mod compile_division_inference;
mod compile_equality_inferences;
mod compile_fact_stmt_result;
mod compile_function_template;
mod compile_have_fn_by_induc_result;
mod compile_have_fn_equal_stmt_result;
mod compile_have_obj_by_exist_facts_result;
mod compile_have_obj_equal_stmt_result;
mod compile_have_obj_in_nonempty_set_stmt_result;
mod compile_inferred_obj;
mod compile_known_application;
mod compile_let_stmt_result;
mod compile_nonzero_factor_inference;
mod compile_obtain_constructor;
mod compile_obtain_obj_from_atomic_fact_stmt_result;
mod compile_obtain_obj_from_exist_fact_stmt_result;
mod compile_order_bound_inferences;
mod compile_positive_power_inference;
mod compile_prop_clause_instance;
mod compile_recursive_unfold_result;
mod compile_release_and_expand_result;
mod compile_run;
mod compile_stmt_result;
mod compile_store_result;
mod compile_subtractive_inference;
mod compile_witness_stmt_result;
mod helper;
mod lean_compile_error;
mod litex_to_lean_compiler;
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
