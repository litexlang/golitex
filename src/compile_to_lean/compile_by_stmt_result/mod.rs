mod compile_by_cases_stmt_result;
pub(in crate::compile_to_lean) mod compile_by_contra_stmt_result;
mod compile_by_def_stmt_result;
mod compile_by_extension_stmt_result;
mod compile_by_induc_stmt_result;
mod compile_by_stmt_result;
mod compile_by_thm_stmt_result;
pub(in crate::compile_to_lean) mod compile_classified_negation;
mod compile_quantified_closing;
mod compile_quantified_contra;
mod compile_unique_contra;

#[cfg(test)]
mod proof_flow_tests;

pub(in crate::compile_to_lean) mod induction_evidence;

mod compile_by_fn_extension_stmt_result;

mod compile_by_enumeration;
mod compile_enumeration_product;
mod compile_integer_enumeration;
