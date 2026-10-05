pub mod by_have_fn_equal;
pub mod by_both_function_bodies;
pub mod by_have_fn_equal_case_by_case;
pub mod by_have_fn_by_induc;
pub mod by_parent_checked_beta;
pub mod result;

pub use result::EqualitySearchProofByFnApplicationObjectDefinition;

pub mod normalize_function_body;

#[cfg(test)]
#[path = "../../../../../../../tests/unit/execute/function_body_evaluation/tests.rs"]
mod function_body_evaluation_tests;
