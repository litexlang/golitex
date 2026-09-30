pub mod by_they_are_the_same;
pub mod result;
pub mod by_builtin_rewrite_result;
pub mod by_builtin_strategy_result;
pub mod helper;
pub mod equivalence_class_graph;
pub mod search_equal_fact_by_closed_numeric_equal_substitution;
pub mod search_equal_fact_by_extremum_equality;
pub mod search_equal_fact_by_finite_set_product_pointwise;
pub mod search_equal_fact_by_mod_congruence;
pub mod search_equal_fact_by_rational_with_nonzero_premises;
pub mod search_equal_fact_proof_by_builtin_rewrite;
pub mod search_equal_fact_proof_by_matching_one_arg_by_one;
pub mod search_equal_fact_proof_by_equivalence_class;
pub mod verify_equal_fact;
pub mod by_object_definition;
pub mod verify_equality_by_builtin_rules;
pub mod verify_well_defined;
pub mod well_defined_result;

pub use by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite;
pub use by_builtin_strategy_result::EqualitySearchProofByBuiltinStrategy;
pub use by_object_definition::EqualitySearchProofByObjectDefinition;
pub use verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;
pub use well_defined_result::{
    EqualFactWellDefinedProof, FailToVerifyEqualFactWellDefinedResult,
    VerifyEqualFactWellDefinedResult,
};

pub use result::{
    EqualFactSearchedProof, EqualFactSearchedProofByEquivalenceClass,
    EqualFactSearchedProofByKnownForallViaSymmetry, SearchProofByKnownForallFact,
    VerifyEqualityFailed, VerifyEqualityResult,
};
pub use search_equal_fact_proof_by_matching_one_arg_by_one::EqualFactSearchedProofByMatchingOneArgByOne;

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/equality_search/tests.rs"]
mod equality_search_tests;
