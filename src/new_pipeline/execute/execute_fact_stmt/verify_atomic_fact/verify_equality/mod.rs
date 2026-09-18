pub mod result;
pub mod by_builtin_rewrite_result;
pub mod by_builtin_strategy_result;
pub mod helper;
pub mod known_equality_graph;
pub mod search_equal_fact_by_closed_numeric_equal_substitution;
pub mod search_equal_fact_by_extremum_equality;
pub mod search_equal_fact_by_finite_set_product_pointwise;
pub mod search_equal_fact_by_mod_congruence;
pub mod search_equal_fact_by_rational_with_nonzero_premises;
pub mod search_equal_fact_proof_by_builtin_rewrite;
pub mod search_equal_fact_proof_by_matching_one_arg_by_one;
pub mod search_equal_fact_proof_by_known_equality;
pub mod verify_equal_fact;
pub mod verify_equality_by_builtin_rules;
pub mod verify_well_defined;
pub mod well_defined_result;

pub use by_builtin_rewrite_result::EqualitySearchProofByBuiltinRewrite;
pub use by_builtin_strategy_result::EqualitySearchProofByBuiltinStrategy;
pub use search_equal_fact_proof_by_matching_one_arg_by_one::EqualFactSearchedProofByMatchingOneArgByOne;
pub use verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;
pub use well_defined_result::{
    EqualFactWellDefinedProof, FailToVerifyEqualFactWellDefinedResult,
    VerifyEqualFactWellDefinedResult,
};

pub use result::{
    equal_fact_result_from_search_fail, equal_fact_result_from_success,
    equal_fact_result_from_wd_fail, strict_equal_arg_proof_from_searched,
    EqualFactSearchedProof, EqualFactSearchedProofByKnownEquality,
    ForallConclusionArgMatchProof, ForallParamTypeRequirementProof,
    MatchForallConclusionArgsProof, ProveForallInstantiationRequirementsProof,
    SearchProofByKnownForallFact, StrictEqualArgProof, StrictEqualWithFact,
    VerifyEqualityFailed, VerifyEqualityResult, VerifyEqualitySuccess,
};
