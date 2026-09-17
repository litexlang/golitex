pub mod result;
pub mod by_builtin_strategy_result;
pub mod known_equality_graph;
pub mod search_equal_fact_by_rational_with_nonzero_premises;
pub mod search_equal_fact_proof_by_builtin_rewrite;
pub mod search_equal_fact_proof_by_known_rewrite;
pub mod search_equal_fact_proof_by_known_equality;
pub mod verify_equal_fact;
pub mod verify_equality_by_builtin_rules;

pub use by_builtin_strategy_result::EqualitySearchProofByBuiltinStrategy;
pub use search_equal_fact_proof_by_builtin_rewrite::EqualitySearchProofByBuiltinRewrite;
pub use search_equal_fact_proof_by_known_rewrite::EqualitySearchProofByKnownRewrite;
pub use verify_equality_by_builtin_rules::EqualitySearchProofByBuiltinRule;

pub use result::{
    equal_fact_result_from_search_fail, equal_fact_result_from_success,
    equal_fact_result_from_wd_fail, strict_equal_arg_proof_from_searched,
    EqualFactSearchedProof, EqualFactSearchedProofByKnownEquality,
    ForallConclusionArgMatchProof, MatchForallConclusionArgsProof, SearchProofByKnownForallFact,
    StrictEqualArgProof, StrictEqualWithFact, VerifyEqualityFailed, VerifyEqualityResult,
    VerifyEqualitySuccess,
};
