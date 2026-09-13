pub mod by_builtin_rule_result;
pub mod by_builtin_strategy_result;
pub mod verify_equal_fact;

pub use by_builtin_rule_result::EqualitySearchProofByBuiltinRule;
pub use by_builtin_strategy_result::EqualitySearchProofByBuiltinStrategy;
pub use verify_equal_fact::equal_fact_from_let;
