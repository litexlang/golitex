mod token_block;
mod tokenizer;
pub use token_block::TokenBlock;
pub use tokenizer::Tokenizer;

mod by_stmt;
#[path = "fact/expression.rs"]
mod fact_expression;
#[path = "fact/parameter_definition.rs"]
mod fact_parameter_definition;
mod helper;
#[path = "object/collections.rs"]
mod object_collections;
#[path = "object/expression.rs"]
mod object_expression;
#[path = "object/primary.rs"]
mod object_primary;
#[path = "object/reference.rs"]
mod object_reference;
#[path = "statements/claim.rs"]
mod statement_claim;
#[path = "statements/definition.rs"]
mod statement_definition;
#[path = "statements/evaluation.rs"]
mod statement_evaluation;
#[path = "statements/example.rs"]
mod statement_example;
#[path = "statements/have_function.rs"]
mod statement_have_function;
#[path = "statements/have_object.rs"]
mod statement_have_object;
#[path = "statements/obtain_and_algorithm.rs"]
mod statement_obtain_and_algorithm;
mod statement_parsing;
#[path = "statements/sketch.rs"]
mod statement_sketch;
#[path = "statements/strategy.rs"]
mod statement_strategy;
#[path = "statements/theorem.rs"]
mod statement_theorem;
#[path = "statements/tooling.rs"]
mod statement_tooling;
#[path = "statements/trust_fact.rs"]
mod statement_trust_fact;
#[path = "statements/try_block.rs"]
mod statement_try_block;
#[path = "statements/use_strategy.rs"]
mod statement_use_strategy;
#[path = "statements/witness.rs"]
mod statement_witness;
