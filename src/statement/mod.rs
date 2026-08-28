mod commands;
mod conversions;
mod definitions;
mod display;
mod metadata;
mod proof_blocks;
pub mod proof_directives;
mod statement;
mod type_names;

// Compatibility alias retained for one version while embedders migrate.
pub use proof_directives as explicit_verify;

pub use commands::evaluation as eval_stmt;
pub use definitions::algorithm as define_algorithm_stmt;
pub use definitions::axiom as axiom_stmt;
pub use definitions::parameters;
pub use definitions::statement as definition_stmt;
pub use proof_blocks::claim as claim_stmt;
pub use proof_blocks::example as example_stmt;
pub use proof_blocks::sketch as sketch_stmt;
pub use proof_blocks::trust as trust_stmt;
pub use proof_blocks::try_block as try_stmt;
pub use proof_blocks::witness as witness_stmt;

pub use definitions::axiom::AxiomStmt;
pub use definitions::strategy::DefStrategyStmt;
pub use definitions::structure::{DefStructStmt, StructFieldDef};
pub use definitions::theorem::DefThmStmt;
pub use proof_directives::{
    ByClosedRangeAsCasesStmt, ByDefStmt, ByEnumerateRangeStmt, ByStructDefStmt, ByThmStmt,
    ReleaseThmStmt,
};
pub use statement::{
    ByStmt, CommandStmt, DefinitionStmt, ProofBlockStmt, Stmt, UnsafeStmt, WitnessStmt,
};
