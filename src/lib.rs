#![cfg_attr(test, allow(deprecated))]

pub mod api;
pub mod cli;
pub mod compatibility;
// Compatibility alias retained for one version while embedders migrate.
pub use compatibility::common;
pub mod environment;
pub mod error;
pub mod execution;
// Compatibility alias retained for one version while embedders migrate.
pub use execution as execute;
pub mod extract_code_of_other_languages_from_litex;
pub mod fact;
pub mod graph;
pub mod inference;
// Compatibility alias retained for one version while embedders migrate.
pub use inference as infer;
pub mod latex_renderer;
// Compatibility alias retained for one version while embedders migrate.
pub use latex_renderer as to_latex;
#[cfg(test)]
#[path = "../tests/unit/kernel_contracts/mod.rs"]
mod kernel_contracts;
pub mod module_system;
// Compatibility alias retained for one version while embedders migrate.
pub use module_system as module_manager;
pub mod object;
// Compatibility alias retained for one version while embedders migrate.
pub use object as obj;
pub mod output;
pub mod parsing;
// Compatibility alias retained for one version while embedders migrate.
pub use parsing as parse;
pub mod algebraic_normalization;
pub mod pipeline;
pub mod prelude;
// Compatibility alias retained for one version while embedders migrate.
pub use algebraic_normalization as rational_expression;
// Compatibility aliases retained while canonical ownership moves under the
// verified executable-code extraction subsystem.
pub use extract_code_of_other_languages_from_litex::c as c_extractor;
pub use extract_code_of_other_languages_from_litex::c as to_c;
pub use extract_code_of_other_languages_from_litex::python as python_extractor;
pub use extract_code_of_other_languages_from_litex::python as to_python;
pub mod result;
pub mod runner;
pub mod runtime;
pub mod statement;
// Compatibility alias retained for one version while embedders migrate.
pub use statement as stmt;
pub mod stmt_result_to_lean_compiler;
pub mod symbol;
pub mod syntax;
#[cfg(test)]
#[path = "../tests/unit/test_support.rs"]
pub mod test_support;
pub mod verification;
// Compatibility alias retained for one version while embedders migrate.
pub use verification as verify;

// Staged verifier rewrite. The legacy `verify` compatibility alias above and
// the active Runtime execution path remain unchanged until this rewrite has
// completed its Result/pipeline migration.
#[path = "verify/mod.rs"]
pub mod verify_rewrite;
