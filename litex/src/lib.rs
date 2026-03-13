// Library entry for tests and other crates. Exposes run_source_code to run litex source.

mod verify;
mod simplify_polynomial;
mod common;
mod error;
mod execute;
mod obj;
mod stmt;
mod fact;
mod result;
mod module_manager;
mod runtime_context;
mod environment;
mod parse;
mod pipeline;

pub use pipeline::run_source_code;
