//! Litex-to-Lean bridge driven by verifier-produced To-Lean IR.

mod rational_expression;
mod to_lean_pipeline;

pub use to_lean_pipeline::{emit_lean_from_ir, to_lean, to_lean_from_source};
