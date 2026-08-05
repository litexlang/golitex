//! Experimental Litex-to-Lean bridge for verified rational equalities.

mod rational_expression;
mod to_lean_pipeline;

pub use to_lean_pipeline::{to_lean, to_lean_from_source};
