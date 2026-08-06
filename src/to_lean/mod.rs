//! Experimental Litex-to-Lean bridge for verified rational equalities.

mod current_json;
mod rational_expression;
mod to_lean_pipeline;

pub use to_lean_pipeline::{
    to_lean, to_lean_from_source, to_lean_from_statement_json, to_lean_from_statement_jsons,
};
