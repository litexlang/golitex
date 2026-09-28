//! Obj / Fact / Stmt IR and display strings.
//!
//! Plain identifier IR embeds `#id#name`; display uses the surface name.
//! See README.md and `../identifier_identity.md`.

pub mod fact;
pub mod obj;
pub mod param;
pub mod readable;
pub mod stmt;
pub mod types;

pub use readable::readable_string_from_ir_text;
pub use types::{FactIR, ObjIR, ParamIR, StmtIR};
