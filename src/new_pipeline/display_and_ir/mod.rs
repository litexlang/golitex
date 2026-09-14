//! Obj / Fact / Stmt IR and display strings.
//!
//! Internal strings use ordinary Litex surface spelling (name is identity).
//! `display_string` currently equals the IR string. See README.md in this
//! directory.

pub mod fact;
pub mod obj;
pub mod param;
pub mod stmt;
pub mod types;

pub use types::{FactIR, ObjIR, ParamIR, StmtIR};
