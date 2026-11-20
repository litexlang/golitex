//! Object expression parse (Phase 1).
//!
//! Precedence (low → high): unicode ∪∩×, +-, */%, ..., unary -, ^, postfix (`!` / `.` / call / `[i]`), primary.

mod bound_expression;
mod expression;
mod integral;
mod primary;

pub use expression::parse_obj;
pub use primary::{is_atom_name, is_simple_name, parse_obj_list_paren};
