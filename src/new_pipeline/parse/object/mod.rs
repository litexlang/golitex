//! Object expression parse for new_pipeline (Phase 1).
//!
//! Precedence (low → high): unicode ∪∩×, +-, */%, ..., unary -, ^, postfix, primary.

mod expression;
mod primary;

pub use expression::parse_obj;
pub use primary::{is_atom_name, is_simple_name, parse_obj_list_paren};
