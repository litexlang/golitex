//! Obj / Fact / Stmt internal representation and display strings.
//!
//! Internal strings use ordinary Litex surface spelling. The only unusual part
//! is tagging each identifier with its IdentifierId as `#<id>#name` (and
//! `Mod::#<id>#name` for module-qualified names). `display_string` is that
//! string with those tags stripped. See README.md in this directory for why
//! the id tag exists (binding identity, exact cache keys, readable user output).

pub mod fact;
pub mod helper;
pub mod obj;
pub mod param;
pub mod stmt;

pub use helper::strip_identifier_id_tags;
