//! Framework AST fact shapes.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: prop/predicate names as AtomicName; FactId; SourceLine.
//! Plain objs inside facts use IdentifierId (see `identifier_identity.md`).
//!
//! Layout: `Fact` is the root enum; each Fact variant payload lives in its own file.
//! `AtomicFact` and all atomic payloads stay together in `atomic.rs`.

mod and_fact;
mod atomic;
mod chain_fact;
mod exist_fact;
mod fact;
mod forall_fact;
mod forall_fact_with_iff;
mod helper;
mod not_forall_fact;
mod or_fact;

pub use and_fact::*;
pub use atomic::*;
pub use chain_fact::*;
pub use exist_fact::*;
pub use fact::Fact;
pub use forall_fact::*;
pub use forall_fact_with_iff::*;
pub use helper::*;
pub use not_forall_fact::*;
pub use or_fact::*;
