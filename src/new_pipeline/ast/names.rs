//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String names, FactId, LineFile; Identifier atoms carry IdentifierId.

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtomicName {
    WithoutMod(String),
    WithMod(String, String),
}

pub type PropName = String;
