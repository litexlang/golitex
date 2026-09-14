//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String names (name is identity); FactId; LineFile.

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtomicName {
    WithoutMod(String),
    WithMod(String, String),
}

pub type PropName = String;
