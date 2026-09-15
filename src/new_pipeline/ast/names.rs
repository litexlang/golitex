//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String names (name is identity); FactId; LineFile.
//!
//! Qualified names: at most three `::` segments (no submodule).
//! `name` | `Mod::name` | `Mod::Export::name`

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtomicName {
    Plain { name: String },
    WithMod { mod_name: String, name: String },
    WithModAndExport {
        mod_name: String,
        export_name: String,
        name: String,
    },
}

pub type PropName = String;

impl AtomicName {
    pub fn display_string(&self) -> String {
        match self {
            AtomicName::Plain { name } => name.clone(),
            AtomicName::WithMod { mod_name, name } => format!("{mod_name}::{name}"),
            AtomicName::WithModAndExport {
                mod_name,
                export_name,
                name,
            } => format!("{mod_name}::{export_name}::{name}"),
        }
    }
}
