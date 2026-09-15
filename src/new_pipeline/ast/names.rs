//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String names (name is identity); FactId; LineFile.
//!
//! Qualified names: at most three `::` segments (no submodule).
//! `name` | `Mod::name` | `Mod::Export::name`
//!
//! Definition-side store keys are unqualified local plain names.
//! Reference / occupy / prop identity uses `AtomicName`.

use std::fmt;

/// Unqualified local name (`foo`, never `Mod::foo`). Alias of `String`.
pub type PlainName = String;

/// Qualified or plain name: at most three `::` segments (no submodule).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AtomicName {
    Plain { name: PlainName },
    WithMod { mod_name: PlainName, name: PlainName },
    WithModAndExport {
        mod_name: PlainName,
        export_name: PlainName,
        name: PlainName,
    },
}

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

    pub fn plain(name: PlainName) -> Self {
        AtomicName::Plain { name }
    }
}

impl fmt::Display for AtomicName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_string())
    }
}
