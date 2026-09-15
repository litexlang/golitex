//! Framework AST data shapes for new_pipeline.
//! Field taxonomy follows the legacy language; methods are added later.
//! Identity: String names (name is identity); FactId; LineFile.
//!
//! Qualified names: at most three `::` segments (no submodule).
//! `name` | `Mod::name` | `Mod::Export::name`
//!
//! Definition-side keys and binder-local names are always plain (one segment).

use std::borrow::Borrow;
use std::fmt;

/// Unqualified definition / binder name (`foo`, never `Mod::foo`).
///
/// Tuple newtype: not silently a `String`. Build with `PlainName::new` or `.into()`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PlainName(String);

impl PlainName {
    pub fn new(name: String) -> Self {
        Self(name)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for PlainName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<str> for PlainName {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl Borrow<str> for PlainName {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl From<String> for PlainName {
    fn from(name: String) -> Self {
        Self::new(name)
    }
}

impl From<&str> for PlainName {
    fn from(name: &str) -> Self {
        Self::new(name.to_string())
    }
}

impl PartialEq<str> for PlainName {
    fn eq(&self, other: &str) -> bool {
        self.0 == other
    }
}

impl PartialEq<&str> for PlainName {
    fn eq(&self, other: &&str) -> bool {
        self.0 == *other
    }
}

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
            AtomicName::Plain { name } => name.as_str().to_string(),
            AtomicName::WithMod { mod_name, name } => {
                format!("{}::{}", mod_name.as_str(), name.as_str())
            }
            AtomicName::WithModAndExport {
                mod_name,
                export_name,
                name,
            } => format!(
                "{}::{}::{}",
                mod_name.as_str(),
                export_name.as_str(),
                name.as_str()
            ),
        }
    }
}
