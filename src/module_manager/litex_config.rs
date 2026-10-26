//! Parsed `litex.config` imports, exports and namespace aliases.

use std::path::PathBuf;

/// One module manifest: imports then exports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LitexConfig {
    pub imports: Vec<LitexConfigImport>,
    pub exports: Vec<LitexConfigExport>,
    pub aliases: Vec<LitexConfigAlias>,
}

/// One `[alias] name = import_alias::export_name` row; never an alias chain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LitexConfigAlias {
    pub name: String,
    pub import_alias: String,
    pub export_name: String,
}

impl LitexConfigAlias {
    pub fn new(name: String, import_alias: String, export_name: String) -> Self {
        Self {
            name,
            import_alias,
            export_name,
        }
    }
}

/// One `[import]` / `[import std]` row after path resolve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LitexConfigImport {
    pub alias: String,
    pub path: PathBuf,
}

/// One `[export]` row (`.lit` only).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LitexConfigExport {
    pub name: String,
    pub path: PathBuf,
}

impl LitexConfig {
    pub fn new() -> Self {
        Self {
            imports: Vec::new(),
            exports: Vec::new(),
            aliases: Vec::new(),
        }
    }
}

impl LitexConfigImport {
    pub fn new(alias: String, path: PathBuf) -> Self {
        Self { alias, path }
    }
}

impl LitexConfigExport {
    pub fn new(name: String, path: PathBuf) -> Self {
        Self { name, path }
    }
}
