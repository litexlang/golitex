//! Parsed `litex.config` for new_pipeline (import / export only).

use std::path::PathBuf;

/// One module manifest: imports then exports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LitexConfig {
    pub imports: Vec<LitexConfigImport>,
    pub exports: Vec<LitexConfigExport>,
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
