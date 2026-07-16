use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ImportStmt {
    ImportGlobalModule(ImportGlobalModuleStmt),
}

#[derive(Clone)]
pub struct TrustImportStmt {
    pub import: ImportStmt,
}

#[derive(Clone)]
pub struct ImportGlobalModuleStmt {
    pub mod_name: String,
    pub line_file: LineFile,
}

impl TrustImportStmt {
    pub fn new(import: ImportStmt) -> Self {
        TrustImportStmt { import }
    }
}

impl fmt::Display for TrustImportStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", TRUST, self.import)
    }
}

impl fmt::Display for ImportStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ImportStmt::ImportGlobalModule(import_global_mod) => write!(f, "{}", import_global_mod),
        }
    }
}

impl ImportGlobalModuleStmt {
    pub fn new_std(mod_name: String, line_file: LineFile) -> Self {
        ImportGlobalModuleStmt {
            mod_name,
            line_file,
        }
    }
}

impl fmt::Display for ImportGlobalModuleStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", IMPORT, STD, self.mod_name)
    }
}

impl ImportStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            ImportStmt::ImportGlobalModule(import_global_mod) => {
                import_global_mod.line_file.clone()
            }
        }
    }
}

impl TrustImportStmt {
    pub fn line_file(&self) -> LineFile {
        self.import.line_file()
    }
}

#[derive(Clone)]
pub struct DoNothingStmt {
    pub line_file: LineFile,
}

impl DoNothingStmt {
    pub fn new(line_file: LineFile) -> Self {
        DoNothingStmt { line_file }
    }
}

impl fmt::Display for DoNothingStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", DO_NOTHING)
    }
}

#[derive(Clone)]
pub struct ClearStmt {
    pub line_file: LineFile,
}

impl ClearStmt {
    pub fn new(line_file: LineFile) -> Self {
        ClearStmt { line_file }
    }
}

impl fmt::Display for ClearStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", CLEAR)
    }
}
