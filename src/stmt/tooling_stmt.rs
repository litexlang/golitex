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
pub struct LocalImportStmt {
    pub name: String,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct TrustLocalImportStmt {
    pub local_import: LocalImportStmt,
}

#[derive(Clone)]
pub struct ImportGlobalModuleStmt {
    pub mod_name: String,
    pub line_file: LineFile,
}

impl LocalImportStmt {
    pub fn new(name: String, line_file: LineFile) -> Self {
        LocalImportStmt { name, line_file }
    }
}

impl TrustImportStmt {
    pub fn new(import: ImportStmt) -> Self {
        TrustImportStmt { import }
    }
}

impl TrustLocalImportStmt {
    pub fn new(local_import: LocalImportStmt) -> Self {
        TrustLocalImportStmt { local_import }
    }
}

impl fmt::Display for TrustImportStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", TRUST, self.import)
    }
}

impl fmt::Display for TrustLocalImportStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", TRUST, self.local_import)
    }
}

impl fmt::Display for LocalImportStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {}", LOCAL, IMPORT, self.name)
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
    pub fn new(mod_name: String, line_file: LineFile) -> Self {
        ImportGlobalModuleStmt {
            mod_name,
            line_file,
        }
    }
}

impl fmt::Display for ImportGlobalModuleStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", IMPORT, self.mod_name)
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

impl TrustLocalImportStmt {
    pub fn line_file(&self) -> LineFile {
        self.local_import.line_file.clone()
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
