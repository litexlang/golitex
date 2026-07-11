use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ImportStmt {
    ImportRelativePath(ImportRelativePathStmt),
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
pub struct ImportRelativePathStmt {
    pub path: String,
    pub as_mod_name: Option<String>,
    pub line_file: LineFile,
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
        write!(f, "{} {}", LOCAL_IMPORT, self.name)
    }
}

impl fmt::Display for ImportStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ImportStmt::ImportRelativePath(import_relative_path) => {
                write!(f, "{}", import_relative_path)
            }
            ImportStmt::ImportGlobalModule(import_global_mod) => write!(f, "{}", import_global_mod),
        }
    }
}

impl ImportRelativePathStmt {
    pub fn new(path: String, as_mod_name: Option<String>, line_file: LineFile) -> Self {
        ImportRelativePathStmt {
            path,
            as_mod_name,
            line_file,
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

impl fmt::Display for ImportRelativePathStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.as_mod_name {
            Some(name) => write!(
                f,
                "{} {}{}{} {} {}",
                IMPORT, DOUBLE_QUOTE, self.path, DOUBLE_QUOTE, AS, name
            ),
            None => write!(
                f,
                "{} {}{}{}",
                IMPORT, DOUBLE_QUOTE, self.path, DOUBLE_QUOTE
            ),
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
            ImportStmt::ImportRelativePath(import_relative_path) => {
                import_relative_path.line_file.clone()
            }
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
