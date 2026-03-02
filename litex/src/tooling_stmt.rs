use std::fmt;
use crate::consts::{CLEAR, DO_NOTHING, IMPORT, DOUBLE_QUOTE, AS};

pub enum ToolingStmt {
    Import(ImportStmt),
    Clear(ClearStmt),
    DoNothing(DoNothingStmt),
}

pub enum ImportStmt {
    ImportRelativePath(ImportRelativePathStmt),
    ImportGlobalModule(ImportGlobalModuleStmt),
}

pub struct ImportRelativePathStmt {
    pub path: String,
    pub as_mod_name: String,
    pub line: u32,
    pub file_index: usize,
}

pub struct ImportGlobalModuleStmt {
    pub mod_name: String,
    pub as_mod_name: String,
    pub line: u32,
    pub file_index: usize,
}

impl fmt::Display for ImportStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ImportStmt::ImportRelativePath(import_relative_path) => write!(f, "{}", import_relative_path),
            ImportStmt::ImportGlobalModule(import_global_mod) => write!(f, "{}", import_global_mod),
        }
    }
}

impl ImportRelativePathStmt {
    pub fn new(path: &str, as_mod_name: &str, line: u32, file_index: usize) -> Self {
        ImportRelativePathStmt { path: path.to_string(), as_mod_name: as_mod_name.to_string(), line, file_index }
    }
}

impl ImportGlobalModuleStmt {
    pub fn new(mod_name: &str, as_mod_name: &str, line: u32, file_index: usize) -> Self {
        ImportGlobalModuleStmt { mod_name: mod_name.to_string(), as_mod_name: as_mod_name.to_string(), line, file_index }
    }
}

impl fmt::Display for ImportRelativePathStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{} {} {}", IMPORT, DOUBLE_QUOTE, self.path, DOUBLE_QUOTE, AS, self.as_mod_name)
    }
}

impl fmt::Display for ImportGlobalModuleStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", IMPORT, self.mod_name, AS, self.as_mod_name)
    }
}

impl ImportStmt {
    pub fn line_file(&self) -> (u32, usize) {
        match self {
            ImportStmt::ImportRelativePath(import_relative_path) => (import_relative_path.line, import_relative_path.file_index),
            ImportStmt::ImportGlobalModule(import_global_mod) => (import_global_mod.line, import_global_mod.file_index),
        }
    }
}

pub struct DoNothingStmt {
    pub line: u32,
    pub file_index: usize,
}

pub struct ClearStmt {
    pub line: u32,
    pub file_index: usize,
}

impl fmt::Display for ToolingStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ToolingStmt::Import(import_stmt) => write!(f, "{}", import_stmt),
            ToolingStmt::Clear(clear_stmt) => write!(f, "{}", clear_stmt),
            ToolingStmt::DoNothing(do_nothing_stmt) => write!(f, "{}", do_nothing_stmt),
        }
    }
}

impl ToolingStmt {
    pub fn line_file(&self) -> (u32, usize) {
        match self {
            ToolingStmt::Import(import_stmt) => import_stmt.line_file(),
            ToolingStmt::Clear(clear_stmt) => (clear_stmt.line, clear_stmt.file_index),
            ToolingStmt::DoNothing(do_nothing_stmt) => (do_nothing_stmt.line, do_nothing_stmt.file_index),
        }
    }
}

impl ClearStmt {
    pub fn new(line: u32, file_index: usize) -> Self {
        ClearStmt { line, file_index }
    }
}

impl fmt::Display for ClearStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", CLEAR)
    }
}

impl DoNothingStmt {
    pub fn new(line: u32, file_index: usize) -> Self {
        DoNothingStmt { line, file_index }
    }
}

impl fmt::Display for DoNothingStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", DO_NOTHING)
    }
}