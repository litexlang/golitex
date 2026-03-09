use std::fmt;
use crate::keywords::{CLEAR, DO_NOTHING, IMPORT, DOUBLE_QUOTE, AS};

pub enum ToolingStmt {
    Import(ImportStmt),
    Clear(ClearStmt),
    DoNothing(DoNothingStmt),
    RunFile(RunFileStmt),
}

pub enum ImportStmt {
    ImportRelativePath(ImportRelativePathStmt),
    ImportGlobalModule(ImportGlobalModuleStmt),
}

pub struct ImportRelativePathStmt {
    pub path: String,
    pub as_mod_name: Option<String>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct ImportGlobalModuleStmt {
    pub mod_name: String,
    pub as_mod_name: Option<String>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct RunFileStmt {
    pub file_path: String,
    pub line_file_index: Option<(usize, usize)>,
}

impl RunFileStmt {
    pub fn new(file_path: &str, line_file_index: Option<(usize, usize)>) -> Self {
        RunFileStmt { file_path: file_path.to_string(), line_file_index }
    }
}

impl fmt::Display for RunFileStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.file_path)
    }
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
    pub fn new(path: &str, as_mod_name: Option<String>, line_file_index: Option<(usize, usize)>) -> Self {
        ImportRelativePathStmt { path: path.to_string(), as_mod_name, line_file_index }
    }
}

impl ImportGlobalModuleStmt {
    pub fn new(mod_name: &str, as_mod_name: Option<String>, line_file_index: Option<(usize, usize)>) -> Self {
        ImportGlobalModuleStmt { mod_name: mod_name.to_string(), as_mod_name, line_file_index }
    }
}

impl fmt::Display for ImportRelativePathStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.as_mod_name {
            Some(name) => write!(f, "{} {}{}{} {} {}", IMPORT, DOUBLE_QUOTE, self.path, DOUBLE_QUOTE, AS, name),
            None => write!(f, "{} {}{}{}", IMPORT, DOUBLE_QUOTE, self.path, DOUBLE_QUOTE),
        }
    }
}

impl fmt::Display for ImportGlobalModuleStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.as_mod_name {
            Some(name) => write!(f, "{} {} {} {}", IMPORT, self.mod_name, AS, name),
            None => write!(f, "{} {}", IMPORT, self.mod_name),
        }
    }
}

impl ImportStmt {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            ImportStmt::ImportRelativePath(import_relative_path) => import_relative_path.line_file_index,
            ImportStmt::ImportGlobalModule(import_global_mod) => import_global_mod.line_file_index,
        }
    }
}

pub struct DoNothingStmt {
    pub line_file_index: Option<(usize, usize)>,
}

pub struct ClearStmt {
    pub line_file_index: Option<(usize, usize)>,
}

impl fmt::Display for ToolingStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ToolingStmt::Import(import_stmt) => write!(f, "{}", import_stmt),
            ToolingStmt::Clear(clear_stmt) => write!(f, "{}", clear_stmt),
            ToolingStmt::DoNothing(do_nothing_stmt) => write!(f, "{}", do_nothing_stmt),
            ToolingStmt::RunFile(run_file_stmt) => write!(f, "{}", run_file_stmt),
        }
    }
}

impl ToolingStmt {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            ToolingStmt::Import(import_stmt) => import_stmt.line_file(),
            ToolingStmt::Clear(clear_stmt) => clear_stmt.line_file_index,
            ToolingStmt::DoNothing(do_nothing_stmt) => do_nothing_stmt.line_file_index,
            ToolingStmt::RunFile(run_file_stmt) => run_file_stmt.line_file_index,
        }
    }
}

impl ClearStmt {
    pub fn new(line_file_index: Option<(usize, usize)>) -> Self {
        ClearStmt { line_file_index }
    }
}

impl fmt::Display for ClearStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", CLEAR)
    }
}

impl DoNothingStmt {
    pub fn new(line_file_index: Option<(usize, usize)>) -> Self {
        DoNothingStmt { line_file_index }
    }
}

impl fmt::Display for DoNothingStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", DO_NOTHING)
    }
}