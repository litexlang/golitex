use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ImportStmt {
    ImportRelativePath(ImportRelativePathStmt),
    ImportGlobalModule(ImportGlobalModuleStmt),
}

#[derive(Clone)]
pub struct ImportRelativePathStmt {
    pub path: String,
    pub as_mod_name: Option<String>,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct ImportGlobalModuleStmt {
    pub mod_name: String,
    pub as_mod_name: Option<String>,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct RunFileStmt {
    pub file_path: String,
    pub line_file: (usize, usize),
}

impl RunFileStmt {
    pub fn new(file_path: String, line_file: (usize, usize)) -> Self {
        RunFileStmt {
            file_path,
            line_file,
        }
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
            ImportStmt::ImportRelativePath(import_relative_path) => {
                write!(f, "{}", import_relative_path)
            }
            ImportStmt::ImportGlobalModule(import_global_mod) => write!(f, "{}", import_global_mod),
        }
    }
}

impl ImportRelativePathStmt {
    pub fn new(path: String, as_mod_name: Option<String>, line_file: (usize, usize)) -> Self {
        ImportRelativePathStmt {
            path,
            as_mod_name,
            line_file,
        }
    }
}

impl ImportGlobalModuleStmt {
    pub fn new(mod_name: String, as_mod_name: Option<String>, line_file: (usize, usize)) -> Self {
        ImportGlobalModuleStmt {
            mod_name,
            as_mod_name,
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
        match &self.as_mod_name {
            Some(name) => write!(f, "{} {} {} {}", IMPORT, self.mod_name, AS, name),
            None => write!(f, "{} {}", IMPORT, self.mod_name),
        }
    }
}

impl ImportStmt {
    pub fn line_file(&self) -> (usize, usize) {
        match self {
            ImportStmt::ImportRelativePath(import_relative_path) => import_relative_path.line_file,
            ImportStmt::ImportGlobalModule(import_global_mod) => import_global_mod.line_file,
        }
    }
}

#[derive(Clone)]
pub struct DoNothingStmt {
    pub line_file: (usize, usize),
}

impl DoNothingStmt {
    pub fn new(line_file: (usize, usize)) -> Self {
        DoNothingStmt { line_file }
    }
}

impl fmt::Display for DoNothingStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", DO_NOTHING)
    }
}
