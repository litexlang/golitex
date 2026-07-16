use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ImportStmt {
    Module(ImportModuleStmt),
    Std(ImportStdStmt),
}

#[derive(Clone)]
pub struct ImportModuleStmt {
    pub path: String,
    pub alias: String,
    pub line_file: LineFile,
}

#[derive(Clone)]
pub struct ImportStdStmt {
    pub name: String,
    pub line_file: LineFile,
}

impl ImportModuleStmt {
    pub fn new(path: String, alias: String, line_file: LineFile) -> Self {
        Self {
            path,
            alias,
            line_file,
        }
    }
}

impl ImportStdStmt {
    pub fn new(name: String, line_file: LineFile) -> Self {
        Self { name, line_file }
    }
}

impl ImportStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            Self::Module(stmt) => stmt.line_file.clone(),
            Self::Std(stmt) => stmt.line_file.clone(),
        }
    }
}

impl fmt::Display for ImportStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Module(stmt) => write!(f, "{} \"{}\" {} {}", IMPORT, stmt.path, AS, stmt.alias),
            Self::Std(stmt) => write!(f, "{} {} {}", IMPORT, STD, stmt.name),
        }
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
