use std::fmt;
use crate::consts::{IMPORT, DOUBLE_QUOTE, AS};

pub enum ImportStmt {
    ImportRelativePath(ImportRelativePathStmt),
    ImportGlobalPkg(ImportGlobalPkgStmt),
}

pub struct ImportRelativePathStmt {
    pub path: String,
    pub as_pkg_name: String,
    pub line: u32,
    pub file_index: usize,
}

pub struct ImportGlobalPkgStmt {
    pub pkg: String,
    pub as_pkg_name: String,
    pub line: u32,
    pub file_index: usize,
}

impl fmt::Display for ImportStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ImportStmt::ImportRelativePath(import_relative_path) => write!(f, "{}", import_relative_path),
            ImportStmt::ImportGlobalPkg(import_global_pkg) => write!(f, "{}", import_global_pkg),
        }
    }
}

impl ImportRelativePathStmt {
    pub fn new(path: &str, as_pkg_name: &str, line: u32, file_index: usize) -> Self {
        ImportRelativePathStmt { path: path.to_string(), as_pkg_name: as_pkg_name.to_string(), line, file_index }
    }
}

impl ImportGlobalPkgStmt {
    pub fn new(pkg: &str, as_pkg_name: &str, line: u32, file_index: usize) -> Self {
        ImportGlobalPkgStmt { pkg: pkg.to_string(), as_pkg_name: as_pkg_name.to_string(), line, file_index }
    }
}

impl fmt::Display for ImportRelativePathStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}{} {} {}", IMPORT, DOUBLE_QUOTE, self.path, DOUBLE_QUOTE, AS, self.as_pkg_name)
    }
}

impl fmt::Display for ImportGlobalPkgStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}", IMPORT, self.pkg, AS, self.as_pkg_name)
    }
}

impl ImportStmt {
    pub fn line_file(&self) -> (u32, usize) {
        match self {
            ImportStmt::ImportRelativePath(import_relative_path) => (import_relative_path.line, import_relative_path.file_index),
            ImportStmt::ImportGlobalPkg(import_global_pkg) => (import_global_pkg.line, import_global_pkg.file_index),
        }
    }
}

