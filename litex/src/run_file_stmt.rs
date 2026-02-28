use std::fmt;

pub struct RunFileStmt {
    pub file_path: String,
    pub line: u32,
    pub file_index: usize,
}

impl RunFileStmt {
    pub fn new(file_path: &str, line: u32, file_index: usize) -> Self {
        RunFileStmt { file_path: file_path.to_string(), line, file_index }
    }
}

impl fmt::Display for RunFileStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.file_path)
    }
}