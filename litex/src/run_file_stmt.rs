use std::fmt;

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