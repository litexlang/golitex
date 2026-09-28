use super::real_or_virtual_path::RealOrVirtualPath;
use std::path::PathBuf;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeError {
    InvalidArguments(String),
    Io { path: PathBuf, message: String },
    ParseError(RuntimeParseError),
    Unsupported(String),
    InternalBug(String),
}

pub type RuntimeResult<T> = Result<T, RuntimeError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimeParseError {
    pub message: String,
    pub line: usize,
    pub path: RealOrVirtualPath,
}

impl RuntimeParseError {
    pub fn new(message: impl Into<String>, line: usize, path: RealOrVirtualPath) -> Self {
        Self {
            message: message.into(),
            line,
            path,
        }
    }
}

impl From<RuntimeParseError> for RuntimeError {
    fn from(error: RuntimeParseError) -> Self {
        RuntimeError::ParseError(error)
    }
}
