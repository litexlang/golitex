use super::real_or_virtual_path::RealOrVirtualPath;
use std::path::PathBuf;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeError {
    InvalidArguments(String),
    Io { path: PathBuf, message: String },
    ParseError(RuntimeParseError),
    Unsupported(String),
    InternalBug(String),
}

pub type RuntimeResult<T> = Result<T, RuntimeError>;

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidArguments(message) => write!(f, "launch_error: {message}"),
            Self::Io { path, message } => write!(f, "io_error: {}: {message}", path.display()),
            Self::ParseError(error) => write!(
                f, "parse_error: {} at line {} in {}", error.message, error.line, error.path,
            ),
            Self::Unsupported(message) => write!(f, "unsupported: {message}"),
            Self::InternalBug(message) => write!(f, "internal_bug: Litex internal bug: {message}"),
        }
    }
}

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
