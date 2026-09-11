use std::path::PathBuf;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeError {
    InvalidArguments(String),
    Io { path: PathBuf, message: String },
    Unsupported(String),
    Invariant(String),
    Unknown(String),
}

pub type RuntimeResult<T> = Result<T, RuntimeError>;
