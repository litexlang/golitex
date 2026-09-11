use std::path::PathBuf;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PipelineError {
    InvalidArguments(String),
    Io { path: PathBuf, message: String },
    Unsupported(String),
    Invariant(String),
}

pub type PipelineResult<T> = Result<T, PipelineError>;
