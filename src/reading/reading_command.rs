use crate::prelude::*;
use std::path::PathBuf;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReadingInput {
    Empty,
    Source(String),
    File(PathBuf),
    Project(PathBuf),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReadingAction {
    Preview { port: u16, open_browser: bool },
    Json,
    Export(PathBuf),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadingCommand {
    pub input: ReadingInput,
    pub action: ReadingAction,
    pub strict: bool,
    pub language: OutputLanguage,
}

impl ReadingCommand {
    pub fn new(
        input: ReadingInput,
        action: ReadingAction,
        strict: bool,
        language: OutputLanguage,
    ) -> Self {
        Self {
            input,
            action,
            strict,
            language,
        }
    }
}
