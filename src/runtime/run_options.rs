use crate::prelude::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunOptions {
    pub output_style: OutputStyle,
    pub strict_mode: bool,
    pub output_language: OutputLanguage,
    pub summarize: bool,
}

impl Default for RunOptions {
    fn default() -> Self {
        Self {
            output_style: OutputStyle::Normal,
            strict_mode: false,
            output_language: OutputLanguage::English,
            summarize: false,
        }
    }
}
