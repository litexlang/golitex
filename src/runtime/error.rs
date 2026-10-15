use super::code_source::CodeSource;
use std::fmt;
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

impl RuntimeError {
    pub fn with_source_context(self, code: &str) -> Self {
        match self {
            Self::ParseError(error) => error.with_line_source(code).into(),
            other => other,
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidArguments(message) => write!(f, "launch_error: {message}"),
            Self::Io { path, message } => write!(f, "io_error: {}: {message}", path.display()),
            Self::ParseError(error) => {
                write!(
                    f,
                    "parse_error: {} at line {} in {}",
                    error.message, error.line, error.path
                )?;
                if let Some(column) = error.source.as_ref().and_then(|source| source.column) {
                    write!(f, " (column {column})")?;
                }
                Ok(())
            }
            Self::Unsupported(message) => write!(f, "unsupported: {message}"),
            Self::InternalBug(message) => write!(f, "internal_bug: Litex internal bug: {message}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimeParseError {
    pub message: String,
    pub line: usize,
    pub path: CodeSource,
    pub source: Option<ParseErrorSource>,
}

/// A captured input line, independent of files changing after parsing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseErrorSource {
    pub text: String,
    /// One-based Unicode scalar column; None for legacy line-only errors.
    pub column: Option<usize>,
    pub label: Option<String>,
}

impl ParseErrorSource {
    pub fn new(text: String, column: Option<usize>) -> Self {
        Self {
            text,
            column,
            label: None,
        }
    }
}

impl RuntimeParseError {
    pub fn new(message: impl Into<String>, line: usize, path: CodeSource) -> Self {
        Self {
            message: message.into(),
            line,
            path,
            source: None,
        }
    }

    pub fn with_source(mut self, code: &str, offset: usize) -> Self {
        if offset > code.len() || !code.is_char_boundary(offset) {
            return self;
        }
        let start = code[..offset].rfind('\n').map_or(0, |index| index + 1);
        let end = code[offset..]
            .find('\n')
            .map_or(code.len(), |index| offset + index);
        self.line = code[..start].bytes().filter(|byte| *byte == b'\n').count() + 1;
        self.source = Some(ParseErrorSource::new(
            code[start..end].trim_end_matches('\r').to_string(),
            Some(code[start..offset].chars().count() + 1),
        ));
        self
    }

    pub fn with_line_source(mut self, code: &str) -> Self {
        if self.source.is_none() {
            if let Some(line) = self
                .line
                .checked_sub(1)
                .and_then(|line| code.lines().nth(line))
            {
                self.source = Some(ParseErrorSource::new(line.to_string(), None));
            }
        }
        self
    }

    /// Terminal presentation; Display remains the machine-readable summary.
    pub fn diagnostic(&self) -> String {
        let mut out = format!(
            "Parse error: {}\n --> {}:{}",
            self.message, self.path, self.line
        );
        if let Some(source) = &self.source {
            if let Some(column) = source.column {
                out.push_str(&format!(":{column}"));
            }
            let gutter = " ".repeat(self.line.to_string().len());
            let text = source.text.replace('\t', "    ");
            out.push_str(&format!("\n{gutter} |\n{} | {text}", self.line));
            if let Some(column) = source.column {
                let prefix: String = source.text.chars().take(column - 1).collect();
                let label = source.label.as_deref().unwrap_or("");
                // Unicode terminal widths depend on the terminal/font. Keep the
                // original prefix when it is non-ASCII instead of guessing widths.
                let padding = if prefix.is_ascii() {
                    prefix
                        .chars()
                        .map(|ch| if ch == '\t' { "    " } else { " " })
                        .collect::<String>()
                } else {
                    prefix.replace('\t', "    ")
                };
                out.push_str(&format!("\n{gutter} | {padding}^"));
                if !label.is_empty() {
                    out.push(' ');
                    out.push_str(label);
                }
            }
        }
        out
    }
}

impl From<RuntimeParseError> for RuntimeError {
    fn from(error: RuntimeParseError) -> Self {
        RuntimeError::ParseError(error)
    }
}
