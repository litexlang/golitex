use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::result::NonErrStmtExecResult;
use std::fmt;

pub fn duplicate_used_name_error_message(name: &str) -> String {
    format!(
        "name `{}` is already used, cannot be used again for other definitions",
        name
    )
}

fn body_with_previous(message: &str, previous_error: &Option<Box<RuntimeError>>) -> String {
    match previous_error {
        Some(previous_error) => format!("{}\n\n{}", message, previous_error.error_body()),
        None => message.to_string(),
    }
}

fn boxed_previous_error(previous_error: Option<RuntimeError>) -> Option<Box<RuntimeError>> {
    previous_error.map(Box::new)
}

#[derive(Debug)]
pub enum RuntimeError {
    ArithmeticError(ArithmeticError),
    NewAtomicFactError(NewAtomicFactError),
    StoreFactError(StoreFactError),
    ParseBlockError(ParseBlockError),
    ParsingError(ParsingError),
    ExecError(ExecStmtError),
    UnknownError(UnknownError),
    WellDefinedError(WellDefinedError),
    VerifyError(VerifyError),
    VerifyUnknownError(VerifyUnknownError),
    InferError(InferError),
}

impl std::error::Error for RuntimeError {}

impl RuntimeError {
    pub fn line_file(&self) -> (usize, usize) {
        match self {
            RuntimeError::ArithmeticError(_) => DEFAULT_LINE_FILE.clone(),
            RuntimeError::NewAtomicFactError(_) => DEFAULT_LINE_FILE.clone(),
            RuntimeError::StoreFactError(_) => DEFAULT_LINE_FILE.clone(),
            RuntimeError::ParseBlockError(e) => e.line_file(),
            RuntimeError::ParsingError(e) => e.line_file,
            RuntimeError::ExecError(e) => e.line_file,
            RuntimeError::UnknownError(e) => e.line_file,
            RuntimeError::WellDefinedError(e) => e.line_file,
            RuntimeError::VerifyError(e) => e.line_file,
            RuntimeError::VerifyUnknownError(e) => e.line_file,
            RuntimeError::InferError(e) => e.line_file,
        }
    }

    /// Short label for display (e.g. "ExecError", "UnknownError").
    pub fn display_label(&self) -> &'static str {
        match self {
            RuntimeError::ArithmeticError(_) => "ArithmeticError",
            RuntimeError::NewAtomicFactError(_) => "NewAtomicFactError",
            RuntimeError::StoreFactError(_) => "StoreFactError",
            RuntimeError::ParseBlockError(_) => "ParseBlockError",
            RuntimeError::ParsingError(_) => "ParsingError",
            RuntimeError::ExecError(_) => "ExecError",
            RuntimeError::UnknownError(_) => "UnknownError",
            RuntimeError::WellDefinedError(_) => "WellDefinedError",
            RuntimeError::VerifyError(_) => "VerifyError",
            RuntimeError::VerifyUnknownError(_) => "VerifyUnknownError",
            RuntimeError::InferError(_) => "InferError",
        }
    }

    /// Error content only (no type label). Formatting with location is done by RuntimeContext::display_error.
    pub fn error_body(&self) -> String {
        match self {
            RuntimeError::ArithmeticError(e) => e.body_string(),
            RuntimeError::NewAtomicFactError(e) => e.body_string(),
            RuntimeError::StoreFactError(e) => e.body_string(),
            RuntimeError::ParseBlockError(e) => parse_block_error_message(e),
            RuntimeError::ParsingError(e) => e.body_string(),
            RuntimeError::ExecError(e) => e.body_string(),
            RuntimeError::UnknownError(e) => e.body_string(),
            RuntimeError::WellDefinedError(e) => e.body_string(),
            RuntimeError::VerifyError(e) => e.body_string(),
            RuntimeError::VerifyUnknownError(e) => e.body_string(),
            RuntimeError::InferError(e) => e.body_string(),
        }
    }
}

fn parse_block_error_message(e: &ParseBlockError) -> String {
    match e {
        ParseBlockError::ExpectedIndent(_, _) => "expected indent".to_string(),
        ParseBlockError::UnexpectedIndent(_, _) => "unexpected indent".to_string(),
        ParseBlockError::InconsistentIndent(_, _) => "inconsistent indent".to_string(),
        ParseBlockError::MissingBody(_, _) => "block header missing body".to_string(),
        ParseBlockError::NameAlreadyUsed(name) => {
            format!("{}", duplicate_used_name_error_message(name))
        }
        ParseBlockError::InvalidName(msg) => msg.clone(),
    }
}

// Display outputs body only (no type label); full format with label and line is via RuntimeContext::display_error.
impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.error_body())
    }
}

#[derive(Debug)]
pub struct ArithmeticError {
    pub msg: String,
    pub previous_error: Option<Box<RuntimeError>>,
}

impl ArithmeticError {
    pub fn new(msg: String, previous_error: Option<RuntimeError>) -> Self {
        ArithmeticError {
            msg,
            previous_error: boxed_previous_error(previous_error),
        }
    }

    pub fn body_string(&self) -> String {
        body_with_previous(&self.msg, &self.previous_error)
    }
}

impl fmt::Display for ArithmeticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl From<ArithmeticError> for RuntimeError {
    fn from(e: ArithmeticError) -> Self {
        RuntimeError::ArithmeticError(e)
    }
}

#[derive(Debug)]
pub struct NewAtomicFactError {
    pub msg: String,
    pub previous_error: Option<Box<RuntimeError>>,
}

impl std::error::Error for NewAtomicFactError {}

impl fmt::Display for NewAtomicFactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl NewAtomicFactError {
    pub fn new(msg: String, previous_error: Option<RuntimeError>) -> Self {
        NewAtomicFactError {
            msg,
            previous_error: boxed_previous_error(previous_error),
        }
    }

    pub fn body_string(&self) -> String {
        body_with_previous(&self.msg, &self.previous_error)
    }
}

impl From<NewAtomicFactError> for RuntimeError {
    fn from(e: NewAtomicFactError) -> Self {
        RuntimeError::NewAtomicFactError(e)
    }
}

impl From<NewAtomicFactError> for StoreFactError {
    fn from(e: NewAtomicFactError) -> Self {
        let msg = e.msg.clone();
        StoreFactError::new(msg, Some(e.into()))
    }
}

impl From<NewAtomicFactError> for WellDefinedError {
    fn from(e: NewAtomicFactError) -> Self {
        let msg = e.msg.clone();
        WellDefinedError::new(msg, Some(e.into()), DEFAULT_LINE_FILE.clone())
    }
}

#[derive(Debug)]
pub struct StoreFactError {
    pub msg: String,
    pub previous_error: Option<Box<RuntimeError>>,
}

impl std::error::Error for StoreFactError {}

impl fmt::Display for StoreFactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl StoreFactError {
    pub fn new(msg: String, previous_error: Option<RuntimeError>) -> Self {
        StoreFactError {
            msg,
            previous_error: boxed_previous_error(previous_error),
        }
    }

    /// Content only (msg + previous_error bodies), for embedding in other errors.
    pub fn body_string(&self) -> String {
        body_with_previous(&self.msg, &self.previous_error)
    }
}

impl From<StoreFactError> for RuntimeError {
    fn from(e: StoreFactError) -> Self {
        RuntimeError::StoreFactError(e)
    }
}

impl From<StoreFactError> for ExecStmtError {
    fn from(e: StoreFactError) -> Self {
        let body = e.body_string();
        ExecStmtError::new(
            "".to_string(),
            body,
            Some(e.into()),
            vec![],
            DEFAULT_LINE_FILE.clone(),
        )
    }
}

#[derive(Debug)]
pub enum ParseBlockError {
    ExpectedIndent(usize, usize),
    UnexpectedIndent(usize, usize),
    InconsistentIndent(usize, usize),
    MissingBody(usize, usize),
    NameAlreadyUsed(String),
    InvalidName(String),
}

impl std::error::Error for ParseBlockError {}

impl fmt::Display for ParseBlockError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", parse_block_error_message(self))
    }
}

impl ParseBlockError {
    pub fn line_file(&self) -> (usize, usize) {
        match self {
            ParseBlockError::ExpectedIndent(line, file) => (*line, *file),
            ParseBlockError::UnexpectedIndent(line, file) => (*line, *file),
            ParseBlockError::InconsistentIndent(line, file) => (*line, *file),
            ParseBlockError::MissingBody(line, file) => (*line, *file),
            ParseBlockError::NameAlreadyUsed(_) => DEFAULT_LINE_FILE.clone(),
            ParseBlockError::InvalidName(_) => DEFAULT_LINE_FILE.clone(),
        }
    }
}

impl From<ParseBlockError> for RuntimeError {
    fn from(e: ParseBlockError) -> Self {
        RuntimeError::ParseBlockError(e)
    }
}

#[derive(Debug)]
pub struct ParsingError {
    pub msg: String,
    pub line_file: (usize, usize),
    pub previous_error: Option<Box<RuntimeError>>,
}

impl std::error::Error for ParsingError {}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl ParsingError {
    pub fn new(
        msg: String,
        line_file: (usize, usize),
        previous_error: Option<RuntimeError>,
    ) -> Self {
        ParsingError {
            msg,
            line_file,
            previous_error: boxed_previous_error(previous_error),
        }
    }

    pub fn body_string(&self) -> String {
        body_with_previous(&self.msg, &self.previous_error)
    }
}

impl From<ParsingError> for RuntimeError {
    fn from(e: ParsingError) -> Self {
        RuntimeError::ParsingError(e)
    }
}

#[derive(Debug)]
pub struct ExecStmtError {
    pub stmt_type_name: String,
    pub msg: String,
    pub previous_error: Option<Box<RuntimeError>>,
    pub inside_results: Vec<NonErrStmtExecResult>,
    pub line_file: (usize, usize),
}

impl std::error::Error for ExecStmtError {}

impl fmt::Display for ExecStmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n\n{}", self.stmt_type_name, self.body_string())
    }
}

impl ExecStmtError {
    pub fn new(
        stmt_type_name: String,
        msg: String,
        previous_error: Option<RuntimeError>,
        inside_results: Vec<NonErrStmtExecResult>,
        line_file: (usize, usize),
    ) -> Self {
        ExecStmtError {
            stmt_type_name,
            msg,
            previous_error: boxed_previous_error(previous_error),
            inside_results,
            line_file,
        }
    }

    /// Content only (msg + previous_error bodies), for embedding in other errors.
    pub fn body_string(&self) -> String {
        let body = body_with_previous(&self.msg, &self.previous_error);
        let mut main_body = if self.stmt_type_name.is_empty() {
            body
        } else {
            format!("stmt type: {}\n\n{}", self.stmt_type_name, body)
        };
        if !self.inside_results.is_empty() {
            let mut inside_body_lines: Vec<String> = Vec::new();
            for inside_result in self.inside_results.iter() {
                inside_body_lines.push(inside_result.body_string());
            }
            main_body = format!(
                "{}\n\nstatements completed before this error:\n{}",
                main_body,
                inside_body_lines.join("\n---\n")
            );
        }
        main_body
    }
}

impl From<ExecStmtError> for RuntimeError {
    fn from(e: ExecStmtError) -> Self {
        RuntimeError::ExecError(e)
    }
}

#[derive(Debug)]
pub struct WellDefinedError {
    pub msg: String,
    pub previous_error: Option<Box<RuntimeError>>,
    pub line_file: (usize, usize),
}

impl std::error::Error for WellDefinedError {}

impl fmt::Display for WellDefinedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl WellDefinedError {
    pub fn new(
        msg: String,
        previous_error: Option<RuntimeError>,
        line_file: (usize, usize),
    ) -> Self {
        WellDefinedError {
            msg,
            previous_error: boxed_previous_error(previous_error),
            line_file,
        }
    }

    pub fn body_string(&self) -> String {
        body_with_previous(&self.msg, &self.previous_error)
    }
}

impl From<WellDefinedError> for RuntimeError {
    fn from(e: WellDefinedError) -> Self {
        RuntimeError::WellDefinedError(e)
    }
}

impl From<WellDefinedError> for ExecStmtError {
    fn from(e: WellDefinedError) -> Self {
        let line_file = e.line_file;
        ExecStmtError::new(
            "".to_string(),
            "fact/object is not well-defined:".to_string(),
            Some(RuntimeError::WellDefinedError(e)),
            vec![],
            line_file,
        )
    }
}

#[derive(Debug)]
pub struct VerifyError {
    pub msg: String,
    pub previous_error: Option<Box<RuntimeError>>,
    pub line_file: (usize, usize),
}

impl std::error::Error for VerifyError {}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl VerifyError {
    pub fn new(
        msg: String,
        previous_error: Option<RuntimeError>,
        line_file: (usize, usize),
    ) -> Self {
        VerifyError {
            msg,
            previous_error: boxed_previous_error(previous_error),
            line_file,
        }
    }

    pub fn body_string(&self) -> String {
        body_with_previous(&self.msg, &self.previous_error)
    }
}

impl From<VerifyError> for RuntimeError {
    fn from(e: VerifyError) -> Self {
        RuntimeError::VerifyError(e)
    }
}

impl From<VerifyError> for ExecStmtError {
    fn from(e: VerifyError) -> Self {
        let line_file = e.line_file;
        ExecStmtError::new(
            "".to_string(),
            "verify fact error:".to_string(),
            Some(RuntimeError::VerifyError(e)),
            vec![],
            line_file,
        )
    }
}

impl From<VerifyError> for WellDefinedError {
    fn from(e: VerifyError) -> Self {
        let line_file = e.line_file;
        WellDefinedError::new(
            "verify fact error:".to_string(),
            Some(RuntimeError::VerifyError(e)),
            line_file,
        )
    }
}

#[derive(Debug)]
pub struct VerifyUnknownError {
    pub msg: String,
    pub previous_error: Option<Box<RuntimeError>>,
    pub line_file: (usize, usize),
}

impl std::error::Error for VerifyUnknownError {}

impl fmt::Display for VerifyUnknownError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl VerifyUnknownError {
    pub fn new(
        msg: String,
        previous_error: Option<RuntimeError>,
        line_file: (usize, usize),
    ) -> Self {
        VerifyUnknownError {
            msg,
            previous_error: boxed_previous_error(previous_error),
            line_file,
        }
    }

    pub fn body_string(&self) -> String {
        body_with_previous(&self.msg, &self.previous_error)
    }
}

impl From<VerifyUnknownError> for RuntimeError {
    fn from(e: VerifyUnknownError) -> Self {
        RuntimeError::VerifyUnknownError(e)
    }
}

impl From<VerifyUnknownError> for VerifyError {
    fn from(e: VerifyUnknownError) -> Self {
        let line_file = e.line_file;
        VerifyError::new(
            "verify result is unknown:".to_string(),
            Some(RuntimeError::VerifyUnknownError(e)),
            line_file,
        )
    }
}

#[derive(Debug)]
pub struct UnknownError {
    pub msg: String,
    pub line_file: (usize, usize),
    pub previous_error: Option<Box<RuntimeError>>,
}

impl std::error::Error for UnknownError {}

impl fmt::Display for UnknownError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl UnknownError {
    pub fn new(
        msg: String,
        line_file: (usize, usize),
        previous_error: Option<RuntimeError>,
    ) -> Self {
        UnknownError {
            msg,
            line_file,
            previous_error: boxed_previous_error(previous_error),
        }
    }

    pub fn body_string(&self) -> String {
        body_with_previous(&self.msg, &self.previous_error)
    }
}

impl From<UnknownError> for RuntimeError {
    fn from(e: UnknownError) -> Self {
        RuntimeError::UnknownError(e)
    }
}

#[derive(Debug)]
pub struct InferError {
    pub msg: String,
    pub line_file: (usize, usize),
    pub previous_error: Option<Box<RuntimeError>>,
}

impl std::error::Error for InferError {}

impl fmt::Display for InferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl InferError {
    pub fn new(
        msg: String,
        line_file: (usize, usize),
        previous_error: Option<RuntimeError>,
    ) -> Self {
        InferError {
            msg,
            line_file,
            previous_error: boxed_previous_error(previous_error),
        }
    }

    pub fn body_string(&self) -> String {
        body_with_previous(&self.msg, &self.previous_error)
    }
}

impl From<InferError> for RuntimeError {
    fn from(e: InferError) -> Self {
        RuntimeError::InferError(e)
    }
}

impl From<InferError> for ExecStmtError {
    fn from(e: InferError) -> Self {
        let msg = e.body_string();
        ExecStmtError::new(
            "".to_string(),
            msg,
            Some(e.into()),
            vec![],
            DEFAULT_LINE_FILE.clone(),
        )
    }
}
