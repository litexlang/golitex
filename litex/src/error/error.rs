use std::fmt;
use crate::common::defaults::DEFAULT_LINE_FILE;

fn body_with_previous(message: &str, previous_error: &Option<Box<StmtError>>) -> String {
    match previous_error {
        Some(previous_error) => format!("{}\n{}", message, previous_error.error_body()),
        None => message.to_string(),
    }
}

fn boxed_previous_error(previous_error: Option<StmtError>) -> Option<Box<StmtError>> {
    previous_error.map(Box::new)
}

#[derive(Debug)]
pub enum StmtError {
    ArithmeticError(ArithmeticError),
    NewAtomicFactError(NewAtomicFactError),
    StoreFactError(StoreFactError),
    ParseBlockError(ParseBlockError),
    ParsingError(ParsingError),
    ExecError(ExecError),
    UnknownError(UnknownError),
    WellDefinedError(WellDefinedError),
    VerifyError(VerifyError),
    InferError(InferError),
}


impl std::error::Error for StmtError {}

impl StmtError {
    pub fn line_file(&self) -> (usize, usize) {
        match self {
            StmtError::ArithmeticError(_) => DEFAULT_LINE_FILE.clone(),
            StmtError::NewAtomicFactError(_) => DEFAULT_LINE_FILE.clone(),
            StmtError::StoreFactError(_) => DEFAULT_LINE_FILE.clone(),
            StmtError::ParseBlockError(e) => e.line_file(),
            StmtError::ParsingError(e) => e.line_file,
            StmtError::ExecError(e) => e.line_file,
            StmtError::UnknownError(e) => e.line_file,
            StmtError::WellDefinedError(e) => e.line_file,
            StmtError::VerifyError(e) => e.line_file,
            StmtError::InferError(e) => e.line_file,
        }
    }

    /// Short label for display (e.g. "ExecError", "UnknownError").
    pub fn display_label(&self) -> &'static str {
        match self {
            StmtError::ArithmeticError(_) => "ArithmeticError",
            StmtError::NewAtomicFactError(_) => "NewAtomicFactError",
            StmtError::StoreFactError(_) => "StoreFactError",
            StmtError::ParseBlockError(_) => "ParseBlockError",
            StmtError::ParsingError(_) => "ParsingError",
            StmtError::ExecError(_) => "ExecError",
            StmtError::UnknownError(_) => "UnknownError",
            StmtError::WellDefinedError(_) => "WellDefinedError",
            StmtError::VerifyError(_) => "VerifyError",
            StmtError::InferError(_) => "InferError",
        }
    }

    /// Error content only (no type label). Formatting with location is done by RuntimeContext::display_error.
    pub fn error_body(&self) -> String {
        match self {
            StmtError::ArithmeticError(e) => e.body_string(),
            StmtError::NewAtomicFactError(e) => e.body_string(),
            StmtError::StoreFactError(e) => e.body_string(),
            StmtError::ParseBlockError(e) => parse_block_error_message(e),
            StmtError::ParsingError(e) => e.body_string(),
            StmtError::ExecError(e) => e.body_string(),
            StmtError::UnknownError(e) => e.body_string(),
            StmtError::WellDefinedError(e) => e.body_string(),
            StmtError::VerifyError(e) => e.body_string(),
            StmtError::InferError(e) => e.body_string(),
        }
    }
}

fn parse_block_error_message(e: &ParseBlockError) -> String {
    match e {
        ParseBlockError::ExpectedIndent(_, _) => "expected indent".to_string(),
        ParseBlockError::UnexpectedIndent(_, _) => "unexpected indent".to_string(),
        ParseBlockError::InconsistentIndent(_, _) => "inconsistent indent".to_string(),
        ParseBlockError::MissingBody(_, _) => "block header missing body".to_string(),
        ParseBlockError::NameAlreadyUsed(name) => format!("name {} is already used", name),
        ParseBlockError::InvalidName(msg) => msg.clone(),
    }
}

// Display outputs body only (no type label); full format with label and line is via RuntimeContext::display_error.
impl fmt::Display for StmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.error_body())
    }
}


#[derive(Debug)]
pub struct ArithmeticError{
    pub msg: String,
    pub previous_error: Option<Box<StmtError>>,
}


impl ArithmeticError {
    pub fn new(msg: String, previous_error: Option<StmtError>) -> Self {
        ArithmeticError { msg, previous_error: boxed_previous_error(previous_error) }
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

impl From<ArithmeticError> for StmtError {
    fn from(e: ArithmeticError) -> Self {
        StmtError::ArithmeticError(e)
    }
}

#[derive(Debug)]
pub struct NewAtomicFactError {
    pub msg: String,
    pub previous_error: Option<Box<StmtError>>,
}

impl std::error::Error for NewAtomicFactError {}

impl fmt::Display for NewAtomicFactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl NewAtomicFactError {
    pub fn new(msg: String, previous_error: Option<StmtError>) -> Self {
        NewAtomicFactError { msg, previous_error: boxed_previous_error(previous_error) }
    }

    pub fn body_string(&self) -> String {
        body_with_previous(&self.msg, &self.previous_error)
    }
}

impl From<NewAtomicFactError> for StmtError {
    fn from(e: NewAtomicFactError) -> Self {
        StmtError::NewAtomicFactError(e)
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
    pub previous_error: Option<Box<StmtError>>,
}

impl std::error::Error for StoreFactError {}

impl fmt::Display for StoreFactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl StoreFactError {
    pub fn new(msg: String, previous_error: Option<StmtError>) -> Self {
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

impl From<StoreFactError> for StmtError {
    fn from(e: StoreFactError) -> Self {
        StmtError::StoreFactError(e)
    }
}

impl From<StoreFactError> for ExecError {
    fn from(e: StoreFactError) -> Self {
        let body = e.body_string();
        ExecError::new("".to_string(), body, Some(e.into()), DEFAULT_LINE_FILE.clone())
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


impl From<ParseBlockError> for StmtError {
    fn from(e: ParseBlockError) -> Self {
        StmtError::ParseBlockError(e)
    }
}

#[derive(Debug)]
pub struct ParsingError {
    pub msg: String,
    pub line_file: (usize, usize),
    pub previous_error: Option<Box<StmtError>>,
}

impl std::error::Error for ParsingError {}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl ParsingError {
    pub fn new(msg: String, line_file: (usize, usize), previous_error: Option<StmtError>) -> Self {
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

impl From<ParsingError> for StmtError {
    fn from(e: ParsingError) -> Self {
        StmtError::ParsingError(e)
    }
}


#[derive(Debug)]
pub struct ExecError {
    pub stmt_type_name: String,
    pub msg: String,
    pub previous_error: Option<Box<StmtError>>,
    pub line_file: (usize, usize),
}

impl std::error::Error for ExecError {}

impl fmt::Display for ExecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}", self.stmt_type_name, self.body_string())
    }
}

impl ExecError {
    pub fn new(stmt_type_name: String, msg: String, previous_error: Option<StmtError>, line_file: (usize, usize)) -> Self {
        ExecError {
            stmt_type_name,
            msg,
            previous_error: boxed_previous_error(previous_error),
            line_file,
        }
    }

    /// Content only (msg + previous_error bodies), for embedding in other errors.
    pub fn body_string(&self) -> String {
        let body = body_with_previous(&self.msg, &self.previous_error);
        if self.stmt_type_name.is_empty() {
            body
        } else {
            format!("stmt type: {}\n{}", self.stmt_type_name, body)
        }
    }
}

impl From<ExecError> for StmtError {
    fn from(e: ExecError) -> Self {
        StmtError::ExecError(e)
    }
}

#[derive(Debug)]
pub struct WellDefinedError {
    pub msg: String,
    pub previous_error: Option<Box<StmtError>>,
    pub line_file: (usize, usize),
}

impl std::error::Error for WellDefinedError {}

impl fmt::Display for WellDefinedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl WellDefinedError {
    pub fn new(msg: String, previous_error: Option<StmtError>, line_file: (usize, usize)) -> Self {
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

impl From<WellDefinedError> for StmtError {
    fn from(e: WellDefinedError) -> Self {
        StmtError::WellDefinedError(e)
    }
}

impl From<WellDefinedError> for ExecError {
    fn from(e: WellDefinedError) -> Self {
        let body = "well defined error: ".to_string() + &e.body_string();
        ExecError::new("".to_string(), body, Some(e.into()), DEFAULT_LINE_FILE.clone())
    }
}

#[derive(Debug)]
pub struct VerifyError {
    pub msg: String,
    pub previous_error: Option<Box<StmtError>>,
    pub line_file: (usize, usize),
}

impl std::error::Error for VerifyError {}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl VerifyError {
    pub fn new(msg: String, previous_error: Option<StmtError>, line_file: (usize, usize)) -> Self {
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

impl From<VerifyError> for StmtError {
    fn from(e: VerifyError) -> Self {
        StmtError::VerifyError(e)
    }
}

impl From<VerifyError> for ExecError {
    fn from(e: VerifyError) -> Self {
        let body = "verify fact error: ".to_string() + &e.body_string();
        ExecError::new("".to_string(), body, Some(e.into()), DEFAULT_LINE_FILE.clone())
    }
}

impl From<VerifyError> for WellDefinedError {
    fn from(e: VerifyError) -> Self {
        let body = "verify fact error: ".to_string() + &e.body_string();
        WellDefinedError::new(body, Some(e.into()), DEFAULT_LINE_FILE.clone())
    }
}

#[derive(Debug)]
pub struct UnknownError {
    pub msg: String,
    pub line_file: (usize, usize),
    pub previous_error: Option<Box<StmtError>>,
}

impl std::error::Error for UnknownError {}

impl fmt::Display for UnknownError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl UnknownError {
    pub fn new(msg: String, line_file: (usize, usize), previous_error: Option<StmtError>) -> Self {
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

impl From<UnknownError> for StmtError {
    fn from(e: UnknownError) -> Self {
        StmtError::UnknownError(e)
    }
}


#[derive(Debug)]
pub struct InferError {
    pub msg: String,
    pub line_file: (usize, usize),
    pub previous_error: Option<Box<StmtError>>,
}

impl std::error::Error for InferError {}

impl fmt::Display for InferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl InferError {
    pub fn new(msg: String, line_file: (usize, usize), previous_error: Option<StmtError>) -> Self {
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

impl From<InferError> for StmtError {
    fn from(e: InferError) -> Self {
        StmtError::InferError(e)
    }
}

impl From<InferError> for ExecError {
    fn from(e: InferError) -> Self {
        let msg = e.body_string();
        ExecError::new("".to_string(), msg, Some(e.into()), DEFAULT_LINE_FILE.clone())
    }
}