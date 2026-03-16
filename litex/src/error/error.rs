use std::fmt;

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
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            StmtError::ArithmeticError(_) => None,
            StmtError::NewAtomicFactError(_) => None,
            StmtError::StoreFactError(_) => None,
            StmtError::ParseBlockError(e) => e.line_file(),
            StmtError::ParsingError(e) => Some(e.line_file_index),
            StmtError::ExecError(e) => e.line_file_index,
            StmtError::UnknownError(e) => e.line_file_index,
            StmtError::WellDefinedError(e) => e.line_file_index,
            StmtError::VerifyError(e) => e.line_file_index,
            StmtError::InferError(e) => e.line_file_index,
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
            StmtError::ArithmeticError(e) => e.msg.clone(),
            StmtError::NewAtomicFactError(e) => e.msg.clone(),
            StmtError::StoreFactError(e) => {
                let mut s = e.msg.clone();
                for p in &e.previous_errors {
                    s.push_str("\n");
                    s.push_str(&p.error_body());
                }
                s
            }
            StmtError::ParseBlockError(e) => parse_block_error_message(e),
            StmtError::ParsingError(e) => e.msg.clone(),
            StmtError::ExecError(e) => {
                let mut s = e.msg.clone();
                for p in &e.previous_errors {
                    s.push_str("\n");
                    s.push_str(&p.error_body());
                }
                s
            }
            StmtError::UnknownError(e) => e.msg.clone(),
            StmtError::WellDefinedError(e) => {
                let mut s = e.msg.clone();
                for p in &e.previous_errors {
                    s.push_str("\n");
                    s.push_str(&p.error_body());
                }
                s
            }
            StmtError::VerifyError(e) => {
                let mut s = e.msg.clone();
                for p in &e.previous_errors {
                    s.push_str("\n");
                    s.push_str(&p.error_body());
                }
                s
            }
            StmtError::InferError(e) => e.msg.clone(),
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
}


impl ArithmeticError {
    pub fn new(msg: String) -> Self {
        ArithmeticError { msg }
    }
}

impl fmt::Display for ArithmeticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
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
}

impl std::error::Error for NewAtomicFactError {}

impl fmt::Display for NewAtomicFactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl NewAtomicFactError {
    pub fn new(msg: String) -> Self {
        NewAtomicFactError { msg }
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
        StoreFactError::new(msg, vec![e.into()])
    }
}

impl From<NewAtomicFactError> for WellDefinedError {
    fn from(e: NewAtomicFactError) -> Self {
        let msg = e.msg.clone();
        WellDefinedError::new(msg, vec![e.into()], None)
    }
}

#[derive(Debug)]
pub struct StoreFactError {
    pub msg: String,
    pub previous_errors: Vec<StmtError>,
}

impl std::error::Error for StoreFactError {}

impl fmt::Display for StoreFactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl StoreFactError {
    pub fn new(msg: String, previous_errors: Vec<StmtError>) -> Self {
        StoreFactError { msg, previous_errors }
    }

    /// Content only (msg + previous_errors bodies), for embedding in other errors.
    pub fn body_string(&self) -> String {
        let rest: Vec<String> = self.previous_errors.iter().map(|p| p.error_body()).collect();
        self.msg.clone() + "\n" + &rest.join("\n")
    }
}

impl From<StoreFactError> for StmtError {
    fn from(e: StoreFactError) -> Self {
        StmtError::StoreFactError(e)
    }
}

impl From<StoreFactError> for ExecError {
    fn from(e: StoreFactError) -> Self {
        let rest: Vec<String> = e.previous_errors.iter().map(|p| p.error_body()).collect();
        let body = e.msg.clone() + "\n" + &rest.join("\n");
        ExecError::new(body, vec![e.into()], None)
    }
}

#[derive(Debug)]
pub enum ParseBlockError {
    ExpectedIndent(usize, usize),
    UnexpectedIndent(usize, usize),
    InconsistentIndent(usize, usize),
    MissingBody(usize, usize),
    NameAlreadyUsed(String),
}

impl std::error::Error for ParseBlockError {}

impl fmt::Display for ParseBlockError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", parse_block_error_message(self))
    }
}

impl ParseBlockError {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            ParseBlockError::ExpectedIndent(line, file) => Some((*line, *file)),
            ParseBlockError::UnexpectedIndent(line, file) => Some((*line, *file)),
            ParseBlockError::InconsistentIndent(line, file) => Some((*line, *file)),
            ParseBlockError::MissingBody(line, file) => Some((*line, *file)),
            ParseBlockError::NameAlreadyUsed(_) => None,
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
    pub line_file_index: (usize, usize),
}

impl std::error::Error for ParsingError {}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl ParsingError {
    pub fn new(msg: String, line_file_index: (usize, usize)) -> Self {
        ParsingError { msg, line_file_index }
    }
}

impl From<ParsingError> for StmtError {
    fn from(e: ParsingError) -> Self {
        StmtError::ParsingError(e)
    }
}


#[derive(Debug)]
pub struct ExecError {
    pub msg: String,
    pub previous_errors: Vec<StmtError>,
    pub line_file_index: Option<(usize, usize)>,
}

impl std::error::Error for ExecError {}

impl fmt::Display for ExecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.body_string())
    }
}

impl ExecError {
    pub fn new(msg: String, previous_errors: Vec<StmtError>, line_file_index: Option<(usize, usize)>) -> Self {
        ExecError { msg, previous_errors, line_file_index }
    }

    /// Content only (msg + previous_errors bodies), for embedding in other errors.
    pub fn body_string(&self) -> String {
        let rest: Vec<String> = self.previous_errors.iter().map(|p| p.error_body()).collect();
        self.msg.clone() + "\n" + &rest.join("\n")
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
    pub previous_errors: Vec<StmtError>,
    pub line_file_index: Option<(usize, usize)>,
}

impl std::error::Error for WellDefinedError {}

impl fmt::Display for WellDefinedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let rest: Vec<String> = self.previous_errors.iter().map(|p| p.error_body()).collect();
        write!(f, "{}\n{}", self.msg, rest.join("\n"))
    }
}

impl WellDefinedError {
    pub fn new(msg: String, previous_errors: Vec<StmtError>, line_file_index: Option<(usize, usize)>) -> Self {
        WellDefinedError { msg, previous_errors, line_file_index }
    }
}

impl From<WellDefinedError> for StmtError {
    fn from(e: WellDefinedError) -> Self {
        StmtError::WellDefinedError(e)
    }
}

impl From<WellDefinedError> for ExecError {
    fn from(e: WellDefinedError) -> Self {
        let rest: Vec<String> = e.previous_errors.iter().map(|p| p.error_body()).collect();
        let body = "well defined error: ".to_string() + &e.msg + "\n" + &rest.join("\n");
        ExecError::new(body, vec![e.into()], None)
    }
}

#[derive(Debug)]
pub struct VerifyError {
    pub msg: String,
    pub previous_errors: Vec<StmtError>,
    pub line_file_index: Option<(usize, usize)>,
}

impl std::error::Error for VerifyError {}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let rest: Vec<String> = self.previous_errors.iter().map(|p| p.error_body()).collect();
        write!(f, "{}\n{}", self.msg, rest.join("\n"))
    }
}

impl VerifyError {
    pub fn new(msg: String, previous_errors: Vec<StmtError>, line_file_index: Option<(usize, usize)>) -> Self {
        VerifyError { msg, previous_errors, line_file_index }
    }
}

impl From<VerifyError> for StmtError {
    fn from(e: VerifyError) -> Self {
        StmtError::VerifyError(e)
    }
}

impl From<VerifyError> for ExecError {
    fn from(e: VerifyError) -> Self {
        let rest: Vec<String> = e.previous_errors.iter().map(|p| p.error_body()).collect();
        let body = "verify fact error: ".to_string() + &e.msg + "\n" + &rest.join("\n");
        ExecError::new(body, vec![e.into()], None)
    }
}

impl From<VerifyError> for WellDefinedError {
    fn from(e: VerifyError) -> Self {
        let rest: Vec<String> = e.previous_errors.iter().map(|p| p.error_body()).collect();
        let body = "verify fact error: ".to_string() + &e.msg + "\n" + &rest.join("\n");
        WellDefinedError::new(body, vec![e.into()], None)
    }
}

#[derive(Debug)]
pub struct UnknownError {
    pub msg: String,
    pub line_file_index: Option<(usize, usize)>,
}

impl std::error::Error for UnknownError {}

impl fmt::Display for UnknownError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl UnknownError {
    pub fn new(msg: String, line_file_index: Option<(usize, usize)>) -> Self {
        UnknownError { msg, line_file_index }
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
    pub line_file_index: Option<(usize, usize)>,
}

impl std::error::Error for InferError {}

impl fmt::Display for InferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl InferError {
    pub fn new(msg: String, line_file_index: Option<(usize, usize)>) -> Self {
        InferError { msg, line_file_index }
    }
}

impl From<InferError> for StmtError {
    fn from(e: InferError) -> Self {
        StmtError::InferError(e)
    }
}

impl From<InferError> for ExecError {
    fn from(e: InferError) -> Self {
        let msg = e.msg.clone();
        ExecError::new(msg, vec![e.into()], None)
    }
}

#[derive(Debug)]
pub struct NameAlreadyUsedError {
    pub name: String,
}

impl std::error::Error for NameAlreadyUsedError {}

impl fmt::Display for NameAlreadyUsedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "name {} is already used", self.name)
    }
}