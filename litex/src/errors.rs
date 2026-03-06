use std::fmt;

#[derive(Debug)]
pub enum StmtError {
    ArithmeticError(ArithmeticError),
    NewAtomicFactError(NewAtomicFactError),
    StoreFactError(StoreFactError),
    ParseBlockError(ParseBlockError),
    ParsingError(ParsingError),
    ExecError(ExecError), 
}

impl std::error::Error for StmtError {}


impl fmt::Display for StmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StmtError::ArithmeticError(e) => write!(f, "{}", e),
            StmtError::NewAtomicFactError(e) => write!(f, "{}", e),
            StmtError::StoreFactError(e) => write!(f, "{}", e),
            StmtError::ParseBlockError(e) => write!(f, "{}", e),
            StmtError::ParsingError(e) => write!(f, "{}", e),
            StmtError::ExecError(e) => write!(f, "{}", e),
        }
    }
}


#[derive(Debug)]
pub struct ArithmeticError{
    pub msg: String,
}


impl fmt::Display for ArithmeticError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}", "ArithmeticError:".to_string(), self.msg)
    }
}

impl ArithmeticError {
    pub fn new(msg: &str) -> Self {
        ArithmeticError { msg: msg.to_string() }
    }
}

#[derive(Debug)]
pub struct NewAtomicFactError {
    pub msg: String,
}

impl std::error::Error for NewAtomicFactError {}

impl fmt::Display for NewAtomicFactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}", "NewAtomicFactError:".to_string(), self.msg)
    }
}

impl NewAtomicFactError {
    pub fn new(msg: &str) -> Self {
        NewAtomicFactError { msg: msg.to_string() }
    }
}


#[derive(Debug)]
pub struct StoreFactError {
    pub msg: String,
}

impl std::error::Error for StoreFactError {}

impl fmt::Display for StoreFactError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}", "StoreFactError:".to_string(), self.msg)
    }
}

impl StoreFactError {
    pub fn new(msg: &str) -> Self {
        StoreFactError { msg: msg.to_string() }
    }
}

#[derive(Debug)]
pub enum ParseBlockError {
    ExpectedIndent { line: usize },
    UnexpectedIndent { line: usize },
    InconsistentIndent { line: usize },
    MissingBody { line: usize },
}

impl std::error::Error for ParseBlockError {}

impl fmt::Display for ParseBlockError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseBlockError::ExpectedIndent { line } => {
                write!(f, "line {}: expected indent", line)
            }
            ParseBlockError::UnexpectedIndent { line } => {
                write!(f, "line {}: unexpected indent", line)
            }
            ParseBlockError::InconsistentIndent { line } => {
                write!(f, "line {}: inconsistent indent", line)
            }
            ParseBlockError::MissingBody { line } => {
                write!(f, "line {}: block header missing body", line)
            }
        }
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
        write!(f, "ParsingError on line {} in file index {}: {}", self.line_file_index.0, self.line_file_index.1, self.msg)
    }
}

impl ParsingError {
    pub fn new(msg: &str, line_file_index: (usize, usize)) -> Self {
        ParsingError { msg: msg.to_string(), line_file_index }
    }
}


#[derive(Debug)]
pub struct ExecError {
    pub msg: String,
}

impl std::error::Error for ExecError {}

impl fmt::Display for ExecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}\n{}", "Execution Error:".to_string(), self.msg)
    }
}

impl ExecError {
    pub fn new(msg: &str) -> Self {
        ExecError { msg: msg.to_string() }
    }
}