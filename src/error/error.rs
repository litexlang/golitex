use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub enum RuntimeError {
    ArithmeticError(RuntimeErrorStruct),
    NewFactError(RuntimeErrorStruct),
    StoreFactError(RuntimeErrorStruct),
    ParseError(RuntimeErrorStruct),
    ExecStmtError(RuntimeErrorStruct),
    WellDefinedError(RuntimeErrorStruct),
    VerifyError(RuntimeErrorStruct),
    UnknownError(RuntimeErrorStruct),
    InferError(RuntimeErrorStruct),
    NameAlreadyUsedError(RuntimeErrorStruct),
    DefineParamsError(RuntimeErrorStruct),
    InstantiateError(RuntimeErrorStruct),
}

#[derive(Debug)]
pub struct RuntimeErrorStruct {
    pub statement: Option<Stmt>,
    pub msg: String,
    pub line_file: LineFile,
    pub previous_error: Option<Box<RuntimeError>>,
    pub inside_results: Vec<StmtResult>,
}

#[derive(Debug)]
pub struct ArithmeticRuntimeError(pub RuntimeErrorStruct);

impl From<ArithmeticRuntimeError> for RuntimeError {
    fn from(w: ArithmeticRuntimeError) -> Self {
        RuntimeError::ArithmeticError(w.0)
    }
}

#[derive(Debug)]
pub struct NewFactRuntimeError(pub RuntimeErrorStruct);

impl From<NewFactRuntimeError> for RuntimeError {
    fn from(w: NewFactRuntimeError) -> Self {
        RuntimeError::NewFactError(w.0)
    }
}

#[derive(Debug)]
pub struct StoreFactRuntimeError(pub RuntimeErrorStruct);

impl From<StoreFactRuntimeError> for RuntimeError {
    fn from(w: StoreFactRuntimeError) -> Self {
        RuntimeError::StoreFactError(w.0)
    }
}

#[derive(Debug)]
pub struct ParseRuntimeError(pub RuntimeErrorStruct);

impl From<ParseRuntimeError> for RuntimeError {
    fn from(w: ParseRuntimeError) -> Self {
        RuntimeError::ParseError(w.0)
    }
}

#[derive(Debug)]
pub struct WellDefinedRuntimeError(pub RuntimeErrorStruct);

impl From<WellDefinedRuntimeError> for RuntimeError {
    fn from(w: WellDefinedRuntimeError) -> Self {
        RuntimeError::WellDefinedError(w.0)
    }
}

#[derive(Debug)]
pub struct VerifyRuntimeError(pub RuntimeErrorStruct);

impl From<VerifyRuntimeError> for RuntimeError {
    fn from(w: VerifyRuntimeError) -> Self {
        RuntimeError::VerifyError(w.0)
    }
}

#[derive(Debug)]
pub struct UnknownRuntimeError(pub RuntimeErrorStruct);

impl From<UnknownRuntimeError> for RuntimeError {
    fn from(w: UnknownRuntimeError) -> Self {
        RuntimeError::UnknownError(w.0)
    }
}

#[derive(Debug)]
pub struct InferRuntimeError(pub RuntimeErrorStruct);

impl From<InferRuntimeError> for RuntimeError {
    fn from(w: InferRuntimeError) -> Self {
        RuntimeError::InferError(w.0)
    }
}

#[derive(Debug)]
pub struct NameAlreadyUsedRuntimeError(pub RuntimeErrorStruct);

impl From<NameAlreadyUsedRuntimeError> for RuntimeError {
    fn from(w: NameAlreadyUsedRuntimeError) -> Self {
        RuntimeError::NameAlreadyUsedError(w.0)
    }
}

#[derive(Debug)]
pub struct DefineParamsRuntimeError(pub RuntimeErrorStruct);

impl From<DefineParamsRuntimeError> for RuntimeError {
    fn from(w: DefineParamsRuntimeError) -> Self {
        RuntimeError::DefineParamsError(w.0)
    }
}

#[derive(Debug)]
pub struct InstantiateRuntimeError(pub RuntimeErrorStruct);

impl From<InstantiateRuntimeError> for RuntimeError {
    fn from(w: InstantiateRuntimeError) -> Self {
        RuntimeError::InstantiateError(w.0)
    }
}

impl RuntimeErrorStruct {
    pub fn new(
        statement: Option<Stmt>,
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
        inside_results: Vec<StmtResult>,
    ) -> Self {
        RuntimeErrorStruct {
            statement,
            msg,
            line_file,
            previous_error: previous_error.map(Box::new),
            inside_results,
        }
    }
}

pub fn short_exec_error(
    stmt: Stmt,
    message: impl Into<String>,
    cause: Option<RuntimeError>,
    inside_results: Vec<StmtResult>,
) -> RuntimeError {
    let message = message.into();
    let line_file = stmt.line_file();
    RuntimeError::ExecStmtError(RuntimeErrorStruct::new(
        Some(stmt.clone()),
        message,
        line_file.clone(),
        cause,
        inside_results,
    ))
}

pub fn exec_stmt_error_with_stmt_and_cause(stmt: Stmt, cause: RuntimeError) -> RuntimeError {
    RuntimeError::ExecStmtError(RuntimeErrorStruct::new(
        Some(stmt.clone()),
        String::new(),
        stmt.line_file(),
        Some(cause),
        vec![],
    ))
}

impl std::error::Error for RuntimeError {}

impl RuntimeError {
    pub fn wrap_new_fact_as_store_conflict(e: RuntimeError) -> RuntimeError {
        match e {
            RuntimeError::NewFactError(s) => NewFactRuntimeError(RuntimeErrorStruct::new(
                s.statement.clone(),
                s.msg.clone(),
                s.line_file.clone(),
                Some(NewFactRuntimeError(s).into()),
                vec![],
            ))
            .into(),
            _ => e,
        }
    }

    pub fn line_file(&self) -> LineFile {
        match self {
            RuntimeError::ArithmeticError(e) => e.line_file.clone(),
            RuntimeError::NewFactError(e) => e.line_file.clone(),
            RuntimeError::StoreFactError(e) => e.line_file.clone(),
            RuntimeError::ParseError(e) => e.line_file.clone(),
            RuntimeError::ExecStmtError(e) => e.line_file.clone(),
            RuntimeError::WellDefinedError(e) => e.line_file.clone(),
            RuntimeError::VerifyError(e) => e.line_file.clone(),
            RuntimeError::UnknownError(e) => e.line_file.clone(),
            RuntimeError::InferError(e) => e.line_file.clone(),
            RuntimeError::NameAlreadyUsedError(e) => e.line_file.clone(),
            RuntimeError::DefineParamsError(e) => e.line_file.clone(),
            RuntimeError::InstantiateError(e) => e.line_file.clone(),
        }
    }

    pub fn display_label(&self) -> &'static str {
        match self {
            RuntimeError::ArithmeticError(_) => "ArithmeticError",
            RuntimeError::NewFactError(_) => "NewFactError",
            RuntimeError::StoreFactError(_) => "StoreFactError",
            RuntimeError::ParseError(_) => "ParseError",
            RuntimeError::ExecStmtError(_) => "ExecStmtError",
            RuntimeError::WellDefinedError(_) => "WellDefinedError",
            RuntimeError::VerifyError(_) => "VerifyError",
            RuntimeError::UnknownError(_) => "UnknownError",
            RuntimeError::InferError(_) => "InferError",
            RuntimeError::NameAlreadyUsedError(_) => "NameAlreadyUsedError",
            RuntimeError::DefineParamsError(_) => "DefineParamsError",
            RuntimeError::InstantiateError(_) => "InstantiateError",
        }
    }
}

// Display outputs a short placeholder; JSON: `display_runtime_error_json` in `crate::pipeline`.
impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", "error")
    }
}

impl fmt::Display for RuntimeErrorStruct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.msg)
    }
}

impl std::error::Error for RuntimeErrorStruct {}

impl RuntimeErrorStruct {
    pub fn new_with_just_msg(msg: String) -> Self {
        Self::new(None, msg, default_line_file(), None, vec![])
    }

    pub fn new_with_msg_and_line_file(msg: String, line_file: LineFile) -> Self {
        Self::new(None, msg, line_file, None, vec![])
    }

    pub fn new_with_msg_and_cause(msg: String, cause: RuntimeError) -> Self {
        Self::new(None, msg, default_line_file(), Some(cause), vec![])
    }
}
