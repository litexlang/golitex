use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub enum RuntimeError {
    ArithmeticError(RuntimeErrorStruct),
    NewAtomicFactError(RuntimeErrorStruct),
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
pub struct NewAtomicFactRuntimeError(pub RuntimeErrorStruct);
impl From<NewAtomicFactRuntimeError> for RuntimeError {
    fn from(w: NewAtomicFactRuntimeError) -> Self {
        RuntimeError::NewAtomicFactError(w.0)
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
    ) -> Self {
        RuntimeErrorStruct::new_with_inside_results(
            statement,
            msg,
            line_file,
            previous_error,
            vec![],
        )
    }

    pub fn new_with_inside_results(
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
            previous_error: boxed_previous_error(previous_error),
            inside_results,
        }
    }

    pub fn new_with_msg_previous_error(msg: String, previous_error: Option<RuntimeError>) -> Self {
        RuntimeErrorStruct::new(None, msg, default_line_file(), previous_error)
    }

    pub fn exec_stmt_new(
        stmt: Option<Stmt>,
        info: String,
        previous_error: Option<RuntimeError>,
        inside_results: Vec<StmtResult>,
    ) -> Self {
        let line_file = if let Some(ref stmt) = stmt {
            stmt.line_file()
        } else {
            default_line_file()
        };
        RuntimeErrorStruct::new_with_inside_results(
            stmt,
            info,
            line_file,
            previous_error,
            inside_results,
        )
    }

    pub fn exec_stmt_new_with_stmt(
        stmt: Stmt,
        info: String,
        previous_error: Option<RuntimeError>,
        inside_results: Vec<StmtResult>,
    ) -> Self {
        let line_file = stmt.line_file();
        RuntimeErrorStruct::new_with_inside_results(
            Some(stmt),
            info,
            line_file,
            previous_error,
            inside_results,
        )
    }

    pub fn exec_stmt_with_message_and_cause(
        stmt: Stmt,
        message: String,
        cause: Option<RuntimeError>,
        inside_results: Vec<StmtResult>,
    ) -> Self {
        let line_file = stmt.line_file();
        let previous_error = if message.is_empty() {
            cause
        } else {
            Some(
                RuntimeError::new_unknown_error_with_msg_position_optional_stmt_previous_error(
                    message.clone(),
                    line_file,
                    Some(stmt.clone()),
                    cause,
                ),
            )
        };
        RuntimeErrorStruct::exec_stmt_new_with_stmt(stmt, message, previous_error, inside_results)
    }
}

impl std::error::Error for RuntimeError {}

impl From<RuntimeErrorStruct> for RuntimeError {
    fn from(s: RuntimeErrorStruct) -> Self {
        RuntimeError::ExecStmtError(s)
    }
}

impl RuntimeError {
    pub fn wrap_new_atomic_fact_as_store_conflict(e: RuntimeError) -> RuntimeError {
        match e {
            RuntimeError::NewAtomicFactError(s) => {
                NewAtomicFactRuntimeError(RuntimeErrorStruct::new_with_inside_results(
                    s.statement.clone(),
                    s.msg.clone(),
                    s.line_file.clone(),
                    Some(NewAtomicFactRuntimeError(s).into()),
                    vec![],
                ))
                .into()
            }
            _ => e,
        }
    }

    pub fn line_file(&self) -> LineFile {
        match self {
            RuntimeError::ArithmeticError(e) => e.line_file.clone(),
            RuntimeError::NewAtomicFactError(e) => e.line_file.clone(),
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
            RuntimeError::NewAtomicFactError(_) => "NewAtomicFactError",
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

    pub fn new_infer_error_with_msg_position_previous_error(
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        InferRuntimeError(RuntimeErrorStruct::new(
            None,
            msg,
            line_file,
            previous_error,
        ))
        .into()
    }

    pub fn new_define_params_error_with_msg_previous_error_position(
        msg: String,
        previous_error: Option<RuntimeError>,
        line_file: LineFile,
    ) -> Self {
        DefineParamsRuntimeError(RuntimeErrorStruct::new(
            None,
            msg,
            line_file,
            previous_error,
        ))
        .into()
    }

    pub fn new_parse_error_with_msg_position_previous_error(
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        ParseRuntimeError(RuntimeErrorStruct::new(
            None,
            msg,
            line_file,
            previous_error,
        ))
        .into()
    }

    pub fn new_parse_error_for_block_unexpected_indent_at_line_file(line_file: LineFile) -> Self {
        let (line_no, path) = (line_file.0, line_file.1.as_ref());
        Self::new_parse_error_with_msg_position_previous_error(
            format!("unexpected indent at line {} in {}", line_no, path),
            line_file,
            None,
        )
    }

    pub fn new_parse_error_for_block_expected_indent_at_line_file(line_file: LineFile) -> Self {
        let (line_no, path) = (line_file.0, line_file.1.as_ref());
        Self::new_parse_error_with_msg_position_previous_error(
            format!("expected indent at line {} in {}", line_no, path),
            line_file,
            None,
        )
    }

    pub fn new_parse_error_for_block_missing_body_at_line_file(line_file: LineFile) -> Self {
        let (line_no, path) = (line_file.0, line_file.1.as_ref());
        Self::new_parse_error_with_msg_position_previous_error(
            format!("block header missing body at line {} in {}", line_no, path),
            line_file,
            None,
        )
    }

    pub fn new_parse_error_for_block_inconsistent_indent_at_line_file(line_file: LineFile) -> Self {
        let (line_no, path) = (line_file.0, line_file.1.as_ref());
        Self::new_parse_error_with_msg_position_previous_error(
            format!("inconsistent indent at line {} in {}", line_no, path),
            line_file,
            None,
        )
    }

    pub fn new_verify_error_with_fact_msg_position_previous_error(
        fact: Fact,
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        VerifyRuntimeError(RuntimeErrorStruct::new(
            Some(fact.into_stmt()),
            msg,
            line_file,
            previous_error,
        ))
        .into()
    }

    pub fn new_verify_error_with_msg_position_previous_error(
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        VerifyRuntimeError(RuntimeErrorStruct::new(
            None,
            msg,
            line_file,
            previous_error,
        ))
        .into()
    }

    pub fn new_unknown_error_with_msg_position_optional_stmt_previous_error(
        msg: String,
        line_file: LineFile,
        statement: Option<Stmt>,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        UnknownRuntimeError(RuntimeErrorStruct::new(
            statement,
            msg,
            line_file,
            previous_error,
        ))
        .into()
    }

    pub fn new_verify_result_unknown_with_fact_previous_error(
        fact: Fact,
        msg: String,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        let line_file = fact.line_file();
        let stmt = fact.into_stmt();
        RuntimeError::new_unknown_error_with_msg_position_optional_stmt_previous_error(
            msg,
            line_file,
            Some(stmt),
            previous_error,
        )
    }

    pub fn new_well_defined_error_with_msg_previous_error_position(
        msg: String,
        previous_error: Option<RuntimeError>,
        line_file: LineFile,
    ) -> Self {
        WellDefinedRuntimeError(RuntimeErrorStruct::new(
            None,
            msg,
            line_file,
            previous_error,
        ))
        .into()
    }

    pub fn new_well_defined_error_wrapping_verify_runtime_error(e: RuntimeError) -> RuntimeError {
        match e {
            RuntimeError::VerifyError(inner) => {
                let line_file = inner.line_file.clone();
                let msg_for_well_defined = if inner.msg.is_empty() {
                    "verify fact error:".to_string()
                } else {
                    inner.msg.clone()
                };
                WellDefinedRuntimeError(RuntimeErrorStruct::new(
                    None,
                    msg_for_well_defined,
                    line_file,
                    Some(VerifyRuntimeError(inner).into()),
                ))
                .into()
            }
            _ => e,
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

fn boxed_previous_error(previous_error: Option<RuntimeError>) -> Option<Box<RuntimeError>> {
    previous_error.map(Box::new)
}
