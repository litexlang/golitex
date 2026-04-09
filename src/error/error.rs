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
    pub conflict_with: Option<ConflictMsg>,
    pub line_file: LineFile,
    pub previous_error: Option<Box<RuntimeError>>,
    pub inside_results: Vec<StmtExecResult>,
}

#[derive(Debug, Clone)]
pub struct ConflictMsg {
    pub msg: String,
    pub line_file: LineFile,
    pub stmt: Option<Stmt>,
}

impl RuntimeErrorStruct {
    pub fn new(
        statement: Option<Stmt>,
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        RuntimeErrorStruct::new_with_conflict(
            statement,
            msg,
            line_file,
            None,
            previous_error,
            vec![],
        )
    }

    pub fn new_with_conflict(
        statement: Option<Stmt>,
        msg: String,
        line_file: LineFile,
        conflict_with: Option<ConflictMsg>,
        previous_error: Option<RuntimeError>,
        inside_results: Vec<StmtExecResult>,
    ) -> Self {
        RuntimeErrorStruct {
            statement,
            msg,
            conflict_with,
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
        inside_results: Vec<StmtExecResult>,
    ) -> Self {
        let line_file = if let Some(ref stmt) = stmt {
            stmt.line_file()
        } else {
            default_line_file()
        };
        RuntimeErrorStruct::new_with_conflict(
            stmt,
            info,
            line_file,
            None,
            previous_error,
            inside_results,
        )
    }

    pub fn exec_stmt_new_with_stmt(
        stmt: Stmt,
        info: String,
        previous_error: Option<RuntimeError>,
        inside_results: Vec<StmtExecResult>,
    ) -> Self {
        let line_file = stmt.line_file();
        RuntimeErrorStruct::new_with_conflict(
            Some(stmt),
            info,
            line_file,
            None,
            previous_error,
            inside_results,
        )
    }

    pub fn exec_stmt_with_message_and_cause(
        stmt: Stmt,
        message: String,
        cause: Option<RuntimeError>,
        inside_results: Vec<StmtExecResult>,
    ) -> Self {
        let line_file = stmt.line_file();
        let previous_error = if message.is_empty() {
            cause
        } else {
            Some(
                RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
                    message.clone(),
                    line_file,
                    None,
                    cause,
                ),
            )
        };
        RuntimeErrorStruct::exec_stmt_new_with_stmt(stmt, message, previous_error, inside_results)
    }
}

impl std::error::Error for RuntimeError {}

impl RuntimeError {
    pub fn into_struct(self) -> RuntimeErrorStruct {
        match self {
            RuntimeError::ArithmeticError(s) => s,
            RuntimeError::NewAtomicFactError(s) => s,
            RuntimeError::StoreFactError(s) => s,
            RuntimeError::ParseError(s) => s,
            RuntimeError::ExecStmtError(s) => s,
            RuntimeError::WellDefinedError(s) => s,
            RuntimeError::VerifyError(s) => s,
            RuntimeError::UnknownError(s) => s,
            RuntimeError::InferError(s) => s,
            RuntimeError::NameAlreadyUsedError(s) => s,
            RuntimeError::DefineParamsError(s) => s,
            RuntimeError::InstantiateError(s) => s,
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

    pub fn message_text_for_duplicate_used_name_without_line_file(name: &str) -> String {
        format!(
            "name `{}` is already used, cannot be used again for other definitions",
            name
        )
    }

    pub fn new_infer_error_with_msg_position_previous_error(
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        RuntimeError::InferError(RuntimeErrorStruct::new(
            None,
            msg,
            line_file,
            previous_error,
        ))
    }

    pub fn new_define_params_error_with_msg_previous_error_position(
        msg: String,
        previous_error: Option<RuntimeError>,
        line_file: LineFile,
    ) -> Self {
        RuntimeError::DefineParamsError(RuntimeErrorStruct::new(
            None,
            msg,
            line_file,
            previous_error,
        ))
    }

    pub fn new_parse_error_with_msg_position_previous_error(
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        RuntimeError::ParseError(RuntimeErrorStruct::new(
            None,
            msg,
            line_file,
            previous_error,
        ))
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
        RuntimeError::VerifyError(RuntimeErrorStruct::new(
            Some(fact.into_stmt()),
            msg,
            line_file,
            previous_error,
        ))
    }

    pub fn new_verify_error_with_msg_position_previous_error(
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        RuntimeError::VerifyError(RuntimeErrorStruct::new(
            None,
            msg,
            line_file,
            previous_error,
        ))
    }

    pub fn new_unknown_error_with_msg_position_optional_fact_previous_error(
        msg: String,
        line_file: LineFile,
        fact: Option<Fact>,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        RuntimeError::UnknownError(RuntimeErrorStruct::new(
            if let Some(fact) = fact {
                Some(fact.into_stmt())
            } else {
                None
            },
            msg,
            line_file,
            previous_error,
        ))
    }

    pub fn new_verify_result_unknown_with_fact_previous_error(
        fact: Fact,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        let line_file = fact.line_file();
        RuntimeError::new_unknown_error_with_msg_position_optional_fact_previous_error(
            String::new(),
            line_file,
            Some(fact),
            previous_error,
        )
    }

    pub fn new_well_defined_error_with_msg_previous_error_position(
        msg: String,
        previous_error: Option<RuntimeError>,
        line_file: LineFile,
    ) -> Self {
        RuntimeError::WellDefinedError(RuntimeErrorStruct::new(
            None,
            msg,
            line_file,
            previous_error,
        ))
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
                RuntimeError::WellDefinedError(RuntimeErrorStruct::new(
                    None,
                    msg_for_well_defined,
                    line_file,
                    Some(RuntimeError::VerifyError(inner)),
                ))
            }
            _ => e,
        }
    }
}

// Display outputs a short placeholder; full machine-readable form is [`RuntimeError::to_display_json_string`].
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

impl From<RuntimeErrorStruct> for RuntimeError {
    fn from(runtime_error_struct: RuntimeErrorStruct) -> Self {
        RuntimeError::ExecStmtError(runtime_error_struct)
    }
}

fn boxed_previous_error(previous_error: Option<RuntimeError>) -> Option<Box<RuntimeError>> {
    previous_error.map(Box::new)
}
