use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

#[derive(Debug)]
pub struct RuntimeErrorStruct {
    pub statement: Option<Stmt>,
    pub msg: String,
    pub conflict_with: Option<ConflictMsg>,
    pub line_file: LineFile,
    pub previous_error: Option<Box<RuntimeError>>,
    pub inside_results: Vec<NonErrStmtExecResult>,
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
        inside_results: Vec<NonErrStmtExecResult>,
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
        inside_results: Vec<NonErrStmtExecResult>,
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
        inside_results: Vec<NonErrStmtExecResult>,
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
        inside_results: Vec<NonErrStmtExecResult>,
    ) -> Self {
        let line_file = stmt.line_file();
        let previous_error = if message.is_empty() {
            cause
        } else {
            Some(RuntimeError::unknown_error(
                message.clone(),
                line_file,
                None,
                cause,
            ))
        };
        RuntimeErrorStruct::exec_stmt_new_with_stmt(stmt, message, previous_error, inside_results)
    }

    pub fn into_runtime_error_as_new_atomic_fact_layer(self) -> RuntimeError {
        RuntimeError::NewAtomicFactError(self)
    }

    pub fn into_runtime_error_as_store_fact_layer(self) -> RuntimeError {
        RuntimeError::StoreFactError(self)
    }

    pub fn into_runtime_error_as_arithmetic_layer(self) -> RuntimeError {
        RuntimeError::ArithmeticError(self)
    }

    pub fn into_store_fact_wrapping_new_atomic(self) -> RuntimeErrorStruct {
        let conflict_with_for_outer = self.conflict_with.clone();
        let statement_for_outer_store_fact_error_layer = self.statement.clone();
        let msg_for_outer_store_fact_error_layer = self.msg.clone();
        let line_file = self.line_file.clone();
        let wrapped_new_atomic_runtime_error = RuntimeError::NewAtomicFactError(self);
        RuntimeErrorStruct::new_with_conflict(
            statement_for_outer_store_fact_error_layer,
            msg_for_outer_store_fact_error_layer,
            line_file,
            conflict_with_for_outer,
            Some(wrapped_new_atomic_runtime_error),
            vec![],
        )
    }

    pub fn into_well_defined_wrapping_new_atomic(self) -> RuntimeError {
        let line_file = self.line_file.clone();
        let msg_for_well_defined_error = self.msg.clone();
        let wrapped_runtime_error = RuntimeError::NewAtomicFactError(self);
        RuntimeError::WellDefinedError(RuntimeErrorStruct::new(
            None,
            msg_for_well_defined_error,
            line_file,
            Some(wrapped_runtime_error),
        ))
    }
}

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

impl std::error::Error for RuntimeError {}

impl RuntimeError {
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

    /// Short label for display (e.g. "ExecError", "VerifyUnknownError").
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

    pub fn duplicate_used_name_error_msg_without_line_file(name: &str) -> String {
        format!(
            "name `{}` is already used, cannot be used again for other definitions",
            name
        )
    }

    pub fn infer_error(
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

    pub fn define_params_error(
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

    pub fn name_already_used_error(
        name: String,
        name_already_used_on_line_file: LineFile,
        line_file: LineFile,
    ) -> Self {
        let msg = format!(
            "name `{}` is already used: previous definition at line {} in {}; current at line {} in {}",
            name,
            name_already_used_on_line_file.0,
            name_already_used_on_line_file.1.as_ref(),
            line_file.0,
            line_file.1.as_ref(),
        );
        RuntimeError::NameAlreadyUsedError(RuntimeErrorStruct::new(None, msg, line_file, None))
    }

    pub fn parse_error(
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

    pub fn parse_error_wrap(
        inner: RuntimeError,
        outer_line_file: LineFile,
        outer_summary: Option<String>,
    ) -> Self {
        let RuntimeError::ParseError(inner_struct) = inner else {
            return inner;
        };
        let summary = outer_summary.unwrap_or_else(|| inner_struct.msg.clone());
        RuntimeError::ParseError(RuntimeErrorStruct::new(
            None,
            summary,
            outer_line_file,
            Some(RuntimeError::ParseError(inner_struct)),
        ))
    }

    pub fn parse_block_unexpected_indent(line_no: usize, path: Rc<str>) -> Self {
        Self::parse_error(
            format!("unexpected indent at line {} in {}", line_no, path.as_ref()),
            (line_no, path.clone()),
            None,
        )
    }

    pub fn parse_block_expected_indent(line_no: usize, path: Rc<str>) -> Self {
        Self::parse_error(
            format!("expected indent at line {} in {}", line_no, path.as_ref()),
            (line_no, path.clone()),
            None,
        )
    }

    pub fn parse_block_missing_body(line_no: usize, path: Rc<str>) -> Self {
        Self::parse_error(
            format!(
                "block header missing body at line {} in {}",
                line_no,
                path.as_ref()
            ),
            (line_no, path.clone()),
            None,
        )
    }

    pub fn parse_block_inconsistent_indent(line_no: usize, path: Rc<str>) -> Self {
        Self::parse_error(
            format!("inconsistent indent at line {} in {}", line_no, path.as_ref()),
            (line_no, path.clone()),
            None,
        )
    }

    pub fn verify_error(
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

    pub fn verify_error_message_only(
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

    pub fn unknown_error(
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

    pub fn verify_result_unknown(fact: Fact, previous_error: Option<RuntimeError>) -> Self {
        let line_file = fact.line_file();
        RuntimeError::unknown_error(String::new(), line_file, Some(fact), previous_error)
    }

    pub fn well_defined_error(
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

    pub fn well_defined_wrapping_from_verify_error(e: RuntimeError) -> RuntimeError {
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

// Display outputs a short placeholder; full machine-readable form is Runtime::display_error_json_string.
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
    fn from(store_or_infer_runtime_error_struct: RuntimeErrorStruct) -> Self {
        RuntimeError::StoreFactError(store_or_infer_runtime_error_struct)
    }
}

fn boxed_previous_error(previous_error: Option<RuntimeError>) -> Option<Box<RuntimeError>> {
    previous_error.map(Box::new)
}
