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
        RuntimeErrorStruct::new_with_conflict(statement, msg, line_file, None, previous_error)
    }

    pub fn new_with_conflict(
        statement: Option<Stmt>,
        msg: String,
        line_file: LineFile,
        conflict_with: Option<ConflictMsg>,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        RuntimeErrorStruct {
            statement,
            msg,
            conflict_with,
            line_file,
            previous_error: boxed_previous_error(previous_error),
        }
    }

    pub fn new_with_msg_previous_error(msg: String, previous_error: Option<RuntimeError>) -> Self {
        RuntimeErrorStruct::new(None, msg, default_line_file(), previous_error)
    }
}

#[derive(Debug)]
pub enum RuntimeError {
    ArithmeticError(RuntimeErrorStruct),
    NewAtomicFactError(RuntimeErrorStruct),
    StoreFactError(RuntimeErrorStruct),
    ParseBlockError(ParseBlockError),
    ParsingError(ParsingError),
    ExecStmtError(ExecStmtError),
    WellDefinedError(WellDefinedError),
    VerifyError(VerifyError),
    UnknownError(UnknownError),
    InferError(InferError),
    NameAlreadyUsedError(NameAlreadyUsedError),
    DefineParamsError(DefineParamsError),
    InstantiateError(RuntimeErrorStruct),
}

impl std::error::Error for RuntimeError {}

impl RuntimeError {
    pub fn line_file(&self) -> LineFile {
        match self {
            RuntimeError::ArithmeticError(e) => e.line_file.clone(),
            RuntimeError::NewAtomicFactError(e) => e.line_file.clone(),
            RuntimeError::StoreFactError(e) => e.line_file.clone(),
            RuntimeError::ParseBlockError(e) => e.line_file(),
            RuntimeError::ParsingError(e) => e.line_file.clone(),
            RuntimeError::ExecStmtError(e) => {
                if let Some(stmt) = &e.stmt {
                    stmt.line_file()
                } else {
                    default_line_file()
                }
            }
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
            RuntimeError::ParseBlockError(e) => e.display_label(),
            RuntimeError::ParsingError(e) => e.display_label(),
            RuntimeError::ExecStmtError(e) => e.display_label(),
            RuntimeError::WellDefinedError(e) => e.display_label(),
            RuntimeError::VerifyError(e) => e.display_label(),
            RuntimeError::UnknownError(e) => e.display_label(),
            RuntimeError::InferError(e) => e.display_label(),
            RuntimeError::NameAlreadyUsedError(e) => e.display_label(),
            RuntimeError::DefineParamsError(e) => e.display_label(),
            RuntimeError::InstantiateError(_) => "InstantiateError",
        }
    }

    pub fn duplicate_used_name_error_msg_without_line_file(name: &str) -> String {
        format!(
            "name `{}` is already used, cannot be used again for other definitions",
            name
        )
    }
}

impl ParseBlockError {
    pub fn display_label(&self) -> &'static str {
        "ParseBlockError"
    }
}

impl ParsingError {
    pub fn display_label(&self) -> &'static str {
        "ParsingError"
    }
}

impl ExecStmtError {
    pub fn display_label(&self) -> &'static str {
        "ExecStmtError"
    }
}

impl WellDefinedError {
    pub fn display_label(&self) -> &'static str {
        "WellDefinedError"
    }
}

impl VerifyError {
    pub fn display_label(&self) -> &'static str {
        "VerifyError"
    }
}

impl UnknownError {
    pub fn display_label(&self) -> &'static str {
        "UnknownError"
    }
}

impl InferError {
    pub fn display_label(&self) -> &'static str {
        "InferError"
    }
}

impl NameAlreadyUsedError {
    pub fn display_label(&self) -> &'static str {
        "NameAlreadyUsedError"
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

#[derive(Debug)]
pub enum ParseBlockError {
    ExpectedIndent(usize, Rc<str>),
    UnexpectedIndent(usize, Rc<str>),
    InconsistentIndent(usize, Rc<str>),
    MissingBody(usize, Rc<str>),
    InvalidName(String),
    NameAlreadyUsed {
        name: String,
        name_already_used_on_line_file: LineFile,
        line_file: LineFile,
    },
}

impl std::error::Error for ParseBlockError {}

impl fmt::Display for ParseBlockError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_label())
    }
}

impl ParseBlockError {
    pub fn line_file(&self) -> LineFile {
        match self {
            ParseBlockError::ExpectedIndent(line, path) => (*line, path.clone()),
            ParseBlockError::UnexpectedIndent(line, path) => (*line, path.clone()),
            ParseBlockError::InconsistentIndent(line, path) => (*line, path.clone()),
            ParseBlockError::MissingBody(line, path) => (*line, path.clone()),
            ParseBlockError::InvalidName(_) => default_line_file(),
            ParseBlockError::NameAlreadyUsed { line_file, .. } => line_file.clone(),
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
    pub line_file: LineFile,
    pub previous_error: Option<Box<RuntimeError>>,
}

impl std::error::Error for ParsingError {}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_label())
    }
}

impl ParsingError {
    pub fn new(
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        ParsingError {
            msg,
            line_file,
            previous_error: boxed_previous_error(previous_error),
        }
    }
}

impl From<ParsingError> for RuntimeError {
    fn from(e: ParsingError) -> Self {
        RuntimeError::ParsingError(e)
    }
}

#[derive(Debug)]
pub struct ExecStmtError {
    pub stmt: Option<Stmt>,
    pub info: String,
    pub previous_error: Option<Box<RuntimeError>>,
    pub inside_results: Vec<NonErrStmtExecResult>,
}

impl std::error::Error for ExecStmtError {}

impl fmt::Display for ExecStmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_label())
    }
}

impl ExecStmtError {
    pub fn new(
        stmt: Option<Stmt>,
        info: String,
        previous_error: Option<RuntimeError>,
        inside_results: Vec<NonErrStmtExecResult>,
    ) -> Self {
        ExecStmtError {
            stmt,
            info,
            previous_error: boxed_previous_error(previous_error),
            inside_results,
        }
    }
    
    pub fn new_with_stmt(
        stmt: Stmt,
        info: String,
        previous_error: Option<RuntimeError>,
        inside_results: Vec<NonErrStmtExecResult>,
    ) -> Self {
        ExecStmtError {
            stmt: Some(stmt),
            info,
            previous_error: boxed_previous_error(previous_error),
            inside_results,
        }
    }

    pub fn with_message_and_cause(
        stmt: Stmt,
        message: String,
        cause: Option<RuntimeError>,
        inside_results: Vec<NonErrStmtExecResult>,
    ) -> Self {
        let line_file = stmt.line_file();
        let previous_error = if message.is_empty() {
            cause
        } else {
            let error_message_for_verify_unknown_error = message.clone();
            Some(RuntimeError::UnknownError(UnknownError::new(
                error_message_for_verify_unknown_error,
                line_file,
                None,
                cause,
            )))
        };
        ExecStmtError::new_with_stmt(stmt, message, previous_error, inside_results)
    }
}

impl From<ExecStmtError> for RuntimeError {
    fn from(e: ExecStmtError) -> Self {
        RuntimeError::ExecStmtError(e)
    }
}

#[derive(Debug)]
pub struct WellDefinedError {
    pub msg: String,
    pub previous_error: Option<Box<RuntimeError>>,
    pub line_file: LineFile,
}

impl std::error::Error for WellDefinedError {}

impl fmt::Display for WellDefinedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_label())
    }
}

impl WellDefinedError {
    pub fn new(
        msg: String,
        previous_error: Option<RuntimeError>,
        line_file: LineFile,
    ) -> Self {
        WellDefinedError {
            msg,
            previous_error: boxed_previous_error(previous_error),
            line_file,
        }
    }
}

impl RuntimeErrorStruct {
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
        )
    }

    pub fn into_well_defined_wrapping_new_atomic(self) -> WellDefinedError {
        let line_file = self.line_file.clone();
        let msg_for_well_defined_error = self.msg.clone();
        let wrapped_runtime_error = RuntimeError::NewAtomicFactError(self);
        WellDefinedError::new(
            msg_for_well_defined_error,
            Some(wrapped_runtime_error),
            line_file,
        )
    }
}

impl From<RuntimeErrorStruct> for WellDefinedError {
    fn from(new_atomic_fact_runtime_error_struct: RuntimeErrorStruct) -> Self {
        new_atomic_fact_runtime_error_struct.into_well_defined_wrapping_new_atomic()
    }
}

impl From<RuntimeErrorStruct> for RuntimeError {
    fn from(store_or_infer_runtime_error_struct: RuntimeErrorStruct) -> Self {
        RuntimeError::StoreFactError(store_or_infer_runtime_error_struct)
    }
}

impl From<WellDefinedError> for RuntimeError {
    fn from(e: WellDefinedError) -> Self {
        RuntimeError::WellDefinedError(e)
    }
}

#[derive(Debug)]
pub struct VerifyError {
    pub fact: Fact,
    pub msg: String,
    pub line_file: LineFile,
    pub previous_error: Option<Box<RuntimeError>>,
}

impl std::error::Error for VerifyError {}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_label())
    }
}

impl VerifyError {
    pub fn new(
        fact: Fact,
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        VerifyError {
            fact,
            msg,
            line_file,
            previous_error: boxed_previous_error(previous_error),
        }
    }
}

impl From<VerifyError> for RuntimeError {
    fn from(e: VerifyError) -> Self {
        RuntimeError::VerifyError(e)
    }
}

impl From<VerifyError> for WellDefinedError {
    fn from(e: VerifyError) -> Self {
        let line_file = e.line_file.clone();
        let msg_for_well_defined = if e.msg.is_empty() {
            "verify fact error:".to_string()
        } else {
            e.msg.clone()
        };
        WellDefinedError::new(
            msg_for_well_defined,
            Some(RuntimeError::VerifyError(e)),
            line_file,
        )
    }
}

#[derive(Debug)]
pub struct UnknownError {
    pub msg: String,
    pub line_file: LineFile,
    pub fact: Option<Fact>,
    pub previous_error: Option<Box<RuntimeError>>,
}

impl std::error::Error for UnknownError {}

impl fmt::Display for UnknownError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_label())
    }
}

impl UnknownError {
    pub fn new(
        msg: String,
        line_file: LineFile,
        fact: Option<Fact>,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        UnknownError {
            msg,
            line_file,
            fact,
            previous_error: boxed_previous_error(previous_error),
        }
    }

    pub fn verify_result_unknown(fact: Fact, previous_error: Option<RuntimeError>) -> Self {
        let line_file = fact.line_file();
        UnknownError {
            msg: String::new(),
            line_file,
            fact: Some(fact),
            previous_error: boxed_previous_error(previous_error),
        }
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
    pub line_file: LineFile,
    pub previous_error: Option<Box<RuntimeError>>,
}

impl std::error::Error for InferError {}

impl fmt::Display for InferError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_label())
    }
}

impl InferError {
    pub fn new(
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
    ) -> Self {
        InferError {
            msg,
            line_file,
            previous_error: boxed_previous_error(previous_error),
        }
    }
}

impl From<InferError> for RuntimeError {
    fn from(e: InferError) -> Self {
        RuntimeError::InferError(e)
    }
}

#[derive(Debug)]
pub struct NameAlreadyUsedError {
    pub name: String,
    pub name_already_used_on_line_file: LineFile,
    pub line_file: LineFile,
}

impl std::error::Error for NameAlreadyUsedError {}

impl fmt::Display for NameAlreadyUsedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_label())
    }
}

impl NameAlreadyUsedError {
    pub fn new(
        name: String,
        name_already_used_on_line_file: LineFile,
        line_file: LineFile,
    ) -> Self {
        NameAlreadyUsedError {
            name,
            name_already_used_on_line_file,
            line_file,
        }
    }
}

#[derive(Debug)]
pub struct DefineParamsError {
    pub msg: String,
    pub previous_error: Option<Box<RuntimeError>>,
    pub line_file: LineFile,
}

impl std::error::Error for DefineParamsError {}

impl fmt::Display for DefineParamsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.display_label())
    }
}

impl DefineParamsError {
    pub fn new(
        msg: String,
        previous_error: Option<RuntimeError>,
        line_file: LineFile,
    ) -> Self {
        DefineParamsError {
            msg,
            previous_error: boxed_previous_error(previous_error),
            line_file,
        }
    }

    pub fn display_label(&self) -> &'static str {
        "DefineParamsError"
    }
}

impl From<DefineParamsError> for RuntimeError {
    fn from(e: DefineParamsError) -> Self {
        RuntimeError::DefineParamsError(e)
    }
}

fn boxed_previous_error(previous_error: Option<RuntimeError>) -> Option<Box<RuntimeError>> {
    previous_error.map(Box::new)
}
