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

macro_rules! runtime_error_wrapper {
    ($($wrapper:ident => $variant:ident),* $(,)?) => {
        $(
            #[derive(Debug)]
            pub struct $wrapper(pub RuntimeErrorStruct);

            impl From<$wrapper> for RuntimeError {
                fn from(w: $wrapper) -> Self {
                    RuntimeError::$variant(w.0)
                }
            }
        )*
    };
}

runtime_error_wrapper! {
    ArithmeticRuntimeError => ArithmeticError,
    NewAtomicFactRuntimeError => NewAtomicFactError,
    StoreFactRuntimeError => StoreFactError,
    ParseRuntimeError => ParseError,
    WellDefinedRuntimeError => WellDefinedError,
    VerifyRuntimeError => VerifyError,
    UnknownRuntimeError => UnknownError,
    InferRuntimeError => InferError,
    NameAlreadyUsedRuntimeError => NameAlreadyUsedError,
    DefineParamsRuntimeError => DefineParamsError,
    InstantiateRuntimeError => InstantiateError,
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
                NewAtomicFactRuntimeError(RuntimeErrorStruct::new(
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
