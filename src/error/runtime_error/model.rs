//! Runtime error category and shared diagnostic payload.

use crate::prelude::*;

#[derive(Debug)]
pub enum RuntimeError {
    ArithmeticError(Box<RuntimeErrorStruct>),
    NewFactError(Box<RuntimeErrorStruct>),
    StoreFactError(Box<RuntimeErrorStruct>),
    ParseError(Box<RuntimeErrorStruct>),
    ExecStmtError(Box<RuntimeErrorStruct>),
    WellDefinedError(Box<RuntimeErrorStruct>),
    VerifyError(Box<RuntimeErrorStruct>),
    UnknownError(Box<RuntimeErrorStruct>),
    InferError(Box<RuntimeErrorStruct>),
    NameAlreadyUsedError(Box<RuntimeErrorStruct>),
    DefineParamsError(Box<RuntimeErrorStruct>),
    InstantiateError(Box<RuntimeErrorStruct>),
}

#[derive(Debug)]
pub struct RuntimeErrorStruct {
    pub statement: Option<Stmt>,
    pub msg: String,
    pub line_file: LineFile,
    pub previous_error: Option<Box<RuntimeError>>,
    pub inside_results: Vec<StmtResult>,
    pub output: Box<RuntimeErrorOutput>,
}
