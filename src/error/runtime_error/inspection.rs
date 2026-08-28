//! Runtime error trace, source-location, and display-label inspection.

use super::{RuntimeError, RuntimeErrorStruct};
use crate::prelude::*;

impl RuntimeError {
    pub fn trace_message(&self) -> String {
        let error = match self {
            RuntimeError::ArithmeticError(e) => e,
            RuntimeError::NewFactError(e) => e,
            RuntimeError::StoreFactError(e) => e,
            RuntimeError::ParseError(e) => e,
            RuntimeError::ExecStmtError(e) => e,
            RuntimeError::WellDefinedError(e) => e,
            RuntimeError::VerifyError(e) => e,
            RuntimeError::UnknownError(e) => e,
            RuntimeError::InferError(e) => e,
            RuntimeError::NameAlreadyUsedError(e) => e,
            RuntimeError::DefineParamsError(e) => e,
            RuntimeError::InstantiateError(e) => e,
        };
        if !error.msg.is_empty() {
            return error.msg.clone();
        }
        if let Some(previous_error) = error.previous_error.as_ref() {
            return previous_error.trace_message();
        }
        self.display_label().to_string()
    }

    pub fn with_execution_trace(mut self, trace: StatementExecutionTrace) -> Self {
        self.execution_trace_mut().execution_trace = Some(trace);
        self
    }

    pub fn execution_trace(&self) -> Option<&StatementExecutionTrace> {
        match self {
            RuntimeError::ArithmeticError(e) => e.execution_trace.as_ref(),
            RuntimeError::NewFactError(e) => e.execution_trace.as_ref(),
            RuntimeError::StoreFactError(e) => e.execution_trace.as_ref(),
            RuntimeError::ParseError(e) => e.execution_trace.as_ref(),
            RuntimeError::ExecStmtError(e) => e.execution_trace.as_ref(),
            RuntimeError::WellDefinedError(e) => e.execution_trace.as_ref(),
            RuntimeError::VerifyError(e) => e.execution_trace.as_ref(),
            RuntimeError::UnknownError(e) => e.execution_trace.as_ref(),
            RuntimeError::InferError(e) => e.execution_trace.as_ref(),
            RuntimeError::NameAlreadyUsedError(e) => e.execution_trace.as_ref(),
            RuntimeError::DefineParamsError(e) => e.execution_trace.as_ref(),
            RuntimeError::InstantiateError(e) => e.execution_trace.as_ref(),
        }
    }

    fn execution_trace_mut(&mut self) -> &mut RuntimeErrorStruct {
        match self {
            RuntimeError::ArithmeticError(e) => e,
            RuntimeError::NewFactError(e) => e,
            RuntimeError::StoreFactError(e) => e,
            RuntimeError::ParseError(e) => e,
            RuntimeError::ExecStmtError(e) => e,
            RuntimeError::WellDefinedError(e) => e,
            RuntimeError::VerifyError(e) => e,
            RuntimeError::UnknownError(e) => e,
            RuntimeError::InferError(e) => e,
            RuntimeError::NameAlreadyUsedError(e) => e,
            RuntimeError::DefineParamsError(e) => e,
            RuntimeError::InstantiateError(e) => e,
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
