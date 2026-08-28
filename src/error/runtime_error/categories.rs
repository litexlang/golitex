//! Typed constructors for runtime error categories.

use super::{RuntimeError, RuntimeErrorStruct};

#[derive(Debug)]
pub struct ArithmeticRuntimeError(pub RuntimeErrorStruct);

impl From<ArithmeticRuntimeError> for RuntimeError {
    fn from(w: ArithmeticRuntimeError) -> Self {
        RuntimeError::ArithmeticError(Box::new(w.0))
    }
}

#[derive(Debug)]
pub struct NewFactRuntimeError(pub RuntimeErrorStruct);

impl From<NewFactRuntimeError> for RuntimeError {
    fn from(w: NewFactRuntimeError) -> Self {
        RuntimeError::NewFactError(Box::new(w.0))
    }
}

#[derive(Debug)]
pub struct StoreFactRuntimeError(pub RuntimeErrorStruct);

impl From<StoreFactRuntimeError> for RuntimeError {
    fn from(w: StoreFactRuntimeError) -> Self {
        RuntimeError::StoreFactError(Box::new(w.0))
    }
}

#[derive(Debug)]
pub struct ParseRuntimeError(pub RuntimeErrorStruct);

impl From<ParseRuntimeError> for RuntimeError {
    fn from(w: ParseRuntimeError) -> Self {
        RuntimeError::ParseError(Box::new(w.0))
    }
}

#[derive(Debug)]
pub struct WellDefinedRuntimeError(pub RuntimeErrorStruct);

impl From<WellDefinedRuntimeError> for RuntimeError {
    fn from(w: WellDefinedRuntimeError) -> Self {
        RuntimeError::WellDefinedError(Box::new(w.0))
    }
}

#[derive(Debug)]
pub struct VerifyRuntimeError(pub RuntimeErrorStruct);

impl From<VerifyRuntimeError> for RuntimeError {
    fn from(w: VerifyRuntimeError) -> Self {
        RuntimeError::VerifyError(Box::new(w.0))
    }
}

#[derive(Debug)]
pub struct UnknownRuntimeError(pub RuntimeErrorStruct);

impl From<UnknownRuntimeError> for RuntimeError {
    fn from(w: UnknownRuntimeError) -> Self {
        RuntimeError::UnknownError(Box::new(w.0))
    }
}

#[derive(Debug)]
pub struct InferRuntimeError(pub RuntimeErrorStruct);

impl From<InferRuntimeError> for RuntimeError {
    fn from(w: InferRuntimeError) -> Self {
        RuntimeError::InferError(Box::new(w.0))
    }
}

#[derive(Debug)]
pub struct NameAlreadyUsedRuntimeError(pub RuntimeErrorStruct);

impl From<NameAlreadyUsedRuntimeError> for RuntimeError {
    fn from(w: NameAlreadyUsedRuntimeError) -> Self {
        RuntimeError::NameAlreadyUsedError(Box::new(w.0))
    }
}

#[derive(Debug)]
pub struct DefineParamsRuntimeError(pub RuntimeErrorStruct);

impl From<DefineParamsRuntimeError> for RuntimeError {
    fn from(w: DefineParamsRuntimeError) -> Self {
        RuntimeError::DefineParamsError(Box::new(w.0))
    }
}

#[derive(Debug)]
pub struct InstantiateRuntimeError(pub RuntimeErrorStruct);

impl From<InstantiateRuntimeError> for RuntimeError {
    fn from(w: InstantiateRuntimeError) -> Self {
        RuntimeError::InstantiateError(Box::new(w.0))
    }
}
