//! Parameter requirement verification outcomes.

use crate::prelude::*;

#[derive(Debug)]
pub struct SuccessVerifyArgsSatisfyParamDefResult {
    pub checks: Vec<VerifyFactResult>,
    pub infers: SuccessInferResult,
}

#[derive(Debug)]
pub struct UnknownVerifyArgsSatisfyParamDefResult {
    pub cause: Box<VerifyFactResult>,
}

#[derive(Debug)]
pub enum VerifyArgsSatisfyParamDefResult {
    Success(Box<SuccessVerifyArgsSatisfyParamDefResult>),
    Unknown(Box<UnknownVerifyArgsSatisfyParamDefResult>),
}

impl VerifyArgsSatisfyParamDefResult {
    pub fn success(checks: Vec<VerifyFactResult>, infers: SuccessInferResult) -> Self {
        Self::Success(Box::new(SuccessVerifyArgsSatisfyParamDefResult {
            checks,
            infers,
        }))
    }

    pub fn unknown(cause: VerifyFactResult) -> Self {
        Self::Unknown(Box::new(UnknownVerifyArgsSatisfyParamDefResult {
            cause: Box::new(cause),
        }))
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown(_))
    }

    pub fn success_result(&self) -> Option<&SuccessVerifyArgsSatisfyParamDefResult> {
        match self {
            Self::Success(result) => Some(result),
            Self::Unknown(_) => None,
        }
    }

    pub fn into_success(self) -> Option<SuccessVerifyArgsSatisfyParamDefResult> {
        match self {
            Self::Success(result) => Some(*result),
            Self::Unknown(_) => None,
        }
    }

    pub fn into_unknown_cause(self) -> Option<VerifyFactResult> {
        match self {
            Self::Success(_) => None,
            Self::Unknown(result) => Some(*result.cause),
        }
    }
}
