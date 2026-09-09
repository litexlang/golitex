//! Existential, universal, binder, and local fact well-definedness results.

use crate::prelude::*;
use std::fmt;

pub struct SuccessVerifyExistFactWellDefinedResult {
    pub statement: ExistFact,
    pub binder: SuccessVerifyFactBinderResult,
    pub body: Vec<SuccessVerifyLocalFactWellDefinedResult>,
}

pub struct SuccessVerifyForallFactWellDefinedResult {
    pub statement: ForallFact,
    pub binder: SuccessVerifyFactBinderResult,
    pub premises: Vec<SuccessVerifyLocalFactWellDefinedResult>,
    pub conclusions: Vec<SuccessVerifyLocalFactWellDefinedResult>,
}

pub struct SuccessVerifyFactBinderResult {
    pub parameter_groups: Vec<SuccessVerifyFactParameterGroupResult>,
}

pub struct SuccessVerifyFactParameterGroupResult {
    pub group_index: usize,
    pub parameter_type: ParamType,
    pub carrier: Option<SuccessVerifyChildObjWellDefinedResult>,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
}

pub struct SuccessVerifyLocalFactWellDefinedResult {
    pub proposition: Fact,
    pub well_definedness: Box<SuccessVerifyFactWellDefinedProofResult>,
    pub store: SuccessStoreFactResult,
}

pub struct SuccessVerifyForallFactWithIffWellDefinedResult {
    pub statement: ForallFactWithIff,
    pub forward: Box<SuccessVerifyFactWellDefinedProofResult>,
    pub reverse: Box<SuccessVerifyFactWellDefinedProofResult>,
}

pub struct SuccessVerifyNotForallFactWellDefinedResult {
    pub statement: NotForallFact,
    pub inner: Box<SuccessVerifyFactWellDefinedProofResult>,
}

impl fmt::Debug for SuccessVerifyExistFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyExistFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("binder", &self.binder)
            .field("body", &self.body)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyForallFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyForallFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("binder", &self.binder)
            .field("premises", &self.premises)
            .field("conclusions", &self.conclusions)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyFactBinderResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyFactBinderResult")
            .field("parameter_groups", &self.parameter_groups)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyFactParameterGroupResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyFactParameterGroupResult")
            .field("group_index", &self.group_index)
            .field("parameter_type", &self.parameter_type.to_string())
            .field("carrier", &self.carrier)
            .field("parameters", &self.parameters)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyLocalFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyLocalFactWellDefinedResult")
            .field("proposition", &self.proposition.to_string())
            .field("well_definedness", &self.well_definedness)
            .field("store", &self.store)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyForallFactWithIffWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyForallFactWithIffWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("forward", &self.forward)
            .field("reverse", &self.reverse)
            .finish()
    }
}

impl fmt::Debug for SuccessVerifyNotForallFactWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyNotForallFactWellDefinedResult")
            .field("statement", &self.statement.to_string())
            .field("inner", &self.inner)
            .finish()
    }
}
