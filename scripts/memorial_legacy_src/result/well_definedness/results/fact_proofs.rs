//! Top-level fact well-definedness proof results.

use crate::prelude::*;
use std::fmt;
use std::rc::Rc;

#[derive(Debug)]
pub enum SuccessVerifyFactWellDefinedProofResult {
    AtomicFact(Box<SuccessVerifyAtomicFactWellDefinedResult>),
    AndFact(Box<SuccessVerifyAndFactWellDefinedResult>),
    ChainFact(Box<SuccessVerifyChainFactWellDefinedResult>),
    OrFact(Box<SuccessVerifyOrFactWellDefinedResult>),
    ExistFact(Box<SuccessVerifyExistFactWellDefinedResult>),
    ForallFact(Box<SuccessVerifyForallFactWellDefinedResult>),
    ForallFactWithIff(Box<SuccessVerifyForallFactWithIffWellDefinedResult>),
    NotForallFact(Box<SuccessVerifyNotForallFactWellDefinedResult>),
}

pub struct SuccessVerifyFactObjectWellDefinedResult {
    pub argument_index: usize,
    pub source_object: Obj,
    pub result: Rc<SuccessVerifyObjWellDefinedResult>,
}

impl SuccessVerifyFactObjectWellDefinedResult {
    pub fn new(
        argument_index: usize,
        source_object: Obj,
        result: Rc<SuccessVerifyObjWellDefinedResult>,
    ) -> Self {
        Self {
            argument_index,
            source_object,
            result,
        }
    }
}

impl fmt::Debug for SuccessVerifyFactObjectWellDefinedResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyFactObjectWellDefinedResult")
            .field("argument_index", &self.argument_index)
            .field("source_object", &self.source_object.to_string())
            .field("result", &self.result)
            .finish()
    }
}
