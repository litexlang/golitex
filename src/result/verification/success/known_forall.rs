//! Known universal-fact requirement and instantiation outcomes.

use crate::prelude::*;
use std::fmt;

pub struct KnownForallInstantiationItem {
    pub param: String,
    pub arg: String,
    /// Typed verifier output retained for compilers. `arg` remains the stable
    /// user-facing rendering used by existing diagnostics and JSON.
    pub arg_obj: Obj,
}

impl fmt::Debug for KnownForallInstantiationItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("KnownForallInstantiationItem")
            .field("param", &self.param)
            .field("arg", &self.arg)
            .finish()
    }
}

#[derive(Debug)]
pub struct SuccessVerifyKnownForallRequirementResult {
    pub stmt: Fact,
    pub result: Box<StmtResult>,
    pub kind: KnownForallRequirementKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KnownForallRequirementKind {
    ParameterType,
    Domain,
}

#[derive(Debug)]
pub struct SuccessInstantiateKnownForallResult {
    pub source_fact: Fact,
    pub source_fact_id: FactId,
    pub source_conclusion_location: ForallConclusionLocation,
    pub instantiation: Vec<KnownForallInstantiationItem>,
    pub requirements: Vec<SuccessVerifyKnownForallRequirementResult>,
}

impl KnownForallInstantiationItem {
    pub fn new(param: String, arg_obj: Obj) -> Self {
        KnownForallInstantiationItem {
            param,
            arg: arg_obj.to_string(),
            arg_obj,
        }
    }
}

impl SuccessVerifyKnownForallRequirementResult {
    pub fn new(stmt: Fact, result: StmtResult, kind: KnownForallRequirementKind) -> Self {
        SuccessVerifyKnownForallRequirementResult {
            stmt,
            result: Box::new(result),
            kind,
        }
    }
}

impl SuccessInstantiateKnownForallResult {
    pub fn new(
        source_fact: Fact,
        source_fact_id: FactId,
        source_conclusion_location: ForallConclusionLocation,
        instantiation: Vec<KnownForallInstantiationItem>,
        requirements: Vec<SuccessVerifyKnownForallRequirementResult>,
    ) -> Self {
        SuccessInstantiateKnownForallResult {
            source_fact,
            source_fact_id,
            source_conclusion_location,
            instantiation,
            requirements,
        }
    }
}
