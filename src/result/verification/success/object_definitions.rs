//! Object, tuple, Cartesian, and indexed-function definition outcomes.

use crate::prelude::*;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct ObjectDefinitionItem {
    pub name: String,
    pub facts: Vec<Fact>,
}

#[derive(Debug)]
pub struct SuccessVerifyObjectChoiceResult {
    pub groups: Vec<SuccessVerifyObjectChoiceGroupResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyObjectChoiceGroupResult {
    pub selected_type_facts: Vec<Fact>,
    pub nonempty_check: Option<Box<StmtResult>>,
}

impl SuccessVerifyObjectChoiceResult {
    pub fn new(groups: Vec<SuccessVerifyObjectChoiceGroupResult>) -> Self {
        SuccessVerifyObjectChoiceResult { groups }
    }
}

pub struct SuccessVerifyHaveObjEqualResult {
    pub type_checks: Vec<StmtResult>,
}

pub struct SuccessVerifyPreimageResult {
    pub source_membership_check: Box<StmtResult>,
}

pub struct SuccessVerifyTupleOrCartDimensionResult {
    pub positive_check: Box<StmtResult>,
    pub at_least_two_check: Box<StmtResult>,
}

/// Successful verification output shared by `have tuple` and `have cart`.
/// The value check is performed in the locally bound index environment, so
/// its recursive object result must be returned by that child layer before
/// the dimension checks are wrapped by the statement verifier.
pub struct SuccessVerifyTupleOrCartDefinitionResult {
    pub value_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub dimension: SuccessVerifyTupleOrCartDimensionResult,
}

pub struct SuccessVerifyIndexedFunctionDefinitionResult {
    pub well_definedness: SuccessVerifyIndexedFunctionDefinitionWellDefinedResult,
    pub bound_checks: Vec<StmtResult>,
    /// Parameter-membership and domain facts installed while checking the
    /// indexed body, with their temporary FactIds frozen before that local
    /// Runtime environment closes.
    pub assumption_infers: SuccessInferResult,
    pub return_check: Box<StmtResult>,
}

impl ObjectDefinitionItem {
    pub fn new(name: String, facts: Vec<Fact>) -> Self {
        ObjectDefinitionItem { name, facts }
    }
}
