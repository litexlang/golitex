//! Set-builder conditions, function sets, and anonymous-function binders.

use crate::prelude::*;

#[derive(Debug)]
pub struct SuccessVerifySetBuilderConditionResult {
    pub condition_index: usize,
    pub well_definedness: Box<WellDefinedFactResult>,
    pub store: SuccessStoreFactResult,
}

impl SuccessVerifySetBuilderConditionResult {
    pub fn new(
        condition_index: usize,
        well_definedness: WellDefinedFactResult,
        store: SuccessStoreFactResult,
    ) -> Self {
        Self {
            condition_index,
            well_definedness: Box::new(well_definedness),
            store,
        }
    }
}

#[derive(Debug)]
pub struct SuccessVerifySetBuilderWellDefinedResult {
    pub parameter_carrier: SuccessVerifyChildObjWellDefinedResult,
    pub parameter: SuccessVerifyBinderPremiseResult,
    pub conditions: Vec<SuccessVerifySetBuilderConditionResult>,
}

#[derive(Debug)]
pub struct SuccessVerifyFunctionSetWellDefinedResult {
    pub parameter_carriers: Vec<SuccessVerifyChildObjWellDefinedResult>,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
    pub domains: Vec<SuccessVerifyBinderPremiseResult>,
    pub return_carrier: SuccessVerifyChildObjWellDefinedResult,
}

#[derive(Debug)]
pub struct SuccessVerifyAnonymousFunctionWellDefinedResult {
    pub parameter_carriers: Vec<SuccessVerifyChildObjWellDefinedResult>,
    pub parameters: Vec<SuccessVerifyBinderPremiseResult>,
    pub domains: Vec<SuccessVerifyBinderPremiseResult>,
    pub return_carrier: SuccessVerifyChildObjWellDefinedResult,
    pub body: SuccessVerifyChildObjWellDefinedResult,
    pub body_membership: SuccessVerifyObjTargetRequirementResult,
}
