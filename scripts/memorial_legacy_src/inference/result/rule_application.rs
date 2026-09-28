use super::InferRule;
use crate::prelude::*;

#[derive(Clone, Debug)]
pub struct SuccessInferPremiseResult {
    pub fact: Fact,
    pub fact_id: Option<FactId>,
}

#[derive(Clone, Debug)]
pub struct SuccessInferRuleApplicationResult {
    pub rule: InferRule,
    pub premises: Vec<SuccessInferPremiseResult>,
    pub conclusions: Vec<SuccessStoreFactResult>,
}
