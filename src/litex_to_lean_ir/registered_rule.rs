use crate::verify::rule_schema::{RuleFingerprint, RuleId};

use super::{LitexToLeanObjectIr, LitexToLeanParameterTypeIr};

#[derive(Clone, Debug)]
pub struct LitexToLeanTypedBoundObjectIr {
    pub object: LitexToLeanObjectIr,
    pub param_type: LitexToLeanParameterTypeIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanRegisteredRuleApplicationIr {
    pub rule_id: RuleId,
    pub semantic_fingerprint: RuleFingerprint,
    pub bindings: Vec<LitexToLeanTypedBoundObjectIr>,
}
