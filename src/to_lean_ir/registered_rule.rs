use crate::verify::rule_schema::{RuleFingerprint, RuleId};

use super::{ObjToLeanIR, ParamTypeToLeanIR};

#[derive(Clone, Debug)]
pub struct TypedBoundObjToLeanIR {
    pub object: ObjToLeanIR,
    pub param_type: ParamTypeToLeanIR,
}

#[derive(Clone, Debug)]
pub struct RegisteredRuleApplicationToLeanIR {
    pub rule_id: RuleId,
    pub semantic_fingerprint: RuleFingerprint,
    pub bindings: Vec<TypedBoundObjToLeanIR>,
    pub parameter_requirement_count: usize,
    pub premise_count: usize,
}
