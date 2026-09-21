//! Object definition outcomes.

use crate::prelude::*;

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
    pub nonempty_check: Option<Box<VerifyFactResult>>,
}

impl SuccessVerifyObjectChoiceResult {
    pub fn new(groups: Vec<SuccessVerifyObjectChoiceGroupResult>) -> Self {
        SuccessVerifyObjectChoiceResult { groups }
    }
}

pub struct SuccessVerifyHaveObjEqualResult {
    pub type_checks: Vec<VerifyFactResult>,
}

pub struct SuccessVerifyPreimageResult {
    pub source_membership_check: Box<VerifyFactResult>,
}


impl ObjectDefinitionItem {
    pub fn new(name: String, facts: Vec<Fact>) -> Self {
        ObjectDefinitionItem { name, facts }
    }
}
