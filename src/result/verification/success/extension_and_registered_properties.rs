//! Extension and registered predicate-property proof outcomes.

use crate::prelude::*;
use std::fmt;

#[derive(Debug)]
pub struct SuccessVerifyByExtensionResult {
    pub left: String,
    pub right: String,
    pub prove_goal: String,
    pub left_to_right_subset: String,
    pub right_to_left_subset: String,
    pub proof_steps: Vec<StmtResult>,
    pub left_to_right_check: Box<VerifyFactResult>,
    pub right_to_left_check: Box<VerifyFactResult>,
}

pub struct SuccessVerifyByPropRegistrationResult {
    pub registration_type: String,
    pub prop_name: String,
    pub forall_fact: ForallFact,
    pub assumption_infers: SuccessInferResult,
    pub proof_steps: Vec<StmtResult>,
    /// The complete recursive result returned by `verify_forall_fact`, not a
    /// flattened copy of its individual conclusions.
    pub forall_check: Box<VerifyFactResult>,
}

impl SuccessVerifyByExtensionResult {
    pub fn new(
        left: String,
        right: String,
        prove_goal: String,
        left_to_right_subset: String,
        right_to_left_subset: String,
        proof_steps: Vec<StmtResult>,
        left_to_right_check: VerifyFactResult,
        right_to_left_check: VerifyFactResult,
    ) -> Self {
        SuccessVerifyByExtensionResult {
            left,
            right,
            prove_goal,
            left_to_right_subset,
            right_to_left_subset,
            proof_steps,
            left_to_right_check: Box::new(left_to_right_check),
            right_to_left_check: Box::new(right_to_left_check),
        }
    }
}

impl SuccessVerifyByPropRegistrationResult {
    pub fn new(
        registration_type: String,
        prop_name: String,
        forall_fact: ForallFact,
        assumption_infers: SuccessInferResult,
        proof_steps: Vec<StmtResult>,
        forall_check: VerifyFactResult,
    ) -> Self {
        SuccessVerifyByPropRegistrationResult {
            registration_type,
            prop_name,
            forall_fact,
            assumption_infers,
            proof_steps,
            forall_check: Box::new(forall_check),
        }
    }
}

impl fmt::Debug for SuccessVerifyByPropRegistrationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("SuccessVerifyByPropRegistrationResult")
            .field("registration_type", &self.registration_type)
            .field("prop_name", &self.prop_name)
            .field("forall_fact", &self.forall_fact.to_string())
            .field("assumption_infers", &self.assumption_infers)
            .field("proof_steps", &self.proof_steps)
            .field("forall_check", &self.forall_check)
            .finish()
    }
}
