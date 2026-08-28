//! Successful witness construction outcomes.

use crate::prelude::*;

pub struct SuccessWitnessExistFactResult {
    pub statement: WitnessExistFact,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyWitnessExistResult>,
}

pub struct SuccessWitnessAtomicFactResult {
    pub statement: WitnessAtomicFact,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyWitnessAtomicFactResult>,
}

pub struct SuccessWitnessNonemptySetResult {
    pub statement: WitnessNonemptySet,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyWitnessNonemptySetResult>,
}

pub struct SuccessVerifyWitnessNonemptySetResult {
    pub proof_steps: Vec<StmtResult>,
    pub nonempty_check: Box<StmtResult>,
}

pub enum SuccessWitnessStmtResult {
    WitnessExistFact(Box<SuccessWitnessExistFactResult>),
    WitnessAtomicFact(Box<SuccessWitnessAtomicFactResult>),
    WitnessNonemptySet(Box<SuccessWitnessNonemptySetResult>),
}
