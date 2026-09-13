use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

// Each equality builtin rule gets its own variant and payload struct.
pub enum EqualitySearchProofByBuiltinRule {
    TheyAreTheSame(EqualitySearchProofByTheyAreTheSame),
    Calculation(EqualitySearchProofByCalculation),
}

pub struct EqualitySearchProofByTheyAreTheSame {}

pub struct EqualitySearchProofByCalculation {}
