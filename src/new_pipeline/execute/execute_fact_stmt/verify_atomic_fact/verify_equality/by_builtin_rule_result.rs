use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::prelude::*;

// Each equality builtin rule gets its own variant and payload struct.
pub enum EqualitySearchProofByBuiltinRule {
    TheyAreTheSame(EqualitySearchProofByTheyAreTheSame),
    Calculation(EqualitySearchProofByCalculation),
}

pub struct EqualitySearchProofByTheyAreTheSame {}

pub struct EqualitySearchProofByCalculation {}
