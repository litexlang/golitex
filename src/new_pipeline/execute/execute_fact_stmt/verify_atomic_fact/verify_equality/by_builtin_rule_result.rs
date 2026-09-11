use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState2;

// Each equality builtin rule gets its own variant and payload struct.
pub enum EqualitySearchProofByBuiltinRule2 {
    TheyAreTheSame(EqualitySearchProofByTheyAreTheSame2),
    Calculation(EqualitySearchProofByCalculation2),
}

pub struct EqualitySearchProofByTheyAreTheSame2 {}

pub struct EqualitySearchProofByCalculation2 {}
