use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult2;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState2;

pub enum EqualitySearchProofByBuiltinStrategy2 {
    ExtremumEquality(ExtremumEqualityStrategySingleStep2),
    FiniteSetProductPointwiseEquality(FiniteSetProductPointwiseEqualityStrategySingleStep2),
    ModCongruence(ModCongruenceStrategySingleStep2),
}

pub struct ExtremumEqualityStrategySingleStep2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

pub struct FiniteSetProductPointwiseEqualityStrategySingleStep2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

pub struct ModCongruenceStrategySingleStep2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}
