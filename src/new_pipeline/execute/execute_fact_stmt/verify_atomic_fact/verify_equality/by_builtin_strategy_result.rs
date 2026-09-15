use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

pub enum EqualitySearchProofByBuiltinStrategy {
    ExtremumEquality(ExtremumEqualityStrategySingleStep),
    FiniteSetProductPointwiseEquality(FiniteSetProductPointwiseEqualityStrategySingleStep),
    ModCongruence(ModCongruenceStrategySingleStep),
}

pub struct ExtremumEqualityStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct FiniteSetProductPointwiseEqualityStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct ModCongruenceStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
