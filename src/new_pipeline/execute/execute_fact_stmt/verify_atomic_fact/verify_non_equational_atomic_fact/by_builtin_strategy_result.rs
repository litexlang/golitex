use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult2;

pub enum NonEquationalAtomicFactSearchProofByBuiltinStrategy2 {
    PosAddPosIsPos(PosAddPosIsPosStrategySingleStep2),
}

pub struct PosAddPosIsPosStrategySingleStep2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}
