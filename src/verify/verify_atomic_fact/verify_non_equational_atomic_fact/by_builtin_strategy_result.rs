use crate::prelude::*;

pub enum NonEquationalAtomicFactSearchProofByBuiltinStrategy2 {
    PosAddPosIsPos(PosAddPosIsPosStrategySingleStep2),
}

pub struct PosAddPosIsPosStrategySingleStep2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}
