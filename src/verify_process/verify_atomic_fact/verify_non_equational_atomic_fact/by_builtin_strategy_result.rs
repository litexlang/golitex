pub enum NonEquationalAtomicFactSearchProofByBuiltinStrategy {
    PosAddPosIsPos(PosAddPosIsPosStrategySingleStep),
}

pub struct PosAddPosIsPosStrategySingleStep {
    pub requirement_facts: Vec<FactStmt>,
    pub proof_of_requirement_facts: Vec<NonEquationalAtomicFactSearchProofByBuiltinStrategy>,
}
