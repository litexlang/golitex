use crate::new_pipeline::ast::fact::{AtomicFact, Fact};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum AtomicExceptEqualityFactSearchProofByBuiltinStrategy {
    PosAddPosIsPos(PosAddPosIsPosStrategySingleStep),
}

pub struct PosAddPosIsPosStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_builtin_strategy(
        &mut self,
        _fact: &AtomicFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinStrategy>> {
        Ok(None)
    }
}
