use crate::error::RuntimeError;
use crate::fact::Fact;
use crate::inference::InferReason;
use crate::result::{
    StmtResult, SuccessFactStmtResult, SuccessStoreFactResult, VerifyFactResult,
};
use crate::runtime::Runtime;
use crate::verification::VerifyState;
use std::result::Result;

impl Runtime {
    pub fn execute_submitted_fact(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        let verification = self.verify_fact_or_error(fact, &VerifyState::initial())?;
        let VerifyFactResult::Verified(verification) = verification else {
            unreachable!("verify_fact_or_error cannot return an unknown fact")
        };
        let infer_result = self.store_without_well_defined_verification_and_infer(fact.clone())?;
        let mut store = SuccessStoreFactResult::new(fact.clone(), infer_result);
        store.fact_id = self.known_fact_id_for_fact(fact)?;
        Ok(SuccessFactStmtResult::verified(verification, store).into())
    }

    pub fn execute_fact_with_trust(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.store_fact_with_trust_and_infer_with_reason(
            fact.clone(),
            InferReason::StatementWithVerification,
        )?;

        Ok(SuccessFactStmtResult::trusted(fact.clone(), infer_result).into())
    }
}
