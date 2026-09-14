use crate::fact::PlainExistFact;
use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

use super::verify_not_exist_fact_result::{
    VerifyNotExistFactResult,
    NotExistFactSearchedProof,
};

impl Runtime {
    pub fn verify_not_exist_fact(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<VerifyNotExistFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_exist_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_not_exist_fact_proof(fact, verify_state)?;
        Ok(VerifyNotExistFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_not_exist_fact_proof(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<NotExistFactSearchedProof, RuntimeError> {
        if let Some(result) =
            self.search_not_exist_fact_proof_by_demorgan_forall(fact, verify_state)?
        {
            return Ok(NotExistFactSearchedProof::ByDemorganForall(result));
        }

        todo!()
    }

    pub fn search_not_exist_fact_proof_by_demorgan_forall(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<Option<VerifyForallFactResult>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search not exist by demorgan forall")
    }
}
