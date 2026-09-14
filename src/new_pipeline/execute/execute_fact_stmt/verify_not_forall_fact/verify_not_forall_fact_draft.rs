use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

use super::verify_not_forall_fact_result::{
    VerifyNotForallFactResult,
    NotForallFactSearchedProof,
};

impl Runtime {
    pub fn verify_not_forall_fact(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> Result<VerifyNotForallFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_not_forall_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_not_forall_fact_proof(fact, verify_state)?;
        Ok(VerifyNotForallFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_not_forall_fact_proof(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> Result<NotForallFactSearchedProof, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("not forall search routes not implemented yet")
    }
}
