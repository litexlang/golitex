use crate::fact::PlainExistFact;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

use super::verify_plain_exist_fact_result::{
    VerifyPlainExistFactResult,
    PlainExistFactSearchedProof,
    PlainExistFactSearchedProofByKnownExistFact,
    PlainExistFactSearchedProofByKnownForallFact,
};

impl Runtime {
    pub fn verify_plain_exist_fact(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<VerifyPlainExistFactResult, RuntimeError> {
        let well_defined_proof =
            self.verify_exist_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = self.search_plain_exist_fact_proof(fact, verify_state)?;
        Ok(VerifyPlainExistFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_plain_exist_fact_proof(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<PlainExistFactSearchedProof, RuntimeError> {
        if let Some(result) =
            self.search_plain_exist_fact_proof_by_known_exist_fact(fact, verify_state.clone())?
        {
            return Ok(PlainExistFactSearchedProof::ByKnownExistFact(result));
        }

        if let Some(result) =
            self.search_plain_exist_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(PlainExistFactSearchedProof::ByBuiltinRule(result));
        }

        if let Some(result) =
            self.search_plain_exist_fact_proof_by_known_forall_fact(fact, verify_state)?
        {
            return Ok(PlainExistFactSearchedProof::ByKnownForallFact(result));
        }

        todo!()
    }

    pub fn search_plain_exist_fact_proof_by_known_exist_fact(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<Option<PlainExistFactSearchedProofByKnownExistFact>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search plain exist by known exist fact")
    }

    pub fn search_plain_exist_fact_proof_by_builtin_rule(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<Option<PlainExistFactSearchedProofByBuiltinRule>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search plain exist by builtin rule")
    }

    pub fn search_plain_exist_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<Option<PlainExistFactSearchedProofByKnownForallFact>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search plain exist by known forall fact")
    }
}
