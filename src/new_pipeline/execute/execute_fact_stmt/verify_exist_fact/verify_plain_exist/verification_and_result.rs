use crate::fact::PlainExistFact;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub struct VerifyPlainExistFactResult {
    pub fact: PlainExistFact,
    pub well_defined_proof: ExistFactWellDefinedProof,
    pub searched_proof: PlainExistFactSearchedProof,
}

pub enum PlainExistFactSearchedProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(PlainExistFactSearchedProofByBuiltinRule),
    ByKnownExistFact(PlainExistFactSearchedProofByKnownExistFact),
    ByKnownForallFact(PlainExistFactSearchedProofByKnownForallFact),
}

pub struct PlainExistFactSearchedProofByKnownExistFact {
    pub cite_fact_id: FactId,
    // If known-exist matching requires alpha-normalized string equality of the
    // full body, cite_fact_id alone is enough.
}

pub struct PlainExistFactSearchedProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

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
            self.search_plain_exist_fact_proof_by_cache(fact, verify_state.clone())?
        {
            return Ok(PlainExistFactSearchedProof::ByCache(result));
        }

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

    pub fn search_plain_exist_fact_proof_by_cache(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState,
    ) -> Result<Option<CacheSearchProof>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search plain exist by cache")
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
