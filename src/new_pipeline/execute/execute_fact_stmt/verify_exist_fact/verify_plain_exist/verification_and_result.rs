use crate::fact::PlainExistFact;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub struct VerifyPlainExistFactResult2 {
    pub fact: PlainExistFact,
    pub well_defined_proof: ExistFactWellDefinedProof2,
    pub searched_proof: PlainExistFactSearchedProof2,
}

pub enum PlainExistFactSearchedProof2 {
    ByCache(CacheSearchProof2),
    ByBuiltinRule(PlainExistFactSearchedProofByBuiltinRule2),
    ByKnownExistFact(PlainExistFactSearchedProofByKnownExistFact2),
    ByKnownForallFact(PlainExistFactSearchedProofByKnownForallFact2),
}

pub struct PlainExistFactSearchedProofByKnownExistFact2 {
    pub cite_fact_id: FactId,
    // If known-exist matching requires alpha-normalized string equality of the
    // full body, cite_fact_id alone is enough.
}

pub struct PlainExistFactSearchedProofByKnownForallFact2 {
    pub cite_fact_id: FactId,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_plain_exist_fact2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyPlainExistFactResult2, RuntimeError> {
        let well_defined_proof =
            self.verify_exist_fact_well_definedness2(fact, verify_state.clone())?;
        let searched_proof = self.search_plain_exist_fact_proof2(fact, verify_state)?;
        Ok(VerifyPlainExistFactResult2 {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_plain_exist_fact_proof2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<PlainExistFactSearchedProof2, RuntimeError> {
        if let Some(result) =
            self.search_plain_exist_fact_proof_by_cache2(fact, verify_state.clone())?
        {
            return Ok(PlainExistFactSearchedProof2::ByCache(result));
        }

        if let Some(result) =
            self.search_plain_exist_fact_proof_by_known_exist_fact2(fact, verify_state.clone())?
        {
            return Ok(PlainExistFactSearchedProof2::ByKnownExistFact(result));
        }

        if let Some(result) =
            self.search_plain_exist_fact_proof_by_builtin_rule2(fact, verify_state.clone())?
        {
            return Ok(PlainExistFactSearchedProof2::ByBuiltinRule(result));
        }

        if let Some(result) =
            self.search_plain_exist_fact_proof_by_known_forall_fact2(fact, verify_state)?
        {
            return Ok(PlainExistFactSearchedProof2::ByKnownForallFact(result));
        }

        todo!()
    }

    pub fn search_plain_exist_fact_proof_by_cache2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<Option<CacheSearchProof2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search plain exist by cache")
    }

    pub fn search_plain_exist_fact_proof_by_known_exist_fact2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<Option<PlainExistFactSearchedProofByKnownExistFact2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search plain exist by known exist fact")
    }

    pub fn search_plain_exist_fact_proof_by_builtin_rule2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<Option<PlainExistFactSearchedProofByBuiltinRule2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search plain exist by builtin rule")
    }

    pub fn search_plain_exist_fact_proof_by_known_forall_fact2(
        &mut self,
        fact: &PlainExistFact,
        verify_state: VerifyState2,
    ) -> Result<Option<PlainExistFactSearchedProofByKnownForallFact2>, RuntimeError> {
        let _ = (fact, verify_state);
        todo!("search plain exist by known forall fact")
    }
}
