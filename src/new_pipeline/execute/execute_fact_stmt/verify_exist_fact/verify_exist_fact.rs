use crate::new_pipeline::ast::fact::ExistFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_fact::result::{
    exist_fact_result_from_search_fail, exist_fact_result_from_success,
    exist_fact_result_from_wd_fail, ExistFactSearchedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyExistFactWellDefinedResult, VerifyState,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Split plain exist / exist! / not exist.
    // Each: WD (Success|Failed, same shape as atomic) → Builtin → known → known_forall.
    // Example (known): stored `exist x N st {x = 1}` proves the same goal.
    // Example (forall): known `forall a N: exist x N st {x = a}` proves `exist x N st {x = 2}`.
    pub fn verify_exist_fact(
        &mut self,
        fact: &ExistFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof =
            match self.verify_exist_fact_well_definedness(fact, verify_state.clone())? {
                VerifyExistFactWellDefinedResult::Success(proof) => proof,
                VerifyExistFactWellDefinedResult::Failed(reason) => {
                    return Ok(exist_fact_result_from_wd_fail(fact, reason));
                }
            };
        let Some(searched_proof) = self.search_exist_fact_proof(fact, verify_state)? else {
            return Ok(exist_fact_result_from_search_fail(fact, well_defined_proof));
        };
        Ok(exist_fact_result_from_success(
            fact,
            well_defined_proof,
            searched_proof,
        ))
    }

    // Builtin → known_exist → known_forall. Builtin is scaffold-only for now.
    fn search_exist_fact_proof(
        &mut self,
        fact: &ExistFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistFactSearchedProof>> {
        if let Some(proof) =
            self.search_exist_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_exist_fact_proof_by_known_exist_fact(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_exist_fact_proof_by_known_forall_fact(fact, verify_state)?
        {
            return Ok(Some(proof));
        }
        Ok(None)
    }

    fn search_exist_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &ExistFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistFactSearchedProof>> {
        Ok(None)
    }

    // Needs KnownFactMemory.known_exist (Env field authorization pending).
    fn search_exist_fact_proof_by_known_exist_fact(
        &mut self,
        _fact: &ExistFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistFactSearchedProof>> {
        Ok(None)
    }

    // Needs KnownForallConclusionMemory.by_exist (Env field authorization pending).
    fn search_exist_fact_proof_by_known_forall_fact(
        &mut self,
        _fact: &ExistFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistFactSearchedProof>> {
        if !verify_state.can_use_forall_fact {
            return Ok(None);
        }
        Ok(None)
    }
}
