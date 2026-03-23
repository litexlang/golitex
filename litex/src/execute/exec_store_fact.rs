use super::Runtime;
use crate::error::ExecStmtError;
use crate::error::StoreFactError;
use crate::fact::{AtomicFact, ExistOrAndChainAtomicFact, Fact, OrAndChainAtomicFact};
use crate::infer::InferResult;
use crate::verify::VerifyState;

use crate::fact::AndChainAtomicFact;

impl<'a> Runtime<'a> {
    pub fn store_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: &Fact,
    ) -> Result<InferResult, StoreFactError> {
        self.runtime_context
            .top_level_env()
            .store_fact_by_ref(fact)?;

        self.runtime_context
            .top_level_env()
            .store_fact_to_cache_known_fact(fact.to_string(), fact.line_file())?;

        let infer_result = self
            .infer(fact)
            .map_err(|e| StoreFactError::new(format!("infer error: {}", e), Some(e.into())))?;
        Ok(infer_result)
    }

    pub fn store_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: &AndChainAtomicFact,
    ) -> Result<InferResult, StoreFactError> {
        self.runtime_context
            .top_level_env()
            .store_and_chain_atomic_fact_by_ref(fact)?;

        let line_file = fact.line_file();
        self.runtime_context
            .top_level_env()
            .store_fact_to_cache_known_fact(fact.to_string(), line_file)?;

        let infer_result = self
            .infer(&fact.to_fact())
            .map_err(|e| StoreFactError::new(format!("infer error: {}", e), Some(e.into())))?;
        Ok(infer_result)
    }

    pub fn store_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: &AtomicFact,
    ) -> Result<InferResult, StoreFactError> {
        self.runtime_context
            .top_level_env()
            .store_atomic_fact_by_ref(fact)?;

        let line_file = fact.line_file();
        self.runtime_context
            .top_level_env()
            .store_fact_to_cache_known_fact(fact.to_string(), line_file)?;

        let wrapped_fact = Fact::AtomicFact(fact.clone());
        let infer_result = self
            .infer(&wrapped_fact)
            .map_err(|e| StoreFactError::new(format!("infer error: {}", e), Some(e.into())))?;
        Ok(infer_result)
    }

    pub fn store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
    ) -> Result<InferResult, StoreFactError> {
        self.runtime_context
            .top_level_env()
            .store_exist_or_and_chain_atomic_fact(fact)?;

        let line_file = fact.line_file();
        self.runtime_context
            .top_level_env()
            .store_fact_to_cache_known_fact(fact.to_string(), line_file)?;

        let infer_result = self
            .infer_exist_or_and_chain_atomic_fact(fact)
            .map_err(|e| StoreFactError::new(format!("infer error: {}", e), Some(e.into())))?;
        Ok(infer_result)
    }

    pub fn store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
        &mut self,
        fact: &OrAndChainAtomicFact,
    ) -> Result<InferResult, StoreFactError> {
        self.runtime_context
            .top_level_env()
            .store_or_and_chain_atomic_fact(fact)?;

        let line_file = fact.line_file();
        self.runtime_context
            .top_level_env()
            .store_fact_to_cache_known_fact(fact.to_string(), line_file)?;

        let infer_result = self
            .infer_or_and_chain_atomic_fact(fact)
            .map_err(|e| StoreFactError::new(format!("infer error: {}", e), Some(e.into())))?;
        Ok(infer_result)
    }

    pub fn verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: &ExistOrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, ExecStmtError> {
        self.verify_exist_or_and_chain_atomic_fact_well_defined(fact, verify_state)?;
        self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(fact)
            .map_err(ExecStmtError::from)
    }

    pub fn verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: &OrAndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, ExecStmtError> {
        self.verify_or_and_chain_atomic_fact_well_defined(fact, verify_state)?;
        self.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(fact)
            .map_err(ExecStmtError::from)
    }

    pub fn verify_fact_well_defined_and_store_and_infer(
        &mut self,
        fact: &Fact,
        verify_state: &VerifyState,
    ) -> Result<InferResult, ExecStmtError> {
        self.verify_fact_well_defined(fact, verify_state)?;
        self.store_fact_without_well_defined_verified_and_infer(fact)
            .map_err(ExecStmtError::from)
    }
}
