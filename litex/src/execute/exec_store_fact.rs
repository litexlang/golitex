use crate::error::ExecError;
use crate::verify::VerifyState;
use crate::fact::Fact;
use super::Executor;
use crate::error::StoreFactError;

impl<'a> Executor<'a> {
    pub fn store_fact_without_well_defined_verified_and_infer(&mut self, fact: &Fact) -> Result<(), StoreFactError> {
        if let Some(env) = self.runtime_context.environments.last_mut() {
            env.store_fact(fact.clone())
        } else {
            Err(StoreFactError::new("no environment found"))
        }
    }

    pub fn verify_fact_well_defined_and_store_and_infer(&mut self, fact: &Fact, verify_state: &VerifyState) -> Result<(), ExecError> {
        self.verify_fact_well_defined(fact, verify_state)?;
        self.store_fact_without_well_defined_verified_and_infer(fact)?;
        Ok(())
    }
}
