use crate::fact::ExistFact;
use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

use super::verify_exist_fact_result::VerifyExistFactResult;

impl Runtime {
    pub fn verify_exist_fact(
        &mut self,
        fact: &ExistFact,
        verify_state: VerifyState,
    ) -> Result<VerifyExistFactResult, RuntimeError> {
        match fact {
            ExistFact::PlainExistFact(spec) => Ok(VerifyExistFactResult::Exist(
                self.verify_plain_exist_fact(spec, verify_state)?,
            )),
            ExistFact::ExistUniqueFact(spec) => Ok(VerifyExistFactResult::ExistUnique(
                self.verify_exist_unique_fact(spec, verify_state)?,
            )),
            ExistFact::NotExistFact(spec) => Ok(VerifyExistFactResult::NotExist(
                self.verify_not_exist_fact(spec, verify_state)?,
            )),
        }
    }
}
