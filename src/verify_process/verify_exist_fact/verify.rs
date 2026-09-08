use crate::prelude::*;

impl Runtime {
    pub fn verify_exist_fact(
        &mut self,
        fact: &ExistFactEnum,
        verify_state: VerifyState,
    ) -> Result<VerifyExistFactResult, RuntimeError> {
        match fact {
            ExistFactEnum::ExistFact(spec) => Ok(VerifyExistFactResult::Exist(
                self.verify_plain_exist_fact(spec, verify_state)?,
            )),
            ExistFactEnum::ExistUniqueFact(spec) => Ok(VerifyExistFactResult::ExistUnique(
                self.verify_exist_unique_fact(spec, verify_state)?,
            )),
            ExistFactEnum::NotExistFact(spec) => Ok(VerifyExistFactResult::NotExist(
                self.verify_not_exist_fact(spec, verify_state)?,
            )),
        }
    }
}
