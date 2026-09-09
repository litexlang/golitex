use crate::fact::ExistFact;
use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub enum VerifyExistFactResult2 {
    Exist(VerifyPlainExistFactResult2),
    ExistUnique(VerifyExistUniqueFactResult2),
    NotExist(VerifyNotExistFactResult2),
}

impl Runtime {
    pub fn verify_exist_fact2(
        &mut self,
        fact: &ExistFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyExistFactResult2, RuntimeError> {
        match fact {
            ExistFact::PlainExistFact(spec) => Ok(VerifyExistFactResult2::Exist(
                self.verify_plain_exist_fact2(spec, verify_state)?,
            )),
            ExistFact::ExistUniqueFact(spec) => Ok(VerifyExistFactResult2::ExistUnique(
                self.verify_exist_unique_fact2(spec, verify_state)?,
            )),
            ExistFact::NotExistFact(spec) => Ok(VerifyExistFactResult2::NotExist(
                self.verify_not_exist_fact2(spec, verify_state)?,
            )),
        }
    }
}
