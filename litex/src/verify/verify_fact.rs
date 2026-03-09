use crate::fact::Fact;
use crate::stmt_result::StmtResult;
use crate::errors::VerifyFactError;
use crate::executor::Executor;

impl<'a> Executor<'a> {
    pub fn verify_fact(&self, fact: &Fact) -> Result<StmtResult, VerifyFactError> {
        match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact(atomic_fact),
            _ => Err(VerifyFactError::new("verify_fact: NOT IMPLEMENTED YET", vec![], None)),
        }
    }
}
