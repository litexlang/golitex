use crate::atomic_fact::{AtomicFact, EqualFact};
use crate::executor::Executor;
use crate::stmt_unknown::StmtUnknown;
use crate::errors::VerifyFactError;
use crate::stmt_success::StmtSuccess;
use crate::stmt_result::StmtResult;
use crate::stmt_success::FactVerifiedByBuiltinRules;

impl<'a> Executor<'a> {
    pub fn verify_atomic_fact(&self, atomic_fact: &AtomicFact) -> Result<StmtResult, VerifyFactError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.verify_equal_fact(equal_fact),
            AtomicFact::InFact(in_fact) => self.verify_in_fact(in_fact),
            _ => Err(VerifyFactError::new("verify_atomic_fact: NOT IMPLEMENTED YET", vec![], None)),
        }
    }

    fn verify_equal_fact(&self, equal_fact: &EqualFact) -> Result<StmtResult, VerifyFactError> {
        if equal_fact.left.two_objs_can_be_calculated_and_equal_by_calculation(&equal_fact.right) {
            Ok(StmtResult::StmtSuccess(StmtSuccess::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(equal_fact.to_string(), "calculation".to_string(), equal_fact.line_file_index))))
        } else {
            Ok(StmtResult::StmtUnknown(StmtUnknown::new()))
        }
    }
}
