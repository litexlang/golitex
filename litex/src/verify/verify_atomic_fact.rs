use crate::fact::{AtomicFact, EqualFact};
use crate::execute::Executor;
use crate::result::StmtUnknown;
use crate::error::VerifyError;
use crate::result::NonErrStmtResult;
use crate::result::FactVerifiedByBuiltinRules;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    pub fn verify_atomic_fact(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.verify_equal_fact(equal_fact, verify_state),
            _ => self.verify_non_equational_atomic_fact(atomic_fact, verify_state),
        }
    }
    
    fn verify_equal_fact(&mut self, equal_fact: &EqualFact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        let _ = verify_state;
        if equal_fact.left.two_objs_can_be_calculated_and_equal_by_calculation(&equal_fact.right) {
            Ok(NonErrStmtResult::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(equal_fact.to_string(), "calculation".to_string(), equal_fact.line_file_index)))
        } else {
            Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
        }
    }
}
