use crate::fact::InFact;
use crate::errors::VerifyFactError;
use crate::execute::Executor;
use crate::keywords::R;
use crate::obj::Obj;
use crate::result::StmtResult;
use crate::result::FactVerifiedByBuiltinRules;
use crate::result::StmtUnknown;

impl<'a> Executor<'a> {
    pub(crate) fn verify_in_fact(&self, in_fact: &InFact) -> Result<StmtResult, VerifyFactError> {
        match (&in_fact.element, &in_fact.set) {
            (Obj::Number(num), Obj::RObj(_)) => {
                self.verify_number_in_standard_number_set(&num.value, R, in_fact.line_file_index)
            }
            _ => Ok(StmtResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    fn verify_number_in_standard_number_set(
        &self,
        num: &str,
        set: &str,
        line_file_index: Option<(usize, usize)>,
    ) -> Result<StmtResult, VerifyFactError> {
        let _ = self;
        match set {
            R => {
                let fact_str = format!("{} in R", num);
                Ok(StmtResult::FactVerifiedByBuiltinRules(
                    FactVerifiedByBuiltinRules::new(fact_str, "number in R".to_string(), line_file_index),
                ))
            }
            _ => Ok(StmtResult::StmtUnknown(StmtUnknown::new())),
        }
    }
}