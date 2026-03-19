use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::error::ExecStmtError;
use crate::execute::Executor;
use crate::fact::{AtomicFact, Fact, IsNonemptySetFact};
use crate::stmt::parameter_def::ParamType;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    /// If check_type_nonempty is true and param_type is Obj(set), verifies that the set is nonempty and stores the fact.
    pub fn verify_param_type_nonempty_if_required(&mut self, param_type: &ParamType, check_type_nonempty: bool) -> Result<(), ExecStmtError> {
        if !check_type_nonempty {
            return Ok(());
        }
        match param_type {
            ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => Ok(()),
            ParamType::Obj(param_set) => {
                let nonempty_fact = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                    param_set.clone(),
                    DEFAULT_LINE_FILE.clone(),
                )));
                self.verify_fact_well_defined_and_store_and_infer(&nonempty_fact, &VerifyState::new(0, false))?;
                Ok(())
            }
        }
    }
}
