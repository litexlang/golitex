use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::error::ExecStmtError;
use crate::execute::Runtime;
use crate::fact::{AtomicFact, Fact, IsNonemptySetFact};
use crate::infer::InferResult;
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult};
use crate::stmt::parameter_def::ParamType;
use crate::verify::VerifyState;

impl Runtime {
    /// If the fact string is in the known-facts cache, return the cached verification result.
    pub fn verify_fact_from_cache_using_display_string(
        &self,
        fact: &Fact,
    ) -> Option<NonErrStmtExecResult> {
        let key = fact.to_string();
        let (cache_ok, cache_line_file) = self.runtime_context.cache_known_facts_contains(&key);
        if cache_ok {
            Some(NonErrStmtExecResult::FactVerifiedByFact(
                FactVerifiedByFact::new(fact.clone(), key, InferResult::new(), cache_line_file),
            ))
        } else {
            None
        }
    }

    /// If check_type_nonempty is true and param_type is Obj(set), verifies that the set is nonempty and stores the fact.
    pub fn verify_param_type_nonempty_if_required(
        &mut self,
        param_type: &ParamType,
        check_type_nonempty: bool,
    ) -> Result<(), ExecStmtError> {
        if !check_type_nonempty {
            return Ok(());
        }
        match param_type {
            ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => Ok(()),
            ParamType::Obj(param_set) => {
                let nonempty_fact = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(
                    IsNonemptySetFact::new(param_set.clone(), DEFAULT_LINE_FILE.clone()),
                ));
                self.verify_fact_well_defined_and_store_and_infer(
                    &nonempty_fact,
                    &VerifyState::new(0, false),
                )?;
                Ok(())
            }
        }
    }
}
