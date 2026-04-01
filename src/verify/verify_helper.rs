use crate::prelude::*;

impl Runtime {
    /// If the fact string is in the known-facts cache, return the cached verification result.
    pub fn verify_fact_from_cache_using_display_string(
        &self,
        fact: &Fact,
    ) -> Option<NonErrStmtExecResult> {
        let key = fact.to_string();
        let (cache_ok, cache_line_file) = self.cache_known_facts_contains(&key);
        if cache_ok {
            Some(NonErrStmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_known_fact_source(
                    fact.clone(),
                    InferResult::new(),
                    key,
                    None,
                    Some(cache_line_file),
                    Vec::new(),
                ),
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
                    nonempty_fact,
                    &VerifyState::new(0, false),
                )?;
                Ok(())
            }
            ParamType::Family(_) => Err(ExecStmtError::new(
                None,
                "family param type is not supported yet in verify_param_type_nonempty_if_required"
                    .to_string(),
                None,
                vec![],
            )),
            ParamType::Struct(_) => Err(ExecStmtError::new(
                None,
                "struct param type is not supported yet in verify_param_type_nonempty_if_required"
                    .to_string(),
                None,
                vec![],
            )),
        }
    }
}
