use crate::prelude::*;

impl Runtime {
    /// If the fact string is in the known-facts cache, return the cached verification result.
    pub fn verify_fact_from_cache_using_display_string(&self, fact: &Fact) -> Option<StmtResult> {
        let key = fact.to_string();
        let (cache_ok, cache_line_file) = self.cache_known_facts_contains(&key);
        if cache_ok {
            Some(
                (FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                    fact.clone(),
                    key,
                    None,
                    Some(cache_line_file),
                    Vec::new(),
                ))
                .into(),
            )
        } else {
            None
        }
    }

    /// If check_type_nonempty is true and param_type is Obj(set), verifies that the set is nonempty and stores the fact.
    pub fn verify_param_type_nonempty_if_required(
        &mut self,
        param_type: &ParamType,
        check_type_nonempty: bool,
    ) -> Result<(), RuntimeError> {
        if !check_type_nonempty {
            return Ok(());
        }
        match param_type {
            ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => Ok(()),
            ParamType::Obj(param_set) => match param_set {
                Obj::FnSet(fn_set) => {
                    let ret_nonempty = IsNonemptySetFact::new(
                        fn_set.ret_set.as_ref().clone(),
                        default_line_file(),
                    )
                    .into();
                    self.verify_fact_well_defined_and_store_and_infer(
                        ret_nonempty,
                        &VerifyState::new(2, false),
                    )?;
                    Ok(())
                }
                Obj::SetBuilder(_) => Err(RuntimeError::from(RuntimeErrorStruct::new(
                    None,
                    "set builder param type is not supported yet in verify_param_type_nonempty_if_required"
                        .to_string(),
                    default_line_file(),
                    None,
                    vec![],
                ))),
                _ => {
                    let nonempty_fact =
                        IsNonemptySetFact::new(param_set.clone(), default_line_file()).into();
                    self.verify_fact_well_defined_and_store_and_infer(
                        nonempty_fact,
                        &VerifyState::new(0, false),
                    )?;
                    Ok(())
                }
            },
            ParamType::Struct(struct_obj) => {
                let is_nonempty_set =
                    IsNonemptySetFact::new(Obj::StructObj(struct_obj.clone()), default_line_file())
                        .into();
                self.verify_fact_well_defined_and_store_and_infer(
                    is_nonempty_set,
                    &VerifyState::new(0, false),
                )?;
                Ok(())
            }
        }
    }
}
