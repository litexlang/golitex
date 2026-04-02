use crate::prelude::*;
use std::collections::HashMap;
use std::result::Result;

impl Runtime {
    pub fn verify_exist_fact(
        &mut self,
        exist_fact: &ExistFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&Fact::ExistFact(exist_fact.clone()))
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_exist_fact_well_defined(exist_fact, verify_state) {
                return Err(VerifyError::new(
                    Fact::ExistFact(exist_fact.clone()),
                    String::new(),
                    exist_fact.line_file(),
                    Some(e.into()),
                ));
            }
        }

        let result = self.verify_exist_fact_with_known_exist_fact(exist_fact, exist_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        let result = self.verify_exist_fact_with_known_forall(exist_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    pub fn verify_exist_fact_with_known_exist_fact(
        &mut self,
        exist_fact: &ExistFact,
        known_exist_fact: &ExistFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        for environment in self.iter_environments_from_top() {
            let result = Self::verify_exist_fact_with_known_exist_fact_with_facts_in_environment(
                self,
                environment,
                exist_fact,
                known_exist_fact,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    pub fn verify_exist_fact_with_known_exist_fact_with_facts_in_environment(
        runtime: &Runtime,
        environment: &Environment,
        exist_fact: &ExistFact,
        known_exist_fact: &ExistFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(known_exist_facts) = environment.known_exist_facts.get(&known_exist_fact.key())
        {
            let target_string = Self::exist_fact_normalized_string(runtime, exist_fact)
                .map_err(|e| {
                    VerifyError::new(
                        Fact::ExistFact(exist_fact.clone()),
                        String::new(),
                        exist_fact.line_file(),
                        Some(e),
                    )
                })?;
            for known_fact in known_exist_facts.iter() {
                let known_string = Self::exist_fact_normalized_string(runtime, known_fact)
                    .map_err(|e| {
                        VerifyError::new(
                            Fact::ExistFact(exist_fact.clone()),
                            String::new(),
                            exist_fact.line_file(),
                            Some(e),
                        )
                    })?;
                if target_string == known_string {
                    return Ok(NonErrStmtExecResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_known_fact_source(
                            Fact::ExistFact(exist_fact.clone()),
                            InferResult::new(),
                            known_fact.to_string(),
                            Some(Fact::ExistFact(known_fact.clone())),
                            None,
                            Vec::new(),
                        ),
                    ));
                }
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn exist_fact_normalized_string(
        runtime: &Runtime,
        exist_fact: &ExistFact,
    ) -> Result<String, RuntimeError> {
        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        let mut normalized_params: Vec<ParamDefWithParamType> = Vec::new();
        let mut param_index: usize = 0;

        for param_def_with_type in exist_fact.params_def_with_type().iter() {
            let mut new_param_names: Vec<String> = Vec::new();
            for original_name in param_def_with_type.0.iter() {
                let normalized_name = format!("#{}", param_index);
                param_index += 1;

                param_to_arg_map.insert(
                    original_name.clone(),
                    Obj::Identifier(Identifier::new(normalized_name.clone())),
                );
                new_param_names.push(normalized_name);
            }

            let instantiated_param_type =
                runtime.inst_param_type(&param_def_with_type.1, &param_to_arg_map)?;
            normalized_params.push(ParamDefWithParamType(
                new_param_names,
                instantiated_param_type,
            ));
        }

        let instantiated_exist_fact = runtime.inst_exist_fact(exist_fact, &param_to_arg_map)?;

        let mut fact_strings: Vec<String> = Vec::new();
        for fact in instantiated_exist_fact.facts().iter() {
            let fact_as_fact = fact.from_ref_to_cloned_fact();
            fact_strings.push(fact_as_fact.to_string());
        }

        let mut params_string_parts: Vec<String> = Vec::new();
        for param_def_with_type in normalized_params.iter() {
            params_string_parts.push(format!(
                "{} {}",
                param_def_with_type.0.join(","),
                param_def_with_type.1
            ));
        }
        let params_string = params_string_parts.join("; ");
        let facts_string = fact_strings.join("; ");

        Ok(format!("{} || {}", params_string, facts_string))
    }
}
