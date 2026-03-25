use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::environment::KnownForallFactParamsAndDom;
use crate::error::VerifyError;
use crate::execute::Runtime;
use crate::fact::{ExistOrAndChainAtomicFact, Fact, ForallFact, OrFact};
use crate::infer::InferResult;
use crate::obj::Obj;
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult, StmtUnknown};
use crate::stmt::parameter_def::ParamDefWithParamType;
use crate::verify::VerifyState;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

impl<'a> Runtime<'a> {
    pub fn verify_or_fact_with_known_forall(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(fact_verified) =
            self.try_verify_or_fact_with_known_forall_facts_in_envs(or_fact, verify_state)?
        {
            return Ok(NonErrStmtExecResult::FactVerifiedByFact(fact_verified));
        }
        if let Some(fact_verified) =
            self.try_verify_or_fact_with_known_forall_facts_in_builtin_env(or_fact, verify_state)?
        {
            return Ok(NonErrStmtExecResult::FactVerifiedByFact(fact_verified));
        }
        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn get_matched_or_fact_in_known_forall_fact_in_envs(
        &self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_or_fact: &OrFact,
    ) -> Result<
        (
            (usize, usize),
            Option<HashMap<String, Obj>>,
            Option<(OrFact, Rc<KnownForallFactParamsAndDom>)>,
        ),
        VerifyError,
    > {
        let lookup_key = given_or_fact.key();

        let envs_count = self.runtime_context.environment_stack.len();
        for i in iterate_from_env_index..envs_count {
            let env = &self.runtime_context.environment_stack[envs_count - 1 - i];
            if let Some(known_forall_facts_in_env) =
                env.known_or_facts_in_forall_facts.get(lookup_key.as_str())
            {
                let known_forall_facts_count = known_forall_facts_in_env.len();
                for j in iterate_from_known_forall_fact_index..known_forall_facts_count {
                    let current_known_forall =
                        &known_forall_facts_in_env[known_forall_facts_count - 1 - j];
                    let fact_args_in_known_forall = current_known_forall.0.get_args_from_fact();
                    let given_fact_args = given_or_fact.get_args_from_fact();
                    let match_result =
                        Self::match_args_in_fact_in_known_forall_fact_with_given_args(
                            &fact_args_in_known_forall,
                            &given_fact_args,
                        )?;
                    if let Some(arg_map) = match_result {
                        return Ok(((i, j), Some(arg_map), Some(current_known_forall.clone())));
                    }
                }
            }
        }

        Ok((DEFAULT_LINE_FILE, None, None))
    }

    fn get_matched_or_fact_in_known_forall_fact_in_builtin_env(
        &self,
        iterate_from_known_forall_fact_index: usize,
        given_or_fact: &OrFact,
    ) -> Result<
        (
            usize,
            Option<HashMap<String, Obj>>,
            Option<(OrFact, Rc<KnownForallFactParamsAndDom>)>,
        ),
        VerifyError,
    > {
        let lookup_key = given_or_fact.key();
        let builtin_env = &self.runtime_context.builtin_environment;

        if let Some(known_forall_facts_in_env) = builtin_env
            .known_or_facts_in_forall_facts
            .get(lookup_key.as_str())
        {
            let known_forall_facts_count = known_forall_facts_in_env.len();
            for j in iterate_from_known_forall_fact_index..known_forall_facts_count {
                let current_known_forall =
                    &known_forall_facts_in_env[known_forall_facts_count - 1 - j];
                let fact_args_in_known_forall = current_known_forall.0.get_args_from_fact();
                let given_fact_args = given_or_fact.get_args_from_fact();
                let match_result = Self::match_args_in_fact_in_known_forall_fact_with_given_args(
                    &fact_args_in_known_forall,
                    &given_fact_args,
                )?;
                if let Some(arg_map) = match_result {
                    return Ok((j, Some(arg_map), Some(current_known_forall.clone())));
                }
            }
        }

        Ok((0, None, None))
    }

    fn try_verify_or_fact_with_known_forall_facts_in_envs(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactVerifiedByFact>, VerifyError> {
        let mut iterate_from_env_index = 0;
        let mut iterate_from_known_forall_fact_index = 0;

        loop {
            let result = self.get_matched_or_fact_in_known_forall_fact_in_envs(
                iterate_from_env_index,
                iterate_from_known_forall_fact_index,
                or_fact,
            )?;
            let ((i, j), arg_map_opt, known_forall_opt) = result;
            match (arg_map_opt, known_forall_opt) {
                (Some(arg_map), Some((or_fact_in_known_forall, forall_rc))) => {
                    if let Some(fact_verified) = self
                        .verify_or_fact_args_satisfy_forall_requirements(
                            &or_fact_in_known_forall,
                            &forall_rc,
                            arg_map,
                            or_fact,
                            verify_state,
                        )?
                    {
                        return Ok(Some(fact_verified));
                    }
                    iterate_from_env_index = i;
                    iterate_from_known_forall_fact_index = j + 1;
                }
                _ => return Ok(None),
            }
        }
    }

    fn try_verify_or_fact_with_known_forall_facts_in_builtin_env(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactVerifiedByFact>, VerifyError> {
        let mut known_fact_index_in_builtin = 0;

        loop {
            let result = self.get_matched_or_fact_in_known_forall_fact_in_builtin_env(
                known_fact_index_in_builtin,
                or_fact,
            )?;
            match result {
                (j, Some(arg_map), Some((or_fact_in_known_forall, forall_rc))) => {
                    if let Some(fact_verified) = self
                        .verify_or_fact_args_satisfy_forall_requirements(
                            &or_fact_in_known_forall,
                            &forall_rc,
                            arg_map,
                            or_fact,
                            verify_state,
                        )?
                    {
                        return Ok(Some(fact_verified));
                    }
                    known_fact_index_in_builtin = j + 1;
                }
                _ => return Ok(None),
            }
        }
    }

    fn verify_or_fact_args_satisfy_forall_requirements(
        &mut self,
        or_fact_in_known_forall: &OrFact,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        arg_map: HashMap<String, Obj>,
        given_or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactVerifiedByFact>, VerifyError> {
        let param_names = ParamDefWithParamType::collect_param_names(&known_forall.params_def);

        if !param_names
            .iter()
            .all(|param_name| arg_map.contains_key(param_name))
        {
            return Ok(None);
        }

        let mut args_for_params: Vec<Obj> = Vec::new();

        for param_name in param_names.iter() {
            let obj = match arg_map.get(param_name) {
                Some(v) => v,
                None => return Ok(None),
            };

            args_for_params.push(obj.clone());
        }

        for (key, obj) in arg_map.iter() {
            if param_names.contains(key) {
                continue;
            } else {
                if key != &obj.to_string() {
                    return Ok(None);
                }
            }
        }

        let args_satisfy_param_types =
            ParamDefWithParamType::facts_for_args_satisfy_param_def_with_type_vec(
                &known_forall.params_def,
                &args_for_params,
            )
            .map_err(|e| {
                VerifyError::new(
                    Fact::OrFact(given_or_fact.clone()),
                    Some(e),
                )
            })?;

        for fact in args_satisfy_param_types.iter() {
            let result = self.verify_atomic_fact(fact, verify_state)?;
            if result.is_unknown() {
                return Ok(None);
            }
        }

        let param_to_arg_map = match ParamDefWithParamType::param_def_params_to_arg_map(
            &known_forall.params_def,
            &arg_map,
        ) {
            Some(m) => m,
            None => return Ok(None),
        };

        for dom_fact in known_forall.dom.iter() {
            let instantiated_dom_fact = dom_fact.instantiate(&param_to_arg_map);
            let result =
                self.verify_exist_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)?;
            if result.is_unknown() {
                return Ok(None);
            }
        }

        let verified_by_known_forall_fact = ForallFact::new(
            known_forall.params_def.clone(),
            known_forall.dom.clone(),
            vec![ExistOrAndChainAtomicFact::OrFact(
                or_fact_in_known_forall.clone(),
            )],
            known_forall.line_file.clone(),
        );
        let fact_verified = FactVerifiedByFact::new(
            Fact::OrFact(given_or_fact.clone()),
            verified_by_known_forall_fact.to_string(),
            InferResult::new(),
            verified_by_known_forall_fact.line_file,
        );
        Ok(Some(fact_verified))
    }
}
