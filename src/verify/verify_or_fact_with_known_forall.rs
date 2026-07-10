use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

// Same ∀-instantiation strategy as `verify_atomic_fact_with_known_forall` (σ from template to given).

impl Runtime {
    pub fn verify_or_fact_with_known_forall(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(fact_verified) =
            self.try_verify_or_fact_with_known_forall_facts_in_envs(or_fact, verify_state)?
        {
            return Ok((fact_verified).into());
        }
        Ok((StmtUnknown::new()).into())
    }

    fn get_matched_or_fact_in_known_forall_fact_in_envs(
        &mut self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_or_fact: &OrFact,
    ) -> Result<
        (
            (usize, usize),
            Option<HashMap<String, Obj>>,
            Option<(OrFact, Rc<KnownForallFactParamsAndDom>)>,
        ),
        RuntimeError,
    > {
        let lookup_key = given_or_fact.key();

        let envs_count = self.environment_count();
        for i in iterate_from_env_index..envs_count {
            let stack_idx = i;
            let known_forall_facts_count = {
                let env = self
                    .environment_by_top_index(stack_idx)
                    .expect("environment index should be valid");
                match env.known_or_facts_in_forall_facts.get(lookup_key.as_str()) {
                    Some(v) => v.len(),
                    None => continue,
                }
            };
            let start_index = if i == iterate_from_env_index {
                iterate_from_known_forall_fact_index
            } else {
                0
            };
            for j in start_index..known_forall_facts_count {
                let entry_idx = known_forall_facts_count - 1 - j;
                let current_known_forall = {
                    let env = self
                        .environment_by_top_index(stack_idx)
                        .expect("environment index should be valid");
                    let Some(known_forall_facts_in_env) =
                        env.known_or_facts_in_forall_facts.get(lookup_key.as_str())
                    else {
                        continue;
                    };
                    let Some(current_known_forall) = known_forall_facts_in_env.get(entry_idx)
                    else {
                        continue;
                    };
                    current_known_forall.clone()
                };
                let fact_args_in_known_forall = current_known_forall.0.get_args_from_fact_ref();
                let given_fact_args = given_or_fact.get_args_from_fact_ref();
                let match_result = self.match_args_in_fact_in_known_forall_fact_with_given_args(
                    &fact_args_in_known_forall,
                    &given_fact_args,
                )?;
                if let Some(arg_map) = match_result {
                    return Ok(((i, j), Some(arg_map), Some(current_known_forall)));
                }
            }
        }

        Ok(((0, 0), None, None))
    }

    fn try_verify_or_fact_with_known_forall_facts_in_envs(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
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

    fn verify_or_fact_args_satisfy_forall_requirements(
        &mut self,
        or_fact_in_known_forall: &OrFact,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        arg_map: HashMap<String, Obj>,
        given_or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let Some((instantiation, requirements)) = self
            .verify_known_forall_requirements_and_build_evidence(
                known_forall.as_ref(),
                &arg_map,
                given_or_fact.clone().into(),
                verify_state,
            )?
        else {
            return Ok(None);
        };

        let verified_by_known_forall_fact = ForallFact::new(
            known_forall.params_def.clone(),
            known_forall.dom.clone(),
            vec![or_fact_in_known_forall.clone().into()],
            known_forall.line_file.clone(),
        )?;
        let fact_verified = FactualStmtSuccess::new_with_verified_by_known_fact(
            given_or_fact.clone().into(),
            VerifiedByResult::known_forall_instantiation(
                verified_by_known_forall_fact.clone().into(),
                instantiation,
                requirements,
            ),
            Vec::new(),
        );
        Ok(Some(fact_verified))
    }
}
