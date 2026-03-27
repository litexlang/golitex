use crate::environment::Environment;
use crate::error::{UnknownError, VerifyError};
use crate::execute::Runtime;
use crate::fact::{AtomicFact, Fact, RestrictFact};
use crate::infer::InferResult;
use crate::result::StmtUnknown;
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult};
use crate::verify::VerifyState;

impl Runtime {
    pub fn verify_non_equational_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut result =
            self.verify_non_equational_atomic_fact_with_builtin_rules(atomic_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
            atomic_fact,
        )?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let verify_state_add_one_round = verify_state.new_state_with_round_increased();
            result = self
                .verify_atomic_fact_with_known_forall(atomic_fact, &verify_state_add_one_round)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    pub fn verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if atomic_fact.number_of_args() == 1 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(atomic_fact)
        } else if atomic_fact.number_of_args() == 2 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(atomic_fact)
        } else {
            self
                .verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(atomic_fact)
        }
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut all_objs_equal_to_arg = self
            .runtime_context
            .get_all_objs_equal_to_arg(&atomic_fact.args()[0].to_string());
        if all_objs_equal_to_arg.is_empty() {
            all_objs_equal_to_arg.push(atomic_fact.args()[0].to_string());
        }

        for environment in self.runtime_context.iter_environments_from_top() {
            let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(environment, atomic_fact, &all_objs_equal_to_arg)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut all_objs_equal_to_arg0 = self
            .runtime_context
            .get_all_objs_equal_to_arg(&atomic_fact.args()[0].to_string());
        if all_objs_equal_to_arg0.is_empty() {
            all_objs_equal_to_arg0.push(atomic_fact.args()[0].to_string());
        }
        let mut all_objs_equal_to_arg1 = self
            .runtime_context
            .get_all_objs_equal_to_arg(&atomic_fact.args()[1].to_string());
        if all_objs_equal_to_arg1.is_empty() {
            all_objs_equal_to_arg1.push(atomic_fact.args()[1].to_string());
        }

        for environment in self.runtime_context.iter_environments_from_top() {
            let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params_with_facts_in_environment(environment, atomic_fact, &all_objs_equal_to_arg0, &all_objs_equal_to_arg1)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut all_objs_equal_to_each_arg: Vec<Vec<String>> = Vec::new();
        for arg in atomic_fact.args().iter() {
            let mut all_objs_equal_to_current_arg = self
                .runtime_context
                .get_all_objs_equal_to_arg(&arg.to_string());
            if all_objs_equal_to_current_arg.is_empty() {
                all_objs_equal_to_current_arg.push(arg.to_string());
            }
            all_objs_equal_to_each_arg.push(all_objs_equal_to_current_arg);
        }

        for environment in self.runtime_context.iter_environments_from_top() {
            let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params_with_facts_in_environment(
                environment,
                atomic_fact,
                &all_objs_equal_to_each_arg,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_arg: &Vec<String>,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(known_facts_map) = environment
            .known_atomic_facts_with_1_arg
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            for obj in all_objs_equal_to_arg.iter() {
                if let Some(known_atomic_fact) = known_facts_map.get(obj) {
                    return Ok(NonErrStmtExecResult::FactVerifiedByFact(
                        FactVerifiedByFact::new(
                            Fact::AtomicFact(atomic_fact.clone()),
                            known_atomic_fact.to_string(),
                            InferResult::new(),
                            known_atomic_fact.line_file(),
                        ),
                    ));
                }
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params_with_facts_in_environment(
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_arg0: &Vec<String>,
        all_objs_equal_to_arg1: &Vec<String>,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(known_facts_map) = environment
            .known_atomic_facts_with_2_args
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            for obj0 in all_objs_equal_to_arg0.iter() {
                for obj1 in all_objs_equal_to_arg1.iter() {
                    if let Some(known_atomic_fact) =
                        known_facts_map.get(&(obj0.clone(), obj1.clone()))
                    {
                        return Ok(NonErrStmtExecResult::FactVerifiedByFact(
                            FactVerifiedByFact::new(
                                Fact::AtomicFact(atomic_fact.clone()),
                                known_atomic_fact.to_string(),
                                InferResult::new(),
                                known_atomic_fact.line_file(),
                            ),
                        ));
                    }
                }
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params_with_facts_in_environment(
        environment: &Environment,
        atomic_fact: &AtomicFact,
        all_objs_equal_to_each_arg: &Vec<Vec<String>>,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(known_facts) = environment
            .known_atomic_facts_with_0_or_more_than_2_args
            .get(&(atomic_fact.key(), atomic_fact.is_true()))
        {
            for known_fact in known_facts.iter() {
                if known_fact.args().len() != atomic_fact.args().len() {
                    let message = format!(
                        "known atomic fact {} has different number of args than the given fact {}",
                        known_fact.to_string(),
                        atomic_fact.to_string()
                    );
                    return Err(VerifyError::new(
                        Fact::AtomicFact(atomic_fact.clone()),
                        Some(UnknownError::new(message, atomic_fact.line_file(), None).into()),
                    ));
                }
                let mut all_args_match = true;
                for (index, known_arg) in known_fact.args().iter().enumerate() {
                    let known_arg_string = known_arg.to_string();
                    if !all_objs_equal_to_each_arg[index].contains(&known_arg_string) {
                        all_args_match = false;
                        break;
                    }
                }
                if all_args_match {
                    return Ok(NonErrStmtExecResult::FactVerifiedByFact(
                        FactVerifiedByFact::new(
                            Fact::AtomicFact(atomic_fact.clone()),
                            known_fact.to_string(),
                            InferResult::new(),
                            known_fact.line_file(),
                        ),
                    ));
                }
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    pub fn verify_restrict_fact_with_builtin_rules(
        &mut self,
        restrict_fact: &RestrictFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        _ = restrict_fact;
        _ = verify_state;
        return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
    }
}
