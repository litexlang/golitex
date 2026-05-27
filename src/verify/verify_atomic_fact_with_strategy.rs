use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn verify_non_equational_atomic_fact_with_strategy(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(strategy_name) = self.active_strategy_name_for_atomic_fact(atomic_fact) else {
            return Ok(StmtUnknown::new().into());
        };
        let Some(strategy) = self
            .get_strategy_definition_by_name(&strategy_name)
            .cloned()
        else {
            return Ok(StmtUnknown::new().into());
        };
        let Some(ExistOrAndChainAtomicFact::AtomicFact(then_atomic_fact)) =
            strategy.forall_fact.then_facts.first()
        else {
            return Ok(StmtUnknown::new().into());
        };

        let Some(arg_map) = self.match_args_in_fact_in_known_forall_fact_with_given_args(
            &then_atomic_fact.args(),
            &atomic_fact.args(),
        )?
        else {
            return Ok(StmtUnknown::new().into());
        };

        self.verify_atomic_fact_with_strategy_args(
            atomic_fact,
            &strategy,
            &strategy_name,
            arg_map,
            verify_state,
        )
    }

    fn active_strategy_name_for_atomic_fact(
        &self,
        atomic_fact: &AtomicFact,
    ) -> Option<StrategyName> {
        let lookup_key = (atomic_fact.key(), atomic_fact.is_true());
        let mut stopped_strategy_names: Vec<StrategyName> = Vec::new();

        for env in self.iter_environments_from_top() {
            if let Some(strategy_name) = env.stopped_strategy_stmts.get(&lookup_key) {
                if !stopped_strategy_names.contains(strategy_name) {
                    stopped_strategy_names.push(strategy_name.clone());
                }
            }
            if let Some(strategy_name) = env.used_strategy_stmts.get(&lookup_key) {
                if !stopped_strategy_names.contains(strategy_name) {
                    return Some(strategy_name.clone());
                }
            }
        }

        None
    }

    fn verify_atomic_fact_with_strategy_args(
        &mut self,
        atomic_fact: &AtomicFact,
        strategy: &DefStrategyStmt,
        strategy_name: &str,
        arg_map: HashMap<String, Obj>,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let param_names = strategy
            .forall_fact
            .params_def_with_type
            .collect_param_names();
        if !param_names
            .iter()
            .all(|param_name| arg_map.contains_key(param_name))
        {
            return Ok(StmtUnknown::new().into());
        }

        let mut args_for_params: Vec<Obj> = Vec::new();
        for param_name in param_names.iter() {
            let Some(obj) = arg_map.get(param_name) else {
                return Ok(StmtUnknown::new().into());
            };
            args_for_params.push(obj.clone());
        }

        let args_param_types = self
            .verify_args_satisfy_param_def_flat_types(
                &strategy.forall_fact.params_def_with_type,
                &args_for_params,
                verify_state,
                ParamObjType::Forall,
            )
            .map_err(|e| {
                RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                    Some(Fact::from(atomic_fact.clone()).into_stmt()),
                    String::new(),
                    atomic_fact.line_file(),
                    Some(e),
                    vec![],
                )))
            })?;
        if args_param_types.is_unknown() {
            return Ok(StmtUnknown::new().into());
        }

        let Some(param_to_arg_map) = strategy
            .forall_fact
            .params_def_with_type
            .param_def_params_to_arg_map(&arg_map)
        else {
            return Ok(StmtUnknown::new().into());
        };

        for dom_fact in strategy.forall_fact.dom_facts.iter() {
            let instantiated_dom_fact = self
                .inst_fact(dom_fact, &param_to_arg_map, ParamObjType::Forall, None)
                .map_err(|e| {
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(atomic_fact.clone()).into_stmt()),
                        String::new(),
                        atomic_fact.line_file(),
                        Some(e),
                        vec![],
                    )))
                })?;
            let result = self
                .verify_fact(&instantiated_dom_fact, verify_state)
                .map_err(|e| {
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(atomic_fact.clone()).into_stmt()),
                        String::new(),
                        atomic_fact.line_file(),
                        Some(e),
                        vec![],
                    )))
                })?;
            if result.is_unknown() {
                return Ok(StmtUnknown::new().into());
            }
        }

        Ok(FactualStmtSuccess::new_with_verified_by_known_fact(
            atomic_fact.clone().into(),
            VerifiedByResult::cited_stmt(
                atomic_fact.clone().into(),
                strategy.clone().into(),
                Some(format!("strategy `{}`", strategy_name)),
            ),
            Vec::new(),
        )
        .into())
    }
}
