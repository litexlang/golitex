use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    fn evaluate_symbol_obj_recursively(
        &mut self,
        obj_to_evaluate: &Obj,
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        match obj_to_evaluate {
            Obj::FnObj(fn_obj) => self.evaluate_fn_obj_to_obj(fn_obj, eval_stmt),
            Obj::Add(add_obj) => {
                let evaluated_left_obj =
                    self.evaluate_symbol_obj_recursively(&add_obj.left, eval_stmt)?;
                let evaluated_right_obj =
                    self.evaluate_symbol_obj_recursively(&add_obj.right, eval_stmt)?;
                let calculated_number = Obj::Add(crate::obj::Add::new(
                    evaluated_left_obj,
                    evaluated_right_obj,
                ))
                .evaluate_to_normalized_decimal_number();
                match calculated_number {
                    Some(number) => Ok(Obj::Number(number)),
                    None => Err(RuntimeError::ExecStmtError(
                        ExecStmtError::with_message_and_cause(
                            Stmt::EvalStmt(eval_stmt.clone()),
                            "eval: failed to calculate add expression".to_string(),
                            None,
                            vec![],
                        ),
                    )),
                }
            }
            Obj::Sub(sub_obj) => {
                let evaluated_left_obj =
                    self.evaluate_symbol_obj_recursively(&sub_obj.left, eval_stmt)?;
                let evaluated_right_obj =
                    self.evaluate_symbol_obj_recursively(&sub_obj.right, eval_stmt)?;
                let calculated_number = Obj::Sub(crate::obj::Sub::new(
                    evaluated_left_obj,
                    evaluated_right_obj,
                ))
                .evaluate_to_normalized_decimal_number();
                match calculated_number {
                    Some(number) => Ok(Obj::Number(number)),
                    None => Err(RuntimeError::ExecStmtError(
                        ExecStmtError::with_message_and_cause(
                            Stmt::EvalStmt(eval_stmt.clone()),
                            "eval: failed to calculate sub expression".to_string(),
                            None,
                            vec![],
                        ),
                    )),
                }
            }
            Obj::Mul(mul_obj) => {
                let evaluated_left_obj =
                    self.evaluate_symbol_obj_recursively(&mul_obj.left, eval_stmt)?;
                let evaluated_right_obj =
                    self.evaluate_symbol_obj_recursively(&mul_obj.right, eval_stmt)?;
                let calculated_number = Obj::Mul(crate::obj::Mul::new(
                    evaluated_left_obj,
                    evaluated_right_obj,
                ))
                .evaluate_to_normalized_decimal_number();
                match calculated_number {
                    Some(number) => Ok(Obj::Number(number)),
                    None => Err(RuntimeError::ExecStmtError(
                        ExecStmtError::with_message_and_cause(
                            Stmt::EvalStmt(eval_stmt.clone()),
                            "eval: failed to calculate mul expression".to_string(),
                            None,
                            vec![],
                        ),
                    )),
                }
            }
            Obj::Div(div_obj) => {
                let evaluated_left_obj =
                    self.evaluate_symbol_obj_recursively(&div_obj.left, eval_stmt)?;
                let evaluated_right_obj =
                    self.evaluate_symbol_obj_recursively(&div_obj.right, eval_stmt)?;
                let calculated_number = Obj::Div(crate::obj::Div::new(
                    evaluated_left_obj,
                    evaluated_right_obj,
                ))
                .evaluate_to_normalized_decimal_number();
                match calculated_number {
                    Some(number) => Ok(Obj::Number(number)),
                    None => Err(RuntimeError::ExecStmtError(
                        ExecStmtError::with_message_and_cause(
                            Stmt::EvalStmt(eval_stmt.clone()),
                            "eval: failed to calculate div expression".to_string(),
                            None,
                            vec![],
                        ),
                    )),
                }
            }
            _ => Ok(obj_to_evaluate.clone()),
        }
    }

    fn evaluate_fn_obj_to_obj(
        &mut self,
        fn_obj_to_evaluate: &FnObj,
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        let fn_name = fn_obj_to_evaluate.head.to_string();
        let mut flattened_number_args: Vec<Obj> = Vec::new();
        for arg_group in fn_obj_to_evaluate.body.iter() {
            for arg in arg_group.iter() {
                let evaluated_arg_obj = self.evaluate_symbol_obj_recursively(arg, eval_stmt)?;
                match evaluated_arg_obj {
                    Obj::Number(number) => {
                        flattened_number_args.push(Obj::Number(number));
                    }
                    _ => {
                        return Err(RuntimeError::ExecStmtError(
                            ExecStmtError::with_message_and_cause(
                                Stmt::EvalStmt(eval_stmt.clone()),
                                "eval: function arguments must evaluate to Number".to_string(),
                                None,
                                vec![],
                            ),
                        ));
                    }
                }
            }
        }

        let algo_definition = match self.get_algo_definition_by_name(&fn_name) {
            Some(definition) => definition.clone(),
            None => {
                return Err(RuntimeError::ExecStmtError(
                    ExecStmtError::with_message_and_cause(
                        Stmt::EvalStmt(eval_stmt.clone()),
                        format!("eval: algorithm `{}` is not defined", fn_name),
                        None,
                        vec![],
                    ),
                ));
            }
        };

        if flattened_number_args.len() != algo_definition.params.len() {
            return Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    Stmt::EvalStmt(eval_stmt.clone()),
                    format!(
                        "eval: argument count mismatch (expected {}, got {})",
                        algo_definition.params.len(),
                        flattened_number_args.len()
                    ),
                    None,
                    vec![],
                ),
            ));
        }

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        for (param_name, arg_obj) in algo_definition
            .params
            .iter()
            .zip(flattened_number_args.iter())
        {
            param_to_arg_map.insert(param_name.clone(), arg_obj.clone());
        }

        for algo_case in algo_definition.cases.iter() {
            let instantiated_case_condition = algo_case.condition.instantiate(&param_to_arg_map);
            let verify_result = self
                .verify_atomic_fact(&instantiated_case_condition, &VerifyState::new(0, false))
                .map_err(|verify_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                        Stmt::EvalStmt(eval_stmt.clone()),
                        "eval: failed to verify case condition".to_string(),
                        Some(verify_error.into()),
                        vec![],
                    ))
                })?;

            if verify_result.is_true() {
                let instantiated_symbol_result =
                    algo_case.return_stmt.value.instantiate(&param_to_arg_map);
                return self
                    .evaluate_symbol_obj_recursively(&instantiated_symbol_result, eval_stmt);
            }
            if verify_result.is_unknown() {
                let reversed_case_condition = instantiated_case_condition.make_reversed();
                let verify_reversed_result = self
                    .verify_atomic_fact(&reversed_case_condition, &VerifyState::new(0, false))
                    .map_err(|verify_error| {
                        RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                            Stmt::EvalStmt(eval_stmt.clone()),
                            "eval: failed to verify reversed case condition".to_string(),
                            Some(verify_error.into()),
                            vec![],
                        ))
                    })?;
                if verify_reversed_result.is_unknown() {
                    return Err(RuntimeError::ExecStmtError(
                        ExecStmtError::with_message_and_cause(
                            Stmt::EvalStmt(eval_stmt.clone()),
                            format!(
                                "eval: case `{}` is unknown and its reverse is also unknown",
                                instantiated_case_condition
                            ),
                            None,
                            vec![],
                        ),
                    ));
                }
            }
        }

        if let Some(default_return_stmt) = &algo_definition.default_return {
            let instantiated_default_symbol =
                default_return_stmt.value.instantiate(&param_to_arg_map);
            self.evaluate_symbol_obj_recursively(&instantiated_default_symbol, eval_stmt)
        } else {
            Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    Stmt::EvalStmt(eval_stmt.clone()),
                    "eval: no case matched and no default return".to_string(),
                    None,
                    vec![],
                ),
            ))
        }
    }

    pub fn _exec_eval_stmt(
        &mut self,
        stmt: &EvalStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(
            &stmt.obj_to_eval,
            &VerifyState::new(0, false),
        )?;

        if !matches!(stmt.obj_to_eval, Obj::FnObj(_)) {
            return Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    Stmt::EvalStmt(stmt.clone()),
                    "eval: obj_to_eval must be a fnObj".to_string(),
                    None,
                    vec![],
                ),
            ));
        }

        self.push_env();
        let eval_result = self.evaluate_symbol_obj_recursively(&stmt.obj_to_eval, stmt);
        self.pop_env();

        let evaluated_obj = eval_result?;
        let evaluated_equal_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            stmt.obj_to_eval.clone(),
            evaluated_obj,
            stmt.line_file,
        )));

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&evaluated_equal_fact);
        self.store_fact_without_well_defined_verified_and_infer(evaluated_equal_fact)?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(Stmt::EvalStmt(stmt.clone()), infer_result, vec![]),
        ))
    }
}
