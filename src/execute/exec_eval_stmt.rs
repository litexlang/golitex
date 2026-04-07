use crate::prelude::*;
use std::collections::HashMap;

/// Right-hand side of a binary op waiting while we evaluate the left spine (iterative, no deep Rust recursion).
enum PendingRight {
    Add(Obj),
    Sub(Obj),
    Mul(Obj),
    Div(Obj),
}

#[derive(Copy, Clone)]
enum BinaryCombineOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl Runtime {
    /// Evaluates numeric expressions for `eval` without deep recursion on the Rust stack.
    /// Algorithm calls are expanded in a loop; `Add`/`Sub`/`Mul`/`Div` use an explicit stack for the left spine.
    fn evaluate_symbol_obj_iterative(
        &mut self,
        initial: Obj,
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        let mut pending: Vec<PendingRight> = Vec::new();
        let mut cur = initial;

        loop {
            cur = self.peel_fn_obj_dispatch_loop(cur, eval_stmt)?;

            match cur {
                Obj::Add(add) => {
                    pending.push(PendingRight::Add(*add.right));
                    cur = *add.left;
                    continue;
                }
                Obj::Sub(sub) => {
                    pending.push(PendingRight::Sub(*sub.right));
                    cur = *sub.left;
                    continue;
                }
                Obj::Mul(mul) => {
                    pending.push(PendingRight::Mul(*mul.right));
                    cur = *mul.left;
                    continue;
                }
                Obj::Div(div) => {
                    pending.push(PendingRight::Div(*div.right));
                    cur = *div.left;
                    continue;
                }
                Obj::Number(acc_num) => {
                    let mut acc = Obj::Number(acc_num);
                    while let Some(pend) = pending.pop() {
                        let (combine_op, right_obj) = match pend {
                            PendingRight::Add(o) => (BinaryCombineOp::Add, o),
                            PendingRight::Sub(o) => (BinaryCombineOp::Sub, o),
                            PendingRight::Mul(o) => (BinaryCombineOp::Mul, o),
                            PendingRight::Div(o) => (BinaryCombineOp::Div, o),
                        };
                        let right_eval =
                            self.evaluate_symbol_obj_iterative(right_obj, eval_stmt)?;
                        acc =
                            self.combine_two_numeric_objs(acc, right_eval, combine_op, eval_stmt)?;
                    }
                    return Ok(acc);
                }
                _ => {
                    if pending.is_empty() {
                        return Ok(cur);
                    }
                    return Err(RuntimeError::from(
                        RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                            Stmt::EvalStmt(eval_stmt.clone()),
                            "eval: non-numeric intermediate with pending binary operation"
                                .to_string(),
                            None,
                            vec![],
                        ),
                    ));
                }
            }
        }
    }

    fn combine_two_numeric_objs(
        &mut self,
        left: Obj,
        right: Obj,
        combine_op: BinaryCombineOp,
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        let combined = match combine_op {
            BinaryCombineOp::Add => Obj::Add(crate::obj::Add::new(left, right)),
            BinaryCombineOp::Sub => Obj::Sub(crate::obj::Sub::new(left, right)),
            BinaryCombineOp::Mul => Obj::Mul(crate::obj::Mul::new(left, right)),
            BinaryCombineOp::Div => Obj::Div(crate::obj::Div::new(left, right)),
        };
        let calculated = combined.evaluate_to_normalized_decimal_number();
        match calculated {
            Some(number) => Ok(Obj::Number(number)),
            None => Err(RuntimeError::from(
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    Stmt::EvalStmt(eval_stmt.clone()),
                    "eval: failed to combine numeric sub-expression".to_string(),
                    None,
                    vec![],
                ),
            )),
        }
    }

    /// Repeatedly expands `FnObj` using the algo definition until the head is not a call.
    fn peel_fn_obj_dispatch_loop(
        &mut self,
        mut cur: Obj,
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        while let Obj::FnObj(ref fn_obj) = cur {
            cur = self.dispatch_algo_one_return_expr(fn_obj, eval_stmt)?;
        }
        Ok(cur)
    }

    /// One algo step: bind numeric args, match case / default, return **instantiated** return expression only (no recursive eval).
    fn dispatch_algo_one_return_expr(
        &mut self,
        fn_obj_to_evaluate: &FnObj,
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        let fn_name = fn_obj_to_evaluate.head.to_string();
        let mut flattened_number_args: Vec<Obj> = Vec::new();
        for arg_group in fn_obj_to_evaluate.body.iter() {
            for arg in arg_group.iter() {
                let evaluated_arg_obj =
                    self.evaluate_symbol_obj_iterative((**arg).clone(), eval_stmt)?;
                match evaluated_arg_obj {
                    Obj::Number(number) => {
                        flattened_number_args.push(Obj::Number(number));
                    }
                    _ => {
                        return Err(RuntimeError::from(
                            RuntimeErrorStruct::exec_stmt_with_message_and_cause(
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
                return Err(RuntimeError::from(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        Stmt::EvalStmt(eval_stmt.clone()),
                        format!("eval: algorithm `{}` is not defined", fn_name),
                        None,
                        vec![],
                    ),
                ));
            }
        };

        if flattened_number_args.len() != algo_definition.params.len() {
            return Err(RuntimeError::from(
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
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
            let instantiated_case_condition =
                self.inst_atomic_fact(&algo_case.condition, &param_to_arg_map)?;
            let verify_result = self
                .verify_atomic_fact(&instantiated_case_condition, &VerifyState::new(0, false))
                .map_err(|verify_error| {
                    RuntimeError::ExecStmtError(
                        RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                            Stmt::EvalStmt(eval_stmt.clone()),
                            "eval: failed to verify case condition".to_string(),
                            Some(verify_error),
                            vec![],
                        ),
                    )
                })?;

            if verify_result.is_true() {
                return self.inst_obj(&algo_case.return_stmt.value, &param_to_arg_map);
            }
            if verify_result.is_unknown() {
                let reversed_case_condition = instantiated_case_condition.make_reversed();
                let verify_reversed_result = self
                    .verify_atomic_fact(&reversed_case_condition, &VerifyState::new(0, false))
                    .map_err(|verify_error| {
                        RuntimeError::ExecStmtError(
                            RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                                Stmt::EvalStmt(eval_stmt.clone()),
                                "eval: failed to verify reversed case condition".to_string(),
                                Some(verify_error),
                                vec![],
                            ),
                        )
                    })?;
                if verify_reversed_result.is_unknown() {
                    return Err(RuntimeError::from(
                        RuntimeErrorStruct::exec_stmt_with_message_and_cause(
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
            self.inst_obj(&default_return_stmt.value, &param_to_arg_map)
        } else {
            Err(RuntimeError::from(
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
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
            return Err(RuntimeError::from(
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    Stmt::EvalStmt(stmt.clone()),
                    "eval: obj_to_eval must be a fnObj".to_string(),
                    None,
                    vec![],
                ),
            ));
        }

        self.push_env();
        let eval_result = self.evaluate_symbol_obj_iterative(stmt.obj_to_eval.clone(), stmt);
        self.pop_env();

        let evaluated_obj = eval_result?;
        let evaluated_equal_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
            stmt.obj_to_eval.clone(),
            evaluated_obj,
            stmt.line_file.clone(),
        )));

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&evaluated_equal_fact);
        self.store_fact_without_well_defined_verified_and_infer(evaluated_equal_fact)?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(Stmt::EvalStmt(stmt.clone()), infer_result, vec![]),
        ))
    }
}
