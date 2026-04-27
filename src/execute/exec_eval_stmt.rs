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
    fn object_supported_by_eval_stmt(obj: &Obj) -> bool {
        matches!(
            obj,
            Obj::Number(_)
                | Obj::FnObj(_)
                | Obj::Add(_)
                | Obj::Sub(_)
                | Obj::Mul(_)
                | Obj::Div(_)
                | Obj::Pow(_)
                | Obj::Sum(_)
                | Obj::Product(_)
                | Obj::MatrixListObj(_)
                | Obj::MatrixAdd(_)
                | Obj::MatrixSub(_)
                | Obj::MatrixMul(_)
                | Obj::MatrixScalarMul(_)
                | Obj::MatrixPow(_)
                | Obj::Atom(AtomObj::Identifier(_))
        )
    }

    /// Only unary `'` … `{ … }` forms (or equivalent bare anonymous head); used by `eval` on sum/product.
    fn summand_as_unary_anonymous_fn_cloned(obj: &Obj) -> Option<AnonymousFn> {
        match obj {
            Obj::AnonymousFn(af) => Some(af.clone()),
            Obj::FnObj(fo) => {
                if !fo.body.is_empty() {
                    return None;
                }
                match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => Some((**a).clone()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// After substituting the sum/product index, evaluate any nested `sum` / `product` in the
    /// expression to a numeric value, then the outer accumulation can use `evaluate_to_normalized_decimal_number`.
    fn eval_reduce_nested_sum_product_in_obj(
        &mut self,
        obj: Obj,
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        match obj {
            Obj::Sum(s) => self.eval_sum_or_product_for_eval_stmt(
                s.start.as_ref(),
                s.end.as_ref(),
                s.func.as_ref(),
                false,
                eval_stmt,
            ),
            Obj::Product(p) => self.eval_sum_or_product_for_eval_stmt(
                p.start.as_ref(),
                p.end.as_ref(),
                p.func.as_ref(),
                true,
                eval_stmt,
            ),
            Obj::Add(b) => {
                let l = self.eval_reduce_nested_sum_product_in_obj((*b.left).clone(), eval_stmt)?;
                let r = self.eval_reduce_nested_sum_product_in_obj((*b.right).clone(), eval_stmt)?;
                Ok(Add::new(l, r).into())
            }
            Obj::Sub(b) => {
                let l = self.eval_reduce_nested_sum_product_in_obj((*b.left).clone(), eval_stmt)?;
                let r = self.eval_reduce_nested_sum_product_in_obj((*b.right).clone(), eval_stmt)?;
                Ok(Sub::new(l, r).into())
            }
            Obj::Mul(b) => {
                let l = self.eval_reduce_nested_sum_product_in_obj((*b.left).clone(), eval_stmt)?;
                let r = self.eval_reduce_nested_sum_product_in_obj((*b.right).clone(), eval_stmt)?;
                Ok(Mul::new(l, r).into())
            }
            Obj::Div(b) => {
                let l = self.eval_reduce_nested_sum_product_in_obj((*b.left).clone(), eval_stmt)?;
                let r = self.eval_reduce_nested_sum_product_in_obj((*b.right).clone(), eval_stmt)?;
                Ok(Div::new(l, r).into())
            }
            Obj::Mod(m) => {
                let l = self.eval_reduce_nested_sum_product_in_obj((*m.left).clone(), eval_stmt)?;
                let r = self.eval_reduce_nested_sum_product_in_obj((*m.right).clone(), eval_stmt)?;
                Ok(Mod::new(l, r).into())
            }
            Obj::Pow(p) => {
                let base =
                    self.eval_reduce_nested_sum_product_in_obj((*p.base).clone(), eval_stmt)?;
                let exp = self
                    .eval_reduce_nested_sum_product_in_obj((*p.exponent).clone(), eval_stmt)?;
                Ok(Pow::new(base, exp).into())
            }
            Obj::Abs(a) => {
                let arg = self.eval_reduce_nested_sum_product_in_obj((*a.arg).clone(), eval_stmt)?;
                Ok(Abs::new(arg).into())
            }
            Obj::Log(l) => {
                let b = self.eval_reduce_nested_sum_product_in_obj((*l.base).clone(), eval_stmt)?;
                let x = self.eval_reduce_nested_sum_product_in_obj((*l.arg).clone(), eval_stmt)?;
                Ok(Log::new(b, x).into())
            }
            Obj::Max(m) => {
                let l = self.eval_reduce_nested_sum_product_in_obj((*m.left).clone(), eval_stmt)?;
                let r = self.eval_reduce_nested_sum_product_in_obj((*m.right).clone(), eval_stmt)?;
                Ok(Max::new(l, r).into())
            }
            Obj::Min(m) => {
                let l = self.eval_reduce_nested_sum_product_in_obj((*m.left).clone(), eval_stmt)?;
                let r = self.eval_reduce_nested_sum_product_in_obj((*m.right).clone(), eval_stmt)?;
                Ok(Min::new(l, r).into())
            }
            other => Ok(other),
        }
    }

    /// Closed integer range: substitute index into the anonymous body `equal_to` and total + or *; no `fn`/algo in terms.
    fn eval_sum_or_product_for_eval_stmt(
        &mut self,
        start: &Obj,
        end: &Obj,
        func: &Obj,
        is_product: bool,
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        let start_ev = self.evaluate_symbol_obj_iterative(start.clone(), eval_stmt)?;
        let end_ev = self.evaluate_symbol_obj_iterative(end.clone(), eval_stmt)?;
        let Some(a_num) = self.resolve_obj_to_number(&start_ev) else {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: sum/product start must resolve to a number".to_string(),
                None,
                vec![],
            ));
        };
        let Some(b_num) = self.resolve_obj_to_number(&end_ev) else {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: sum/product end must resolve to a number".to_string(),
                None,
                vec![],
            ));
        };
        let as_ = a_num.normalized_value.trim();
        let bs = b_num.normalized_value.trim();
        if !is_number_string_literally_integer_without_dot(as_.to_string())
            || !is_number_string_literally_integer_without_dot(bs.to_string())
        {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: sum/product need integer (no fractional part) start and end for iteration"
                    .to_string(),
                None,
                vec![],
            ));
        }
        let ai = as_.parse::<i128>().map_err(|_| {
            short_exec_error(
                eval_stmt.clone().into(),
                "eval: sum/product could not parse integer bounds".to_string(),
                None,
                vec![],
            )
        })?;
        let bi = bs.parse::<i128>().map_err(|_| {
            short_exec_error(
                eval_stmt.clone().into(),
                "eval: sum/product could not parse integer bounds".to_string(),
                None,
                vec![],
            )
        })?;
        if ai > bi {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: sum/product need start <= end (integer range)".to_string(),
                None,
                vec![],
            ));
        }
        let Some(af) = Self::summand_as_unary_anonymous_fn_cloned(func) else {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: sum/product third argument must be a unary anonymous function (no calls)"
                    .to_string(),
                None,
                vec![],
            ));
        };
        if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: sum/product index function must be unary".to_string(),
                None,
                vec![],
            ));
        }
        let param_names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
        let pname = param_names[0].clone();
        let mut acc_num = if is_product {
            Number::new("1".to_string())
        } else {
            Number::new("0".to_string())
        };
        for k in ai..=bi {
            let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
            param_to_arg_map.insert(pname.clone(), Number::new(k.to_string()).into());
            let inst = self.inst_obj(af.equal_to.as_ref(), &param_to_arg_map, ParamObjType::FnSet)?;
            let term = self.resolve_obj(&inst);
            let term = self.eval_reduce_nested_sum_product_in_obj(term, eval_stmt)?;
            let Some(n) = term.evaluate_to_normalized_decimal_number() else {
                return Err(short_exec_error(
                    eval_stmt.clone().into(),
                    format!(
                        "eval: could not reduce sum/product body to a number at index {}",
                        k
                    ),
                    None,
                    vec![],
                ));
            };
            if is_product {
                let step: Obj = Mul::new(acc_num.into(), n.into()).into();
                acc_num = step.evaluate_to_normalized_decimal_number().ok_or_else(|| {
                    short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: product accumulation failed to normalize".to_string(),
                        None,
                        vec![],
                    )
                })?;
            } else {
                let step: Obj = Add::new(acc_num.into(), n.into()).into();
                acc_num = step.evaluate_to_normalized_decimal_number().ok_or_else(|| {
                    short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: sum accumulation failed to normalize".to_string(),
                        None,
                        vec![],
                    )
                })?;
            }
        }
        Ok(acc_num.into())
    }

    fn eval_matrix_list_cells_for_eval_stmt(
        &mut self,
        m: MatrixListObj,
        eval_stmt: &EvalStmt,
    ) -> Result<MatrixListObj, RuntimeError> {
        let mut rows_out = Vec::with_capacity(m.rows.len());
        for row in m.rows {
            let mut out_row = Vec::with_capacity(row.len());
            for cell in row {
                let v = self.evaluate_symbol_obj_iterative(*cell, eval_stmt)?;
                out_row.push(Box::new(v));
            }
            rows_out.push(out_row);
        }
        Ok(MatrixListObj { rows: rows_out })
    }

    fn add_matrix_lists_under_eval(
        &self,
        left: MatrixListObj,
        right: MatrixListObj,
        eval_stmt: &EvalStmt,
    ) -> Result<MatrixListObj, RuntimeError> {
        if left.rows.len() != right.rows.len() {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: matrix ++ row count mismatch".to_string(),
                None,
                vec![],
            ));
        }
        let mut rows = Vec::with_capacity(left.rows.len());
        for (lr, rr) in left.rows.into_iter().zip(right.rows.into_iter()) {
            if lr.len() != rr.len() {
                return Err(short_exec_error(
                    eval_stmt.clone().into(),
                    "eval: matrix ++ column count mismatch".to_string(),
                    None,
                    vec![],
                ));
            }
            let mut row = Vec::with_capacity(lr.len());
            for (a, b) in lr.into_iter().zip(rr.into_iter()) {
                let sum_obj: Obj = Add::new(*a, *b).into();
                let Some(n) = sum_obj.evaluate_to_normalized_decimal_number() else {
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: matrix ++ needs numeric cells".to_string(),
                        None,
                        vec![],
                    ));
                };
                row.push(Box::new(n.into()));
            }
            rows.push(row);
        }
        Ok(MatrixListObj { rows })
    }

    fn sub_matrix_lists_under_eval(
        &self,
        left: MatrixListObj,
        right: MatrixListObj,
        eval_stmt: &EvalStmt,
    ) -> Result<MatrixListObj, RuntimeError> {
        if left.rows.len() != right.rows.len() {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: matrix -- row count mismatch".to_string(),
                None,
                vec![],
            ));
        }
        let mut rows = Vec::with_capacity(left.rows.len());
        for (lr, rr) in left.rows.into_iter().zip(right.rows.into_iter()) {
            if lr.len() != rr.len() {
                return Err(short_exec_error(
                    eval_stmt.clone().into(),
                    "eval: matrix -- column count mismatch".to_string(),
                    None,
                    vec![],
                ));
            }
            let mut row = Vec::with_capacity(lr.len());
            for (a, b) in lr.into_iter().zip(rr.into_iter()) {
                let diff_obj: Obj = Sub::new(*a, *b).into();
                let Some(n) = diff_obj.evaluate_to_normalized_decimal_number() else {
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: matrix -- needs numeric cells".to_string(),
                        None,
                        vec![],
                    ));
                };
                row.push(Box::new(n.into()));
            }
            rows.push(row);
        }
        Ok(MatrixListObj { rows })
    }

    fn multiply_matrix_lists_under_eval(
        &self,
        left: MatrixListObj,
        right: MatrixListObj,
        eval_stmt: &EvalStmt,
    ) -> Result<MatrixListObj, RuntimeError> {
        let r1 = left.rows.len();
        let c1 = if r1 == 0 {
            0
        } else {
            left.rows[0].len()
        };
        let r2 = right.rows.len();
        let c2 = if r2 == 0 {
            0
        } else {
            right.rows[0].len()
        };
        if c1 != r2 {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: matrix ** inner dimension mismatch".to_string(),
                None,
                vec![],
            ));
        }
        let mut rows: Vec<Vec<Box<Obj>>> = Vec::with_capacity(r1);
        for i in 0..r1 {
            let mut row: Vec<Box<Obj>> = Vec::with_capacity(c2);
            for k in 0..c2 {
                let mut acc_num = Number::new("0".to_string());
                for j in 0..c1 {
                    let prod_obj: Obj = Mul::new(
                        (*left.rows[i][j]).clone(),
                        (*right.rows[j][k]).clone(),
                    )
                    .into();
                    let Some(p) = prod_obj.evaluate_to_normalized_decimal_number() else {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: matrix ** cell multiply failed".to_string(),
                            None,
                            vec![],
                        ));
                    };
                    let sum_obj: Obj = Add::new(acc_num.into(), p.into()).into();
                    let Some(s) = sum_obj.evaluate_to_normalized_decimal_number() else {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: matrix ** accumulation failed".to_string(),
                            None,
                            vec![],
                        ));
                    };
                    acc_num = s;
                }
                row.push(Box::new(acc_num.into()));
            }
            rows.push(row);
        }
        Ok(MatrixListObj { rows })
    }

    fn scalar_matrix_mul_under_eval(
        &self,
        scalar: Obj,
        matrix: MatrixListObj,
        eval_stmt: &EvalStmt,
    ) -> Result<MatrixListObj, RuntimeError> {
        let mut rows_out = Vec::with_capacity(matrix.rows.len());
        for row in matrix.rows {
            let mut out_row = Vec::with_capacity(row.len());
            for cell in row {
                let prod_obj: Obj = Mul::new(scalar.clone(), (*cell).clone()).into();
                let Some(n) = prod_obj.evaluate_to_normalized_decimal_number() else {
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: *. needs scalar and numeric matrix cells".to_string(),
                        None,
                        vec![],
                    ));
                };
                out_row.push(Box::new(n.into()));
            }
            rows_out.push(out_row);
        }
        Ok(MatrixListObj { rows: rows_out })
    }

    fn matrix_pow_under_eval(
        &self,
        base: MatrixListObj,
        exponent: usize,
        eval_stmt: &EvalStmt,
    ) -> Result<MatrixListObj, RuntimeError> {
        if exponent == 0 {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: matrix ^^ exponent must be at least 1".to_string(),
                None,
                vec![],
            ));
        }
        let mut acc = base.clone();
        for _ in 1..exponent {
            acc = self.multiply_matrix_lists_under_eval(acc, base.clone(), eval_stmt)?;
        }
        Ok(acc)
    }

    fn eval_to_matrix_list_for_eval_stmt(
        &mut self,
        obj: Obj,
        eval_stmt: &EvalStmt,
    ) -> Result<MatrixListObj, RuntimeError> {
        let cur = self.peel_fn_obj_dispatch_loop(obj, eval_stmt)?;
        match cur {
            Obj::MatrixListObj(m) => self.eval_matrix_list_cells_for_eval_stmt(m, eval_stmt),
            Obj::MatrixAdd(ma) => {
                let l = self.eval_to_matrix_list_for_eval_stmt((*ma.left).clone(), eval_stmt)?;
                let r = self.eval_to_matrix_list_for_eval_stmt((*ma.right).clone(), eval_stmt)?;
                self.add_matrix_lists_under_eval(l, r, eval_stmt)
            }
            Obj::MatrixSub(ms) => {
                let l = self.eval_to_matrix_list_for_eval_stmt((*ms.left).clone(), eval_stmt)?;
                let r = self.eval_to_matrix_list_for_eval_stmt((*ms.right).clone(), eval_stmt)?;
                self.sub_matrix_lists_under_eval(l, r, eval_stmt)
            }
            Obj::MatrixMul(mm) => {
                let l = self.eval_to_matrix_list_for_eval_stmt((*mm.left).clone(), eval_stmt)?;
                let r = self.eval_to_matrix_list_for_eval_stmt((*mm.right).clone(), eval_stmt)?;
                self.multiply_matrix_lists_under_eval(l, r, eval_stmt)
            }
            Obj::MatrixScalarMul(m) => {
                let s = self.evaluate_symbol_obj_iterative((*m.scalar).clone(), eval_stmt)?;
                let mat = self.eval_to_matrix_list_for_eval_stmt((*m.matrix).clone(), eval_stmt)?;
                self.scalar_matrix_mul_under_eval(s, mat, eval_stmt)
            }
            Obj::MatrixPow(mp) => {
                let base = self.eval_to_matrix_list_for_eval_stmt((*mp.base).clone(), eval_stmt)?;
                let exp_obj =
                    self.evaluate_symbol_obj_iterative((*mp.exponent).clone(), eval_stmt)?;
                let Some(exp_num) = exp_obj.evaluate_to_normalized_decimal_number() else {
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: matrix ^^ exponent must evaluate to a number".to_string(),
                        None,
                        vec![],
                    ));
                };
                let exp_u = exp_num.normalized_value.parse::<usize>().map_err(|_| {
                    short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: matrix ^^ exponent must be a non-negative integer".to_string(),
                        None,
                        vec![],
                    )
                })?;
                self.matrix_pow_under_eval(base, exp_u, eval_stmt)
            }
            other => {
                let lookup_key = match &other {
                    Obj::Atom(AtomObj::Identifier(id)) => id.name.clone(),
                    _ => other.to_string(),
                };
                let Some(ml) = self.get_obj_equal_to_matrix_list(&lookup_key) else {
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        format!("eval: `{}` is not a matrix list", lookup_key),
                        None,
                        vec![],
                    ));
                };
                self.eval_to_matrix_list_for_eval_stmt(ml.into(), eval_stmt)
            }
        }
    }

    fn finish_numeric_accumulator_with_pending_rights(
        &mut self,
        acc: Obj,
        pending: &mut Vec<PendingRight>,
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        let mut acc = acc;
        while let Some(pend) = pending.pop() {
            let (combine_op, right_obj) = match pend {
                PendingRight::Add(o) => (BinaryCombineOp::Add, o),
                PendingRight::Sub(o) => (BinaryCombineOp::Sub, o),
                PendingRight::Mul(o) => (BinaryCombineOp::Mul, o),
                PendingRight::Div(o) => (BinaryCombineOp::Div, o),
            };
            let right_eval = self.evaluate_symbol_obj_iterative(right_obj, eval_stmt)?;
            acc = self.combine_two_numeric_objs(acc, right_eval, combine_op, eval_stmt)?;
        }
        Ok(acc)
    }

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
                    return self.finish_numeric_accumulator_with_pending_rights(
                        acc_num.into(),
                        &mut pending,
                        eval_stmt,
                    );
                }
                Obj::Pow(pow) => {
                    let left = self.evaluate_symbol_obj_iterative((*pow.base).clone(), eval_stmt)?;
                    let right =
                        self.evaluate_symbol_obj_iterative((*pow.exponent).clone(), eval_stmt)?;
                    let combined: Obj = Pow::new(left, right).into();
                    match combined.evaluate_to_normalized_decimal_number() {
                        Some(acc_num) => {
                            return self.finish_numeric_accumulator_with_pending_rights(
                                acc_num.into(),
                                &mut pending,
                                eval_stmt,
                            );
                        }
                        None => {
                            if pending.is_empty() {
                                return Ok(combined);
                            }
                            return Err(short_exec_error(
                                eval_stmt.clone().into(),
                                "eval: non-numeric power with pending binary operation"
                                    .to_string(),
                                None,
                                vec![],
                            ));
                        }
                    }
                }
                Obj::Sum(sum) => {
                    if !pending.is_empty() {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: sum with pending binary operation".to_string(),
                            None,
                            vec![],
                        ));
                    }
                    let v = self.eval_sum_or_product_for_eval_stmt(
                        sum.start.as_ref(),
                        sum.end.as_ref(),
                        sum.func.as_ref(),
                        false,
                        eval_stmt,
                    )?;
                    return self.finish_numeric_accumulator_with_pending_rights(
                        v,
                        &mut pending,
                        eval_stmt,
                    );
                }
                Obj::Product(prod) => {
                    if !pending.is_empty() {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: product with pending binary operation".to_string(),
                            None,
                            vec![],
                        ));
                    }
                    let v = self.eval_sum_or_product_for_eval_stmt(
                        prod.start.as_ref(),
                        prod.end.as_ref(),
                        prod.func.as_ref(),
                        true,
                        eval_stmt,
                    )?;
                    return self.finish_numeric_accumulator_with_pending_rights(
                        v,
                        &mut pending,
                        eval_stmt,
                    );
                }
                Obj::MatrixListObj(m) => {
                    if !pending.is_empty() {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: matrix value with pending binary operation".to_string(),
                            None,
                            vec![],
                        ));
                    }
                    let done = self.eval_matrix_list_cells_for_eval_stmt(m, eval_stmt)?;
                    return Ok(done.into());
                }
                Obj::MatrixAdd(ma) => {
                    if !pending.is_empty() {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: matrix ++ with pending binary operation".to_string(),
                            None,
                            vec![],
                        ));
                    }
                    let done = self.eval_to_matrix_list_for_eval_stmt(Obj::MatrixAdd(ma), eval_stmt)?;
                    return Ok(done.into());
                }
                Obj::MatrixSub(ms) => {
                    if !pending.is_empty() {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: matrix -- with pending binary operation".to_string(),
                            None,
                            vec![],
                        ));
                    }
                    let done = self.eval_to_matrix_list_for_eval_stmt(Obj::MatrixSub(ms), eval_stmt)?;
                    return Ok(done.into());
                }
                Obj::MatrixMul(mm) => {
                    if !pending.is_empty() {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: matrix ** with pending binary operation".to_string(),
                            None,
                            vec![],
                        ));
                    }
                    let done = self.eval_to_matrix_list_for_eval_stmt(Obj::MatrixMul(mm), eval_stmt)?;
                    return Ok(done.into());
                }
                Obj::MatrixScalarMul(m) => {
                    if !pending.is_empty() {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: *. with pending binary operation".to_string(),
                            None,
                            vec![],
                        ));
                    }
                    let done =
                        self.eval_to_matrix_list_for_eval_stmt(Obj::MatrixScalarMul(m), eval_stmt)?;
                    return Ok(done.into());
                }
                Obj::MatrixPow(mp) => {
                    if !pending.is_empty() {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: matrix ^^ with pending binary operation".to_string(),
                            None,
                            vec![],
                        ));
                    }
                    let done = self.eval_to_matrix_list_for_eval_stmt(Obj::MatrixPow(mp), eval_stmt)?;
                    return Ok(done.into());
                }
                _ => {
                    if pending.is_empty() {
                        return Ok(cur);
                    }
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: non-numeric intermediate with pending binary operation".to_string(),
                        None,
                        vec![],
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
        let combined: Obj = match combine_op {
            BinaryCombineOp::Add => Add::new(left, right).into(),
            BinaryCombineOp::Sub => Sub::new(left, right).into(),
            BinaryCombineOp::Mul => Mul::new(left, right).into(),
            BinaryCombineOp::Div => Div::new(left, right).into(),
        };
        let calculated = combined.evaluate_to_normalized_decimal_number();
        match calculated {
            Some(number) => Ok(number.into()),
            None => Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: failed to combine numeric sub-expression".to_string(),
                None,
                vec![],
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
                        flattened_number_args.push(number.into());
                    }
                    _ => {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: function arguments must evaluate to Number".to_string(),
                            None,
                            vec![],
                        ));
                    }
                }
            }
        }

        let algo_definition = match self.get_algo_definition_by_name(&fn_name) {
            Some(definition) => definition.clone(),
            None => {
                return Err(short_exec_error(
                    eval_stmt.clone().into(),
                    format!("eval: algorithm `{}` is not defined", fn_name),
                    None,
                    vec![],
                ));
            }
        };

        if flattened_number_args.len() != algo_definition.params.len() {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                format!(
                    "eval: argument count mismatch (expected {}, got {})",
                    algo_definition.params.len(),
                    flattened_number_args.len()
                ),
                None,
                vec![],
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
                self.inst_atomic_fact(
                    &algo_case.condition,
                    &param_to_arg_map,
                    ParamObjType::DefAlgo,
                    None,
                )?;
            let verify_result = self
                .verify_atomic_fact(&instantiated_case_condition, &VerifyState::new(0, false))
                .map_err(|verify_error| {
                    short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: failed to verify case condition".to_string(),
                        Some(verify_error),
                        vec![],
                    )
                })?;

            if verify_result.is_true() {
                return self.inst_obj(&algo_case.return_stmt.value, &param_to_arg_map, ParamObjType::DefAlgo);
            }
            if verify_result.is_unknown() {
                let reversed_case_condition = instantiated_case_condition.make_reversed();
                let verify_reversed_result = self
                    .verify_atomic_fact(&reversed_case_condition, &VerifyState::new(0, false))
                    .map_err(|verify_error| {
                        short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: failed to verify reversed case condition".to_string(),
                            Some(verify_error),
                            vec![],
                        )
                    })?;
                if verify_reversed_result.is_unknown() {
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        format!(
                            "eval: case `{}` is unknown and its reverse is also unknown",
                            instantiated_case_condition
                        ),
                        None,
                        vec![],
                    ));
                }
            }
        }

        if let Some(default_return_stmt) = &algo_definition.default_return {
            self.inst_obj(&default_return_stmt.value, &param_to_arg_map, ParamObjType::DefAlgo)
        } else {
            Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: no case matched and no default return".to_string(),
                None,
                vec![],
            ))
        }
    }

    pub fn exec_eval_stmt(&mut self, stmt: &EvalStmt) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(
            &stmt.obj_to_eval,
            &VerifyState::new(0, false),
        )?;

        let resolved_obj = self.resolve_obj(&stmt.obj_to_eval);
        let eval_result = self.run_in_local_env(|rt| {
            if !Self::object_supported_by_eval_stmt(&resolved_obj) {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    "eval: need a function call, numeric expression (+ - * / ^), sum/product over a unary anonymous body, or matrix ++ -- ** *. ^^ / matrix literal"
                        .to_string(),
                    None,
                    vec![],
                ));
            }
            rt.evaluate_symbol_obj_iterative(resolved_obj.clone(), stmt)
        });

        let evaluated_obj = eval_result?;
        let evaluated_equal_fact = EqualFact::new(
            stmt.obj_to_eval.clone(),
            evaluated_obj,
            stmt.line_file.clone(),
        )
        .into();

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&evaluated_equal_fact);
        self.verify_well_defined_and_store_and_infer_with_default_verify_state(evaluated_equal_fact)?;

        Ok((NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![])).into())
    }
}
