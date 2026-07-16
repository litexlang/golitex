use crate::prelude::*;
use std::collections::{HashMap, HashSet};

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
    /// expression to an eval numeric value before the outer accumulation.
    fn eval_reduce_nested_sum_product_in_obj(
        &mut self,
        obj: Obj,
        eval_stmt: &EvalStmt,
        active_fn_calls: &mut HashSet<ObjString>,
    ) -> Result<Obj, RuntimeError> {
        match obj {
            Obj::Sum(s) => self.eval_sum_or_product_for_eval_stmt(
                s.start.as_ref(),
                s.end.as_ref(),
                s.func.as_ref(),
                false,
                eval_stmt,
                active_fn_calls,
            ),
            Obj::Product(p) => self.eval_sum_or_product_for_eval_stmt(
                p.start.as_ref(),
                p.end.as_ref(),
                p.func.as_ref(),
                true,
                eval_stmt,
                active_fn_calls,
            ),
            Obj::Add(b) => {
                let l = self.eval_reduce_nested_sum_product_in_obj(
                    (*b.left).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let r = self.eval_reduce_nested_sum_product_in_obj(
                    (*b.right).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                Ok(Add::new(l, r).into())
            }
            Obj::Sub(b) => {
                let l = self.eval_reduce_nested_sum_product_in_obj(
                    (*b.left).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let r = self.eval_reduce_nested_sum_product_in_obj(
                    (*b.right).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                Ok(Sub::new(l, r).into())
            }
            Obj::Mul(b) => {
                let l = self.eval_reduce_nested_sum_product_in_obj(
                    (*b.left).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let r = self.eval_reduce_nested_sum_product_in_obj(
                    (*b.right).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                Ok(Mul::new(l, r).into())
            }
            Obj::Div(b) => {
                let l = self.eval_reduce_nested_sum_product_in_obj(
                    (*b.left).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let r = self.eval_reduce_nested_sum_product_in_obj(
                    (*b.right).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                Ok(Div::new(l, r).into())
            }
            Obj::Mod(m) => {
                let l = self.eval_reduce_nested_sum_product_in_obj(
                    (*m.left).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let r = self.eval_reduce_nested_sum_product_in_obj(
                    (*m.right).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                Ok(Mod::new(l, r).into())
            }
            Obj::IntegerQuotient(q) => {
                let dividend = self.eval_reduce_nested_sum_product_in_obj(
                    (*q.dividend).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let divisor = self.eval_reduce_nested_sum_product_in_obj(
                    (*q.divisor).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                Ok(IntegerQuotient::new(dividend, divisor).into())
            }
            Obj::Pow(p) => {
                let base = self.eval_reduce_nested_sum_product_in_obj(
                    (*p.base).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let exp = self.eval_reduce_nested_sum_product_in_obj(
                    (*p.exponent).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                Ok(Pow::new(base, exp).into())
            }
            Obj::Abs(a) => {
                let arg = self.eval_reduce_nested_sum_product_in_obj(
                    (*a.arg).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                Ok(Abs::new(arg).into())
            }
            Obj::Log(l) => {
                let b = self.eval_reduce_nested_sum_product_in_obj(
                    (*l.base).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let x = self.eval_reduce_nested_sum_product_in_obj(
                    (*l.arg).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                Ok(Log::new(b, x).into())
            }
            Obj::Max(m) => {
                let l = self.eval_reduce_nested_sum_product_in_obj(
                    (*m.left).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let r = self.eval_reduce_nested_sum_product_in_obj(
                    (*m.right).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                Ok(Max::new(l, r).into())
            }
            Obj::Min(m) => {
                let l = self.eval_reduce_nested_sum_product_in_obj(
                    (*m.left).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let r = self.eval_reduce_nested_sum_product_in_obj(
                    (*m.right).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
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
        active_fn_calls: &mut HashSet<ObjString>,
    ) -> Result<Obj, RuntimeError> {
        let start_ev = self.evaluate_symbol_obj_iterative_with_active(
            start.clone(),
            eval_stmt,
            active_fn_calls,
        )?;
        let end_ev = self.evaluate_symbol_obj_iterative_with_active(
            end.clone(),
            eval_stmt,
            active_fn_calls,
        )?;
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
        let mut acc_obj: Obj = if is_product {
            Number::new("1".to_string()).into()
        } else {
            Number::new("0".to_string()).into()
        };
        for k in ai..=bi {
            let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
            param_to_arg_map.insert(pname.clone(), Number::new(k.to_string()).into());
            let inst =
                self.inst_obj(af.equal_to.as_ref(), &param_to_arg_map, ParamObjType::FnSet)?;
            let term = self.resolve_obj(&inst);
            let term =
                self.eval_reduce_nested_sum_product_in_obj(term, eval_stmt, active_fn_calls)?;
            let Some(n) = Self::evaluate_numeric_obj_for_eval(&term) else {
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
                let step: Obj = Mul::new(acc_obj, n).into();
                acc_obj = Self::evaluate_numeric_obj_for_eval(&step).ok_or_else(|| {
                    short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: product accumulation failed to normalize".to_string(),
                        None,
                        vec![],
                    )
                })?;
            } else {
                let step: Obj = Add::new(acc_obj, n).into();
                acc_obj = Self::evaluate_numeric_obj_for_eval(&step).ok_or_else(|| {
                    short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: sum accumulation failed to normalize".to_string(),
                        None,
                        vec![],
                    )
                })?;
            }
        }
        Ok(acc_obj)
    }

    fn eval_matrix_list_cells_for_eval_stmt(
        &mut self,
        m: MatrixListObj,
        eval_stmt: &EvalStmt,
        active_fn_calls: &mut HashSet<ObjString>,
    ) -> Result<MatrixListObj, RuntimeError> {
        let mut rows_out = Vec::with_capacity(m.rows.len());
        for row in m.rows {
            let mut out_row = Vec::with_capacity(row.len());
            for cell in row {
                let v = self.evaluate_symbol_obj_iterative_with_active(
                    *cell,
                    eval_stmt,
                    active_fn_calls,
                )?;
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
                let Some(n) = Self::evaluate_numeric_obj_for_eval(&sum_obj) else {
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: matrix ++ needs numeric cells".to_string(),
                        None,
                        vec![],
                    ));
                };
                row.push(Box::new(n));
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
                let Some(n) = Self::evaluate_numeric_obj_for_eval(&diff_obj) else {
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: matrix -- needs numeric cells".to_string(),
                        None,
                        vec![],
                    ));
                };
                row.push(Box::new(n));
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
        let c1 = if r1 == 0 { 0 } else { left.rows[0].len() };
        let r2 = right.rows.len();
        let c2 = if r2 == 0 { 0 } else { right.rows[0].len() };
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
                let mut acc_obj: Obj = Number::new("0".to_string()).into();
                for j in 0..c1 {
                    let prod_obj: Obj =
                        Mul::new((*left.rows[i][j]).clone(), (*right.rows[j][k]).clone()).into();
                    let Some(p) = Self::evaluate_numeric_obj_for_eval(&prod_obj) else {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: matrix ** cell multiply failed".to_string(),
                            None,
                            vec![],
                        ));
                    };
                    let sum_obj: Obj = Add::new(acc_obj, p).into();
                    let Some(s) = Self::evaluate_numeric_obj_for_eval(&sum_obj) else {
                        return Err(short_exec_error(
                            eval_stmt.clone().into(),
                            "eval: matrix ** accumulation failed".to_string(),
                            None,
                            vec![],
                        ));
                    };
                    acc_obj = s;
                }
                row.push(Box::new(acc_obj));
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
                let Some(n) = Self::evaluate_numeric_obj_for_eval(&prod_obj) else {
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: *. needs scalar and numeric matrix cells".to_string(),
                        None,
                        vec![],
                    ));
                };
                out_row.push(Box::new(n));
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
        active_fn_calls: &mut HashSet<ObjString>,
    ) -> Result<MatrixListObj, RuntimeError> {
        let cur = match obj {
            Obj::FnObj(fn_obj) => {
                self.evaluate_fn_obj_with_eval_memo(&fn_obj, eval_stmt, active_fn_calls)?
            }
            other => other,
        };
        match cur {
            Obj::MatrixListObj(m) => {
                self.eval_matrix_list_cells_for_eval_stmt(m, eval_stmt, active_fn_calls)
            }
            Obj::MatrixAdd(ma) => {
                let l = self.eval_to_matrix_list_for_eval_stmt(
                    (*ma.left).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let r = self.eval_to_matrix_list_for_eval_stmt(
                    (*ma.right).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                self.add_matrix_lists_under_eval(l, r, eval_stmt)
            }
            Obj::MatrixSub(ms) => {
                let l = self.eval_to_matrix_list_for_eval_stmt(
                    (*ms.left).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let r = self.eval_to_matrix_list_for_eval_stmt(
                    (*ms.right).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                self.sub_matrix_lists_under_eval(l, r, eval_stmt)
            }
            Obj::MatrixMul(mm) => {
                let l = self.eval_to_matrix_list_for_eval_stmt(
                    (*mm.left).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let r = self.eval_to_matrix_list_for_eval_stmt(
                    (*mm.right).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                self.multiply_matrix_lists_under_eval(l, r, eval_stmt)
            }
            Obj::MatrixScalarMul(m) => {
                let s = self.evaluate_symbol_obj_iterative_with_active(
                    (*m.scalar).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let mat = self.eval_to_matrix_list_for_eval_stmt(
                    (*m.matrix).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                self.scalar_matrix_mul_under_eval(s, mat, eval_stmt)
            }
            Obj::MatrixPow(mp) => {
                let base = self.eval_to_matrix_list_for_eval_stmt(
                    (*mp.base).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let exp_obj = self.evaluate_symbol_obj_iterative_with_active(
                    (*mp.exponent).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                let Some(exp_i) = Self::integer_value_for_eval_obj(&exp_obj) else {
                    return Err(short_exec_error(
                        eval_stmt.clone().into(),
                        "eval: matrix ^^ exponent must evaluate to an integer".to_string(),
                        None,
                        vec![],
                    ));
                };
                let exp_u = usize::try_from(exp_i).map_err(|_| {
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
                self.eval_to_matrix_list_for_eval_stmt(ml.into(), eval_stmt, active_fn_calls)
            }
        }
    }

    fn finish_numeric_accumulator_with_pending_rights(
        &mut self,
        acc: Obj,
        pending: &mut Vec<PendingRight>,
        eval_stmt: &EvalStmt,
        active_fn_calls: &mut HashSet<ObjString>,
    ) -> Result<Obj, RuntimeError> {
        let mut acc = acc;
        while let Some(pend) = pending.pop() {
            let (combine_op, right_obj) = match pend {
                PendingRight::Add(o) => (BinaryCombineOp::Add, o),
                PendingRight::Sub(o) => (BinaryCombineOp::Sub, o),
                PendingRight::Mul(o) => (BinaryCombineOp::Mul, o),
                PendingRight::Div(o) => (BinaryCombineOp::Div, o),
            };
            let right_eval = self.evaluate_symbol_obj_iterative_with_active(
                right_obj,
                eval_stmt,
                active_fn_calls,
            )?;
            acc = self.combine_two_numeric_objs(acc, right_eval, combine_op, eval_stmt)?;
        }
        Ok(acc)
    }

    /// Evaluates numeric expressions for `eval` without deep recursion on the Rust stack.
    /// Algorithm calls use an eval-local memo; `Add`/`Sub`/`Mul`/`Div` use an explicit stack for the left spine.
    fn evaluate_symbol_obj_iterative(
        &mut self,
        initial: Obj,
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        let mut active_fn_calls: HashSet<ObjString> = HashSet::new();
        self.evaluate_symbol_obj_iterative_with_active(initial, eval_stmt, &mut active_fn_calls)
    }

    fn evaluate_symbol_obj_iterative_with_active(
        &mut self,
        initial: Obj,
        eval_stmt: &EvalStmt,
        active_fn_calls: &mut HashSet<ObjString>,
    ) -> Result<Obj, RuntimeError> {
        let mut pending: Vec<PendingRight> = Vec::new();
        let mut cur = initial;

        loop {
            match cur {
                Obj::FnObj(fn_obj) => {
                    cur =
                        self.evaluate_fn_obj_with_eval_memo(&fn_obj, eval_stmt, active_fn_calls)?;
                    continue;
                }
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
                        active_fn_calls,
                    );
                }
                Obj::Pow(pow) => {
                    let left = self.evaluate_symbol_obj_iterative_with_active(
                        (*pow.base).clone(),
                        eval_stmt,
                        active_fn_calls,
                    )?;
                    let right = self.evaluate_symbol_obj_iterative_with_active(
                        (*pow.exponent).clone(),
                        eval_stmt,
                        active_fn_calls,
                    )?;
                    let combined: Obj = Pow::new(left, right).into();
                    match Self::evaluate_numeric_obj_for_eval(&combined) {
                        Some(acc_num) => {
                            return self.finish_numeric_accumulator_with_pending_rights(
                                acc_num,
                                &mut pending,
                                eval_stmt,
                                active_fn_calls,
                            );
                        }
                        None => {
                            if pending.is_empty() {
                                return Ok(combined);
                            }
                            return Err(short_exec_error(
                                eval_stmt.clone().into(),
                                "eval: non-numeric power with pending binary operation".to_string(),
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
                        active_fn_calls,
                    )?;
                    return self.finish_numeric_accumulator_with_pending_rights(
                        v,
                        &mut pending,
                        eval_stmt,
                        active_fn_calls,
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
                        active_fn_calls,
                    )?;
                    return self.finish_numeric_accumulator_with_pending_rights(
                        v,
                        &mut pending,
                        eval_stmt,
                        active_fn_calls,
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
                    let done =
                        self.eval_matrix_list_cells_for_eval_stmt(m, eval_stmt, active_fn_calls)?;
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
                    let done = self.eval_to_matrix_list_for_eval_stmt(
                        Obj::MatrixAdd(ma),
                        eval_stmt,
                        active_fn_calls,
                    )?;
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
                    let done = self.eval_to_matrix_list_for_eval_stmt(
                        Obj::MatrixSub(ms),
                        eval_stmt,
                        active_fn_calls,
                    )?;
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
                    let done = self.eval_to_matrix_list_for_eval_stmt(
                        Obj::MatrixMul(mm),
                        eval_stmt,
                        active_fn_calls,
                    )?;
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
                    let done = self.eval_to_matrix_list_for_eval_stmt(
                        Obj::MatrixScalarMul(m),
                        eval_stmt,
                        active_fn_calls,
                    )?;
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
                    let done = self.eval_to_matrix_list_for_eval_stmt(
                        Obj::MatrixPow(mp),
                        eval_stmt,
                        active_fn_calls,
                    )?;
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
        let calculated = Self::evaluate_numeric_obj_for_eval(&combined);
        match calculated {
            Some(number) => Ok(number),
            None => Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: failed to combine numeric sub-expression".to_string(),
                None,
                vec![],
            )),
        }
    }

    fn evaluate_numeric_obj_for_eval(obj: &Obj) -> Option<Obj> {
        evaluate_obj_to_exact_rational_obj_for_eval(obj).or_else(|| {
            obj.evaluate_to_normalized_decimal_number()
                .map(|number| number.into())
        })
    }

    fn evaluate_fn_obj_with_eval_memo(
        &mut self,
        fn_obj_to_evaluate: &FnObj,
        eval_stmt: &EvalStmt,
        active_fn_calls: &mut HashSet<ObjString>,
    ) -> Result<Obj, RuntimeError> {
        let (evaluated_fn_obj, flattened_number_args) = self
            .evaluate_fn_obj_number_args_for_eval_stmt(
                fn_obj_to_evaluate,
                eval_stmt,
                active_fn_calls,
            )?;
        let evaluated_call_obj: Obj = evaluated_fn_obj.clone().into();
        if let Some(number) = self.resolve_obj_to_number(&evaluated_call_obj) {
            return Ok(number.into());
        }

        if let Some(evaluated) = self.try_evaluate_unary_integer_algo_bottom_up(
            &evaluated_fn_obj,
            &flattened_number_args,
            eval_stmt,
            active_fn_calls,
        )? {
            return Ok(evaluated);
        }

        let call_key = evaluated_call_obj.to_string();
        if active_fn_calls.contains(&call_key) {
            return Err(short_exec_error(
                eval_stmt.clone().into(),
                format!(
                    "eval: recursive algorithm call `{}` is already being evaluated",
                    call_key
                ),
                None,
                vec![],
            ));
        }

        active_fn_calls.insert(call_key.clone());
        let fn_name = evaluated_fn_obj.head.to_string();
        let return_expr = self.dispatch_algo_one_return_expr_with_number_args(
            &fn_name,
            &flattened_number_args,
            eval_stmt,
        );
        let evaluated_result = match return_expr {
            Ok(expr) => {
                self.evaluate_symbol_obj_iterative_with_active(expr, eval_stmt, active_fn_calls)
            }
            Err(error) => Err(error),
        };
        active_fn_calls.remove(&call_key);

        let evaluated_obj = evaluated_result?;
        if let Some(number) = self.resolve_obj_to_number(&evaluated_obj) {
            let number_obj: Obj = number.clone().into();
            self.top_level_env()
                .known_obj_values
                .insert(call_key, KnownObjValue::SimplifiedNumber(number));
            let evaluated_equal_fact =
                EqualFact::new(evaluated_call_obj, number_obj, eval_stmt.line_file.clone());
            self.top_level_env().store_equality(&evaluated_equal_fact)?;
        }
        Ok(evaluated_obj)
    }

    fn try_evaluate_unary_integer_algo_bottom_up(
        &mut self,
        evaluated_fn_obj: &FnObj,
        flattened_number_args: &[Obj],
        eval_stmt: &EvalStmt,
        active_fn_calls: &mut HashSet<ObjString>,
    ) -> Result<Option<Obj>, RuntimeError> {
        if flattened_number_args.len() != 1 {
            return Ok(None);
        }
        let Some(target_value) = Self::integer_value_for_eval_obj(&flattened_number_args[0]) else {
            return Ok(None);
        };

        let fn_name = evaluated_fn_obj.head.to_string();
        let Some(algo_definition) = self.get_algo_definition_by_name(&fn_name) else {
            return Ok(None);
        };
        if algo_definition.params.len() != 1 {
            return Ok(None);
        }
        let Some((start_value, _tail_bound)) =
            Self::unary_integer_algo_base_range(&algo_definition, &algo_definition.params[0])
        else {
            return Ok(None);
        };
        if target_value < start_value {
            return Ok(None);
        }

        let mut last_value_obj: Option<Obj> = None;
        for current_value in start_value..=target_value {
            let current_number_obj: Obj = Number::new(current_value.to_string()).into();
            let current_fn_obj = FnObj::new(
                evaluated_fn_obj.head.as_ref().clone(),
                vec![vec![Box::new(current_number_obj.clone())]],
            );
            let current_call_obj: Obj = current_fn_obj.clone().into();
            if let Some(number) = self.resolve_obj_to_number(&current_call_obj) {
                last_value_obj = Some(number.into());
                continue;
            }

            let call_key = current_call_obj.to_string();
            if active_fn_calls.contains(&call_key) {
                return Ok(None);
            }
            active_fn_calls.insert(call_key.clone());
            let return_expr = self.dispatch_algo_one_return_expr_with_number_args(
                &fn_name,
                &[current_number_obj],
                eval_stmt,
            );
            let evaluated_result = match return_expr {
                Ok(expr) => {
                    self.evaluate_symbol_obj_iterative_with_active(expr, eval_stmt, active_fn_calls)
                }
                Err(error) => Err(error),
            };
            active_fn_calls.remove(&call_key);

            let evaluated_obj = evaluated_result?;
            let Some(number) = self.resolve_obj_to_number(&evaluated_obj) else {
                return Ok(None);
            };
            let number_obj: Obj = number.clone().into();
            self.top_level_env()
                .known_obj_values
                .insert(call_key, KnownObjValue::SimplifiedNumber(number));
            let evaluated_equal_fact = EqualFact::new(
                current_call_obj,
                number_obj.clone(),
                eval_stmt.line_file.clone(),
            );
            self.top_level_env().store_equality(&evaluated_equal_fact)?;
            last_value_obj = Some(number_obj);
        }

        Ok(last_value_obj)
    }

    fn integer_value_for_eval_obj(obj: &Obj) -> Option<i128> {
        if let Some(rational) = evaluate_obj_to_exact_rational_for_eval(obj) {
            return rational.to_i128_if_integer();
        }
        let Obj::Number(number) = obj else {
            return None;
        };
        if !is_number_string_literally_integer_without_dot(number.normalized_value.clone()) {
            return None;
        }
        number.normalized_value.parse::<i128>().ok()
    }

    fn unary_integer_algo_base_range(
        algo_definition: &DefAlgoStmt,
        param_name: &str,
    ) -> Option<(i128, i128)> {
        let mut equal_values: Vec<i128> = Vec::new();
        let mut tail_bounds: Vec<i128> = Vec::new();
        for algo_case in algo_definition.cases.iter() {
            if let Some(value) =
                Self::equal_case_integer_value_for_param(&algo_case.condition, param_name)
            {
                equal_values.push(value);
            }
            if let Some(value) = Self::strict_upper_tail_case_integer_value_for_param(
                &algo_case.condition,
                param_name,
            ) {
                tail_bounds.push(value);
            }
        }
        if tail_bounds.len() != 1 || equal_values.is_empty() {
            return None;
        }
        let start = *equal_values.iter().min()?;
        let max_equal = *equal_values.iter().max()?;
        let tail_bound = tail_bounds[0];
        if max_equal != tail_bound {
            return None;
        }
        for value in start..=tail_bound {
            if !equal_values.contains(&value) {
                return None;
            }
        }
        Some((start, tail_bound))
    }

    fn equal_case_integer_value_for_param(
        atomic_fact: &AtomicFact,
        param_name: &str,
    ) -> Option<i128> {
        let AtomicFact::EqualFact(equal) = atomic_fact else {
            return None;
        };
        let param_obj = obj_for_bound_param_in_scope(param_name.to_string(), ParamObjType::DefAlgo);
        if equal.left.to_string() == param_obj.to_string() {
            return Self::integer_value_for_eval_obj(&equal.right);
        }
        if equal.right.to_string() == param_obj.to_string() {
            return Self::integer_value_for_eval_obj(&equal.left);
        }
        None
    }

    fn strict_upper_tail_case_integer_value_for_param(
        atomic_fact: &AtomicFact,
        param_name: &str,
    ) -> Option<i128> {
        let param_obj = obj_for_bound_param_in_scope(param_name.to_string(), ParamObjType::DefAlgo);
        match atomic_fact {
            AtomicFact::GreaterFact(greater)
                if greater.left.to_string() == param_obj.to_string() =>
            {
                Self::integer_value_for_eval_obj(&greater.right)
            }
            AtomicFact::LessFact(less) if less.right.to_string() == param_obj.to_string() => {
                Self::integer_value_for_eval_obj(&less.left)
            }
            _ => None,
        }
    }

    fn evaluate_fn_obj_number_args_for_eval_stmt(
        &mut self,
        fn_obj_to_evaluate: &FnObj,
        eval_stmt: &EvalStmt,
        active_fn_calls: &mut HashSet<ObjString>,
    ) -> Result<(FnObj, Vec<Obj>), RuntimeError> {
        let mut flattened_number_args: Vec<Obj> = Vec::new();
        let mut evaluated_arg_groups: Vec<Vec<Box<Obj>>> =
            Vec::with_capacity(fn_obj_to_evaluate.body.len());
        for arg_group in fn_obj_to_evaluate.body.iter() {
            let mut evaluated_arg_group: Vec<Box<Obj>> = Vec::with_capacity(arg_group.len());
            for arg in arg_group.iter() {
                let evaluated_arg_obj = self.evaluate_symbol_obj_iterative_with_active(
                    (**arg).clone(),
                    eval_stmt,
                    active_fn_calls,
                )?;
                match evaluated_arg_obj {
                    Obj::Number(number) => {
                        let number_obj: Obj = number.into();
                        flattened_number_args.push(number_obj.clone());
                        evaluated_arg_group.push(Box::new(number_obj));
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
            evaluated_arg_groups.push(evaluated_arg_group);
        }
        Ok((
            FnObj::new(
                fn_obj_to_evaluate.head.as_ref().clone(),
                evaluated_arg_groups,
            ),
            flattened_number_args,
        ))
    }

    /// One algo step: bind numeric args, match case / default, return **instantiated** return expression only (no recursive eval).
    fn dispatch_algo_one_return_expr_with_number_args(
        &mut self,
        fn_name: &str,
        flattened_number_args: &[Obj],
        eval_stmt: &EvalStmt,
    ) -> Result<Obj, RuntimeError> {
        let algo_definition = match self.get_algo_definition_by_name(&fn_name) {
            Some(definition) => definition,
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
            let instantiated_case_condition = self.inst_atomic_fact(
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
                return self.inst_obj(
                    &algo_case.return_stmt.value,
                    &param_to_arg_map,
                    ParamObjType::DefAlgo,
                );
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
            self.inst_obj(
                &default_return_stmt.value,
                &param_to_arg_map,
                ParamObjType::DefAlgo,
            )
        } else {
            Err(short_exec_error(
                eval_stmt.clone().into(),
                "eval: no case matched and no default return".to_string(),
                None,
                vec![],
            ))
        }
    }

    fn evaluate_obj_for_eval_stmt(&mut self, stmt: &EvalStmt) -> Result<Obj, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(
            &stmt.obj_to_eval,
            &VerifyState::new(0, false),
        )?;

        let resolved_obj = self.resolve_obj(&stmt.obj_to_eval);
        let executable_obj = self
            .executable_definition_for_eval_identifier(&resolved_obj)
            .unwrap_or(resolved_obj);
        self.run_in_local_env(|rt| {
            if !Self::object_supported_by_eval_stmt(&executable_obj) {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    "eval: need a function call, numeric expression (+ - * / ^), sum/product over a unary anonymous body, or matrix ++ -- ** *. ^^ / matrix literal"
                        .to_string(),
                    None,
                    vec![],
                ));
            }
            rt.evaluate_symbol_obj_iterative(executable_obj, stmt)
        })
    }

    fn executable_definition_for_eval_identifier(&self, obj: &Obj) -> Option<Obj> {
        if !matches!(obj, Obj::Atom(AtomObj::Identifier(_))) {
            return None;
        }

        self.get_all_obj_representatives_equal_to_given(obj)
            .into_iter()
            .map(|candidate| self.resolve_obj(&candidate))
            .find(|candidate| {
                !matches!(candidate, Obj::Atom(AtomObj::Identifier(_)))
                    && Self::object_supported_by_eval_stmt(candidate)
            })
    }

    pub fn exec_eval_stmt(&mut self, stmt: &EvalStmt) -> Result<StmtResult, RuntimeError> {
        let evaluated_obj = self.evaluate_obj_for_eval_stmt(stmt)?;
        let evaluated_equal_fact = EqualFact::new(
            stmt.obj_to_eval.clone(),
            evaluated_obj,
            stmt.line_file.clone(),
        )
        .into();

        let infer_result = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
                evaluated_equal_fact,
                InferReason::Evaluation,
            )?;

        let reported_store_facts = infer_result.store_fact_outputs().to_vec();
        Ok(
            (NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![])
                .with_reported_store_facts(reported_store_facts))
            .into(),
        )
    }
}
