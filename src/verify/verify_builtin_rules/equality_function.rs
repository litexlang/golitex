use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::factual_equal_success_by_builtin_reason;
use std::collections::HashMap;

impl Runtime {
    /// The positive-power recursion for square real matrices.
    /// Example: `A '^ 1 = A` and `A '^ (k + 1) = (A '^ k) '* A`.
    pub(crate) fn try_verify_matrix_power_definition(
        &self,
        statement_left: &Obj,
        statement_right: &Obj,
        power_side: &Obj,
        other_side: &Obj,
        line_file: LineFile,
    ) -> Option<StmtResult> {
        let Obj::MatrixPow(power) = power_side else {
            return None;
        };
        let one: Obj = Number::new("1".to_string()).into();
        if !self
            .verify_objs_are_equal_known_only(&power.exponent, &one, line_file.clone())
            .is_unknown()
            && !self
                .verify_objs_are_equal_known_only(&power.base, other_side, line_file.clone())
                .is_unknown()
        {
            return Some(factual_equal_success_by_builtin_reason(
                statement_left,
                statement_right,
                line_file,
                "matrix positive power base case: A '^ 1 = A",
            ));
        }

        let Obj::Add(exponent) = power.exponent.as_ref() else {
            return None;
        };
        let predecessor = if !self
            .verify_objs_are_equal_known_only(&exponent.right, &one, line_file.clone())
            .is_unknown()
        {
            exponent.left.as_ref()
        } else if !self
            .verify_objs_are_equal_known_only(&exponent.left, &one, line_file.clone())
            .is_unknown()
        {
            exponent.right.as_ref()
        } else {
            return None;
        };
        let Obj::MatrixMul(product) = other_side else {
            return None;
        };
        let Obj::MatrixPow(previous_power) = product.left.as_ref() else {
            return None;
        };
        let pairs = [
            (power.base.as_ref(), previous_power.base.as_ref()),
            (power.base.as_ref(), product.right.as_ref()),
            (predecessor, previous_power.exponent.as_ref()),
        ];
        if pairs.iter().any(|(left, right)| {
            self.verify_objs_are_equal_known_only(left, right, line_file.clone())
                .is_unknown()
        }) {
            return None;
        }
        Some(factual_equal_success_by_builtin_reason(
            statement_left,
            statement_right,
            line_file,
            "matrix positive power recursion: A '^(k + 1) = (A '^ k) '* A",
        ))
    }

    /// Expand a matrix product entry into its defining finite sum.
    /// Example: `(A '* B)(i, j) = sum(1, n, fn(k N_pos) R {A(i, k) * B(k, j)})`.
    pub(crate) fn try_verify_matrix_product_entry_equals_sum(
        &mut self,
        statement_left: &Obj,
        statement_right: &Obj,
        application_side: &Obj,
        sum_side: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::FnObj(application), Obj::Sum(sum)) = (application_side, sum_side) else {
            return Ok(None);
        };
        let FnObjHead::MatrixOperator(matrix) = application.head.as_ref() else {
            return Ok(None);
        };
        let Obj::MatrixMul(product) = matrix.as_ref() else {
            return Ok(None);
        };
        let args: Vec<Obj> = application
            .body
            .iter()
            .flat_map(|group| group.iter().map(|arg| (**arg).clone()))
            .collect();
        if args.len() != 2 {
            return Ok(None);
        }
        let left_type = self.real_matrix_type(&product.left, verify_state, MATRIX_MUL)?;
        let one: Obj = Number::new("1".to_string()).into();
        if self
            .verify_objs_are_equal_known_only(&sum.start, &one, line_file.clone())
            .is_unknown()
            || self
                .verify_objs_are_equal_known_only(&sum.end, &left_type.col_len, line_file.clone())
                .is_unknown()
        {
            return Ok(None);
        }
        let Obj::AnonymousFn(function) = sum.func.as_ref() else {
            return Ok(None);
        };
        let params = function.body.get_params();
        if params.len() != 1 {
            return Ok(None);
        }
        let index = obj_for_bound_param_in_scope(params[0].clone(), ParamObjType::FnSet);
        let mut map = HashMap::new();
        map.insert(params[0].clone(), index.clone());
        let actual_term = self.inst_obj(&function.equal_to, &map, ParamObjType::FnSet)?;
        let left_head = FnObjHead::from_callable_obj((*product.left).clone())
            .expect("well-defined matrix operand is callable");
        let right_head = FnObjHead::from_callable_obj((*product.right).clone())
            .expect("well-defined matrix operand is callable");
        let expected_term: Obj = Mul::new(
            FnObj::new(
                left_head,
                vec![vec![Box::new(args[0].clone()), Box::new(index.clone())]],
            )
            .into(),
            FnObj::new(
                right_head,
                vec![vec![Box::new(index), Box::new(args[1].clone())]],
            )
            .into(),
        )
        .into();
        let term_result = self.verify_objs_are_equal_in_equality_builtin(
            &actual_term,
            &expected_term,
            line_file.clone(),
            verify_state,
        )?;
        if term_result.is_unknown() {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            statement_left,
            statement_right,
            line_file,
            "matrix multiplication entry is the sum of row-column products",
        )))
    }

    // Beta-reduction for anonymous `fn` heads: if argument lists match the parameter list, substitute
    // into the braced `equal_to` body and require that to equal the other side (same as evaluation).
    pub(crate) fn try_verify_anonymous_fn_application_equals_other_side(
        &mut self,
        statement_left: &Obj,
        statement_right: &Obj,
        application_side: &Obj,
        other_side: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::FnObj(fn_obj) = application_side else {
            return Ok(None);
        };
        let FnObjHead::AnonymousFnLiteral(af) = fn_obj.head.as_ref() else {
            return Ok(None);
        };
        if fn_obj.body.is_empty() {
            return Ok(None);
        }
        let param_defs = &af.body.params_def_with_set;
        let n_params = ParamGroupWithSet::number_of_params(param_defs);
        if n_params == 0 {
            return Ok(None);
        }
        let mut args: Vec<Obj> = Vec::new();
        for g in fn_obj.body.iter() {
            for b in g.iter() {
                args.push((**b).clone());
            }
        }
        if args.len() != n_params {
            return Ok(None);
        }
        let param_to_arg_map =
            ParamGroupWithSet::param_defs_and_args_to_param_to_arg_map(param_defs, &args);
        let reduced =
            self.inst_obj(af.equal_to.as_ref(), &param_to_arg_map, ParamObjType::FnSet)?;
        let inner = self.verify_objs_are_equal_in_equality_builtin(
            &reduced,
            other_side,
            line_file.clone(),
            verify_state,
        )?;
        if inner.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                statement_left,
                statement_right,
                line_file,
                "equality: anonymous function application — substitute args into the body, equals the other side",
            )));
        }
        Ok(None)
    }
}
