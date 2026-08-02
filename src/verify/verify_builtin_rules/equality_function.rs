use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::factual_equal_success_by_builtin_reason;

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
            .verify_objs_are_equal_by_known_equality(&power.exponent, &one, line_file.clone())
            .is_unknown()
            && !self
                .verify_objs_are_equal_by_known_equality(&power.base, other_side, line_file.clone())
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
            .verify_objs_are_equal_by_known_equality(&exponent.right, &one, line_file.clone())
            .is_unknown()
        {
            exponent.left.as_ref()
        } else if !self
            .verify_objs_are_equal_by_known_equality(&exponent.left, &one, line_file.clone())
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
            self.verify_objs_are_equal_by_known_equality(left, right, line_file.clone())
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

    // Beta-reduction for anonymous `fn` heads: if argument lists match the parameter list, substitute
    // into the braced `equal_to` body and require that to equal the other side (same as evaluation).
    pub(crate) fn try_verify_anonymous_fn_application_equals_other_side(
        &mut self,
        statement_left: &Obj,
        statement_right: &Obj,
        application_side: &Obj,
        other_side: &Obj,
        line_file: LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
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
            builtin_state,
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
