//! Anonymous-function body and parameter application matching.

use super::*;

impl ArgMatcher<'_> {
    pub(super) fn match_arg_in_anonymous_fn_body_with_given_arg(
        &mut self,
        known_arg: &Obj,
        given_arg: &Obj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if let Some(existing_match) =
            self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(known_arg, given_arg)?
        {
            return Ok(Some(existing_match));
        }
        if let Some(function_param_match) = self
            .match_forall_function_param_application_as_anonymous_fn(
                known_arg,
                given_arg,
                anonymous_fn_body,
            )?
        {
            return Ok(Some(function_param_match));
        }

        match (known_arg, given_arg) {
            (Obj::FnObj(left), Obj::FnObj(given)) => {
                self.match_fn_obj_in_anonymous_fn_body(left, given, anonymous_fn_body)
            }
            (Obj::Add(left), Obj::Add(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Sub(left), Obj::Sub(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Mul(left), Obj::Mul(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Div(left), Obj::Div(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Mod(left), Obj::Mod(given)) => self.match_binary_in_anonymous_fn_body(
                left.left.as_ref(),
                left.right.as_ref(),
                given.left.as_ref(),
                given.right.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Pow(left), Obj::Pow(given)) => self.match_binary_in_anonymous_fn_body(
                left.base.as_ref(),
                left.exponent.as_ref(),
                given.base.as_ref(),
                given.exponent.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::MatrixAdd(left), Obj::MatrixAdd(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.left.as_ref(),
                    left.right.as_ref(),
                    given.left.as_ref(),
                    given.right.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixSub(left), Obj::MatrixSub(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.left.as_ref(),
                    left.right.as_ref(),
                    given.left.as_ref(),
                    given.right.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixMul(left), Obj::MatrixMul(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.left.as_ref(),
                    left.right.as_ref(),
                    given.left.as_ref(),
                    given.right.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixScalarMul(left), Obj::MatrixScalarMul(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.scalar.as_ref(),
                    left.matrix.as_ref(),
                    given.scalar.as_ref(),
                    given.matrix.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::MatrixPow(left), Obj::MatrixPow(given)) => self
                .match_binary_in_anonymous_fn_body(
                    left.base.as_ref(),
                    left.exponent.as_ref(),
                    given.base.as_ref(),
                    given.exponent.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Abs(left), Obj::Abs(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Sin(left), Obj::Sin(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Arcsin(left), Obj::Arcsin(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Cos(left), Obj::Cos(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Tan(left), Obj::Tan(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Cot(left), Obj::Cot(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Sqrt(left), Obj::Sqrt(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Exp(left), Obj::Exp(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Ln(left), Obj::Ln(given)) => self.match_arg_in_anonymous_fn_body_with_given_arg(
                left.arg.as_ref(),
                given.arg.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::Sign(left), Obj::Sign(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Factorial(left), Obj::Factorial(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.arg.as_ref(),
                    given.arg.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Log(left), Obj::Log(given)) => self.match_binary_in_anonymous_fn_body(
                left.base.as_ref(),
                left.arg.as_ref(),
                given.base.as_ref(),
                given.arg.as_ref(),
                anonymous_fn_body,
            ),
            (Obj::FiniteSetSize(left), Obj::FiniteSetSize(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.set.as_ref(),
                    given.set.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::FiniteSetMax(left), Obj::FiniteSetMax(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.set.as_ref(),
                    given.set.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::FiniteSetMin(left), Obj::FiniteSetMin(given)) => self
                .match_arg_in_anonymous_fn_body_with_given_arg(
                    left.set.as_ref(),
                    given.set.as_ref(),
                    anonymous_fn_body,
                ),
            (Obj::Tuple(left), Obj::Tuple(given)) => self.match_boxed_args_in_anonymous_fn_body(
                &left.args,
                &given.args,
                anonymous_fn_body,
            ),
            (Obj::Cart(left), Obj::Cart(given)) => self.match_boxed_args_in_anonymous_fn_body(
                &left.args,
                &given.args,
                anonymous_fn_body,
            ),
            (Obj::ListSet(left), Obj::ListSet(given)) => self
                .match_boxed_args_in_anonymous_fn_body(&left.list, &given.list, anonymous_fn_body),
            (Obj::FiniteSeqListObj(left), Obj::FiniteSeqListObj(given)) => self
                .match_boxed_args_in_anonymous_fn_body(&left.objs, &given.objs, anonymous_fn_body),
            _ => Ok(None),
        }
    }

    pub(super) fn match_fn_obj_in_anonymous_fn_body(
        &mut self,
        left: &FnObj,
        given: &FnObj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.body.len() != given.body.len() {
            return Ok(None);
        }
        let left_head: Obj = left.head.as_ref().clone().into();
        let given_head: Obj = given.head.as_ref().clone().into();
        let Some(mut merged) = self.match_arg_in_anonymous_fn_body_with_given_arg(
            &left_head,
            &given_head,
            anonymous_fn_body,
        )?
        else {
            return Ok(None);
        };

        for (left_row, given_row) in left.body.iter().zip(given.body.iter()) {
            if left_row.len() != given_row.len() {
                return Ok(None);
            }
            let Some(row_map) =
                self.match_boxed_args_in_anonymous_fn_body(left_row, given_row, anonymous_fn_body)?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, row_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    pub(super) fn match_binary_in_anonymous_fn_body(
        &mut self,
        left_left: &Obj,
        left_right: &Obj,
        given_left: &Obj,
        given_right: &Obj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Some(mut merged) = self.match_arg_in_anonymous_fn_body_with_given_arg(
            left_left,
            given_left,
            anonymous_fn_body,
        )?
        else {
            return Ok(None);
        };
        let Some(right_map) = self.match_arg_in_anonymous_fn_body_with_given_arg(
            left_right,
            given_right,
            anonymous_fn_body,
        )?
        else {
            return Ok(None);
        };
        if !self.merge_arg_match_map_into(&mut merged, right_map) {
            return Ok(None);
        }
        Ok(Some(merged))
    }

    pub(super) fn match_boxed_args_in_anonymous_fn_body(
        &mut self,
        left: &[Box<Obj>],
        given: &[Box<Obj>],
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        if left.len() != given.len() {
            return Ok(None);
        }
        let mut merged = HashMap::new();
        for (left_arg, given_arg) in left.iter().zip(given.iter()) {
            let Some(sub_map) = self.match_arg_in_anonymous_fn_body_with_given_arg(
                left_arg.as_ref(),
                given_arg.as_ref(),
                anonymous_fn_body,
            )?
            else {
                return Ok(None);
            };
            if !self.merge_arg_match_map_into(&mut merged, sub_map) {
                return Ok(None);
            }
        }
        Ok(Some(merged))
    }

    pub(super) fn match_forall_function_param_application_as_anonymous_fn(
        &mut self,
        known_arg: &Obj,
        given_arg: &Obj,
        anonymous_fn_body: &FnSetBody,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        let Obj::FnObj(fn_obj) = known_arg else {
            return Ok(None);
        };
        let FnObjHead::Bound(forall_param) = fn_obj.head.as_ref() else {
            return Ok(None);
        };
        if !self.arg_match_binding_is_active(&forall_param.symbol) {
            return Ok(None);
        }
        if !Self::fn_obj_applies_to_exact_anonymous_fn_params(fn_obj, anonymous_fn_body) {
            return Ok(None);
        }

        // Prefer the callable prefix when the given body is itself an
        // application to the same anonymous-function binders.  For example,
        // matching `F(K)` against `rows(p,q,h,k)(K)` must bind `F` to
        // `rows(p,q,h,k)`, not synthesize `fn(K) {rows(...)(K)}` with the
        // surrounding anonymous summand's return type.
        if let Obj::FnObj(given_fn_obj) = given_arg {
            let applied_group_count = fn_obj.body.len();
            if given_fn_obj.body.len() >= applied_group_count {
                let prefix_group_count = given_fn_obj.body.len() - applied_group_count;
                let given_suffix = &given_fn_obj.body[prefix_group_count..];
                let suffix_matches = fn_obj.body.iter().zip(given_suffix.iter()).all(
                    |(known_group, given_group)| {
                        known_group.len() == given_group.len()
                            && known_group
                                .iter()
                                .zip(given_group.iter())
                                .all(|(known, given)| known.to_string() == given.to_string())
                    },
                );
                if suffix_matches {
                    let mut map = HashMap::new();
                    map.insert(
                        arg_match_binding_key(&forall_param.symbol),
                        given_fn_obj.prefix_obj(prefix_group_count),
                    );
                    return Ok(Some(map));
                }

                // A named application may contribute its callable prefix only
                // when its complete suffix is exactly the surrounding
                // anonymous-function binder application.  Falling through here
                // would instead synthesize a lambda from, for example,
                // `rows(a)(1)` while matching `F(K)`, silently treating the
                // nonmatching named suffix as if it were `K`.
                return Ok(None);
            }
        }

        let anonymous_fn = AnonymousFn::new(
            anonymous_fn_body.set_bound_parameters.clone(),
            anonymous_fn_body.dom_facts.clone(),
            (*anonymous_fn_body.ret_set).clone(),
            given_arg.clone(),
        )?;
        let mut map = HashMap::new();
        map.insert(
            arg_match_binding_key(&forall_param.symbol),
            anonymous_fn.into(),
        );
        Ok(Some(map))
    }

    pub(super) fn fn_obj_applies_to_exact_anonymous_fn_params(
        fn_obj: &FnObj,
        anonymous_fn_body: &FnSetBody,
    ) -> bool {
        let expected_param_bindings = anonymous_fn_body.get_param_bindings();
        let expected_len = expected_param_bindings.len();
        let actual_args_count: usize = fn_obj.body.iter().map(|row| row.len()).sum();
        if actual_args_count != expected_len {
            return false;
        }

        let mut flat_index = 0;
        for row in fn_obj.body.iter() {
            for arg in row.iter() {
                let expected = obj_for_bound_param_in_scope(&expected_param_bindings[flat_index]);
                if arg.to_string() != expected.to_string() {
                    return false;
                }
                flat_index += 1;
            }
        }
        true
    }

    pub(super) fn match_fn_param_group_type_in_known_forall_with_given(
        &mut self,
        left: &SetBoundParameterGroup,
        given: &SetBoundParameterGroup,
    ) -> Result<Option<HashMap<String, Obj>>, RuntimeError> {
        self.match_arg_in_atomic_fact_in_known_forall_with_given_arg(
            left.set_obj(),
            given.set_obj(),
        )
    }
}
