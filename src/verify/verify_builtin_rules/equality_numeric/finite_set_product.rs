use super::*;

impl Runtime {
    // A finite-set product over the empty set is one.
    // Example: `finite_set_product({}, fn(x Z) Z {x}) = 1`.
    pub(crate) fn try_verify_finite_set_product_empty(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let empty_set: Obj = ListSet::new(vec![]).into();
        let one: Obj = Number::new("1".to_string()).into();
        for (product_side, other) in [(left, right), (right, left)] {
            let Obj::ProductOfFiniteSet(p) = product_side else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    p.set.as_ref(),
                    &empty_set,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &one,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set product over empty set is one",
                )));
            }
        }
        Ok(None)
    }

    // A finite-set product over a displayed finite set expands to the left-associated product
    // of the factor at each listed element. Example:
    // `finite_set_product({1, 2}, fn(x Z) Z {x}) = 1 * 2`.
    pub(crate) fn try_verify_finite_set_product_list_expansion(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (product_side, other) in [(left, right), (right, left)] {
            let Obj::ProductOfFiniteSet(p) = product_side else {
                continue;
            };
            let Obj::ListSet(list_set) = p.set.as_ref() else {
                continue;
            };
            let mut terms = Vec::with_capacity(list_set.list.len());
            for element in list_set.list.iter() {
                let Some(term) =
                    self.instantiate_unary_function_at(p.func.as_ref(), element.as_ref())?
                else {
                    terms.clear();
                    break;
                };
                terms.push(term);
            }
            if terms.len() != list_set.list.len() {
                continue;
            }
            let expected = Self::left_assoc_mul_from_terms(terms);
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &expected,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set product over displayed set expands elementwise",
                )));
            }
        }
        Ok(None)
    }

    // Inserting a fresh element splits a finite-set product into the old product and its factor.
    // Example: from `not x $in S`, prove
    // `finite_set_product(union({x}, S), f) = finite_set_product(S, f|S) * f(x)`.
    pub(crate) fn try_verify_finite_set_product_fresh_insertion(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (union_side, product_side) in [(left, right), (right, left)] {
            let Obj::ProductOfFiniteSet(union_product) = union_side else {
                continue;
            };
            let Obj::Mul(mul) = product_side else {
                continue;
            };
            let Obj::ProductOfFiniteSet(smaller_product) = mul.left.as_ref() else {
                continue;
            };
            let Obj::Union(union) = union_product.set.as_ref() else {
                continue;
            };

            for (singleton_side, smaller_set) in [
                (union.left.as_ref(), union.right.as_ref()),
                (union.right.as_ref(), union.left.as_ref()),
            ] {
                let Obj::ListSet(singleton) = singleton_side else {
                    continue;
                };
                if singleton.list.len() != 1 {
                    continue;
                }
                let inserted = singleton.list[0].as_ref().clone();
                let freshness: AtomicFact =
                    NotInFact::new(inserted.clone(), smaller_set.clone(), line_file.clone()).into();
                if !self
                    .verify_non_equational_known_then_builtin_rules_only(&freshness, verify_state)?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        smaller_product.set.as_ref(),
                        smaller_set,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                if !self
                    .verify_finite_set_sum_functions_pointwise_equal(
                        union_product.func.as_ref(),
                        smaller_product.func.as_ref(),
                        smaller_set.clone(),
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                let Some(inserted_factor) =
                    self.instantiate_unary_function_at(union_product.func.as_ref(), &inserted)?
                else {
                    continue;
                };
                if !self
                    .verify_objs_are_equal_in_equality_builtin(
                        mul.right.as_ref(),
                        &inserted_factor,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
                {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set product after inserting a fresh element",
                )));
            }
        }
        Ok(None)
    }

    // Removing a member splits a finite-set product into the remaining product and that member's factor.
    // Example: from `x $in A`, prove
    // `finite_set_product(A, f) = finite_set_product(set_minus(A, {x}), f|-) * f(x)`.
    pub(crate) fn try_verify_finite_set_product_remove_member(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (full_side, product_side) in [(left, right), (right, left)] {
            let Obj::ProductOfFiniteSet(full_product) = full_side else {
                continue;
            };
            let Obj::Mul(mul) = product_side else {
                continue;
            };
            let Obj::ProductOfFiniteSet(remaining_product) = mul.left.as_ref() else {
                continue;
            };
            let Obj::SetMinus(remaining_set) = remaining_product.set.as_ref() else {
                continue;
            };
            let Obj::ListSet(singleton) = remaining_set.right.as_ref() else {
                continue;
            };
            if singleton.list.len() != 1 {
                continue;
            }
            let removed = singleton.list[0].as_ref().clone();
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    full_product.set.as_ref(),
                    remaining_set.left.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let membership: AtomicFact = InFact::new(
                removed.clone(),
                full_product.set.as_ref().clone(),
                line_file.clone(),
            )
            .into();
            if !self
                .verify_non_equational_known_then_builtin_rules_only(&membership, verify_state)?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_finite_set_sum_functions_pointwise_equal(
                    full_product.func.as_ref(),
                    remaining_product.func.as_ref(),
                    remaining_product.set.as_ref().clone(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let Some(removed_factor) =
                self.instantiate_unary_function_at(full_product.func.as_ref(), &removed)?
            else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    mul.right.as_ref(),
                    &removed_factor,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set product after removing a member",
            )));
        }
        Ok(None)
    }

    // A finite-set product over an integer closed range agrees with the existing range product.
    // Example: `finite_set_product(1...3, fn(x Z) Z {x}) = product(1, 3, fn(x Z) Z {x})`.
    pub(crate) fn try_verify_finite_set_product_closed_range_bridge(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (finite_side, range_side) in [(left, right), (right, left)] {
            let Obj::ProductOfFiniteSet(finite_product) = finite_side else {
                continue;
            };
            let Obj::ClosedRange(range) = finite_product.set.as_ref() else {
                continue;
            };
            let Obj::Product(range_product) = range_side else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    range.start.as_ref(),
                    range_product.start.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    range.end.as_ref(),
                    range_product.end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    finite_product.func.as_ref(),
                    range_product.func.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set product over closed integer range equals range product",
            )));
        }
        Ok(None)
    }

    // A constant finite-set factor is the constant raised to the set cardinality.
    // Example: `finite_set_product(X, fn(x X) R {c}) = c ^ finite_set_size(X)`.
    pub(crate) fn try_verify_finite_set_product_constant_factor(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (product_side, other) in [(left, right), (right, left)] {
            let Obj::ProductOfFiniteSet(p) = product_side else {
                continue;
            };
            let af = match p.func.as_ref() {
                Obj::AnonymousFn(af) => af,
                Obj::FnObj(fo) if fo.body.is_empty() => match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                    _ => continue,
                },
                _ => continue,
            };
            if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
                continue;
            }
            let names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
            let pname = match names.first() {
                Some(n) => n.as_str(),
                None => continue,
            };
            if obj_expr_mentions_bare_id(af.equal_to.as_ref(), pname) {
                continue;
            }
            let c = (*af.equal_to).clone();
            let finite_set_size: Obj = FiniteSetSize::new((*p.set).clone()).into();
            let expected: Obj = Pow::new(c, finite_set_size).into();
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &expected,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set product of a constant factor",
                )));
            }
        }
        Ok(None)
    }

    // Finite-set products are equal when their factors are pointwise equal on the same finite set.
    // Example: from `forall x X: f(x) = g(x)`, prove
    // `finite_set_product(X, f) = finite_set_product(X, g)`.
    pub(crate) fn try_verify_finite_set_product_pointwise_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let (left_product, right_product) = match (left, right) {
            (Obj::ProductOfFiniteSet(l), Obj::ProductOfFiniteSet(r)) => (l, r),
            _ => return Ok(None),
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                left_product.set.as_ref(),
                right_product.set.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let x_name = self.generate_random_unused_name();
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
        let Some(left_inst) =
            self.instantiate_unary_function_at(left_product.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(right_inst) =
            self.instantiate_unary_function_at(right_product.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let then_fact: AtomicFact = EqualFact::new(left_inst, right_inst, line_file.clone()).into();
        let r = self.verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
            x_name,
            left_product.set.as_ref().clone(),
            &then_fact,
            verify_state,
        )?;
        if r.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set products from pointwise equality on the finite set",
            )));
        }
        Ok(None)
    }

    pub(super) fn left_assoc_add_from_terms(terms: Vec<Obj>) -> Obj {
        let mut it = terms.into_iter();
        let Some(first) = it.next() else {
            return Number::new("0".to_string()).into();
        };
        let mut acc = first;
        for term in it {
            acc = Add::new(acc, term).into();
        }
        acc
    }

    pub(super) fn left_assoc_mul_from_terms(terms: Vec<Obj>) -> Obj {
        let mut it = terms.into_iter();
        let Some(first) = it.next() else {
            return Number::new("1".to_string()).into();
        };
        let mut acc = first;
        for term in it {
            acc = Mul::new(acc, term).into();
        }
        acc
    }

    pub(super) fn unary_application_arg_matching_callable(
        application: &Obj,
        callable: &Obj,
    ) -> Option<Obj> {
        let Obj::FnObj(fn_obj) = application else {
            return None;
        };
        if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 1 {
            return None;
        }
        let expected_head = FnObjHead::from_callable_obj(callable.clone())?;
        let actual_head_obj: Obj = fn_obj.head.as_ref().clone().into();
        let expected_head_obj: Obj = expected_head.into();
        if !objs_equal_by_display_string(&actual_head_obj, &expected_head_obj) {
            return None;
        }
        Some(fn_obj.body[0][0].as_ref().clone())
    }

    pub(super) fn verify_finite_set_sum_functions_pointwise_equal(
        &mut self,
        left_func: &Obj,
        right_func: &Obj,
        set: Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let x_name = self.generate_random_unused_name();
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
        let Some(left_inst) = self.instantiate_unary_function_at(left_func, &x_obj)? else {
            return Ok(StmtResult::Unknown(StmtUnknown::new()));
        };
        let Some(right_inst) = self.instantiate_unary_function_at(right_func, &x_obj)? else {
            return Ok(StmtResult::Unknown(StmtUnknown::new()));
        };
        let pointwise_fact: AtomicFact = EqualFact::new(left_inst, right_inst, line_file).into();
        self.verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
            x_name,
            set,
            &pointwise_fact,
            verify_state,
        )
    }

    pub(super) fn nested_finite_set_sum_cartesian_shape(
        &mut self,
        obj: &Obj,
        _line_file: LineFile,
        _verify_state: &VerifyState,
    ) -> Result<Option<NestedFiniteSetSumCartesianShape>, RuntimeError> {
        let Obj::SumOfFiniteSet(outer_sum) = obj else {
            return Ok(None);
        };
        let outer_name = self.generate_random_unused_name();
        let outer_obj = obj_for_bound_param_in_scope(outer_name.clone(), ParamObjType::Forall);
        let Some(inner_sum_obj) =
            self.instantiate_unary_function_at(outer_sum.func.as_ref(), &outer_obj)?
        else {
            return Ok(None);
        };
        let Obj::SumOfFiniteSet(inner_sum) = inner_sum_obj else {
            return Ok(None);
        };
        if obj_expr_mentions_bare_id(inner_sum.set.as_ref(), outer_name.as_str()) {
            return Ok(None);
        }

        let inner_name = format!("{}_inner", outer_name);
        let inner_obj = obj_for_bound_param_in_scope(inner_name.clone(), ParamObjType::Forall);
        let Some(summand) =
            self.instantiate_unary_function_at(inner_sum.func.as_ref(), &inner_obj)?
        else {
            return Ok(None);
        };
        let Obj::FnObj(call) = summand else {
            return Ok(None);
        };
        if call.body.len() != 1 || call.body[0].len() != 1 {
            return Ok(None);
        }
        let Obj::Tuple(tuple) = call.body[0][0].as_ref() else {
            return Ok(None);
        };
        if tuple.args.len() != 2 {
            return Ok(None);
        }

        let first_arg = tuple.args[0].as_ref();
        let second_arg = tuple.args[1].as_ref();
        let first_is_outer = verify_equality_by_they_are_the_same(first_arg, &outer_obj);
        let second_is_inner = verify_equality_by_they_are_the_same(second_arg, &inner_obj);
        let first_is_inner = verify_equality_by_they_are_the_same(first_arg, &inner_obj);
        let second_is_outer = verify_equality_by_they_are_the_same(second_arg, &outer_obj);
        let product_set: Obj = if first_is_outer && second_is_inner {
            Cart::new(vec![
                outer_sum.set.as_ref().clone(),
                inner_sum.set.as_ref().clone(),
            ])
            .into()
        } else if first_is_inner && second_is_outer {
            Cart::new(vec![
                inner_sum.set.as_ref().clone(),
                outer_sum.set.as_ref().clone(),
            ])
            .into()
        } else {
            return Ok(None);
        };
        let function: Obj = call.head.as_ref().clone().into();
        Ok(Some(NestedFiniteSetSumCartesianShape {
            product_set,
            function,
        }))
    }

    pub(crate) fn instantiate_unary_function_at(
        &mut self,
        func: &Obj,
        x: &Obj,
    ) -> Result<Option<Obj>, RuntimeError> {
        if let Some(instantiated) = self.instantiate_unary_anonymous_summand_at(func, x)? {
            return Ok(Some(instantiated));
        }
        if let Obj::FnObj(fo) = func {
            if !fo.body.is_empty() {
                return Ok(None);
            }
            return Ok(Some(
                FnObj::new((*fo.head).clone(), vec![vec![Box::new(x.clone())]]).into(),
            ));
        }
        let Some(head) = FnObjHead::from_callable_obj(func.clone()) else {
            return Ok(None);
        };
        Ok(Some(
            FnObj::new(head, vec![vec![Box::new(x.clone())]]).into(),
        ))
    }

    pub(crate) fn unary_anonymous_function_param_set(func: &Obj) -> Option<Obj> {
        let af: &AnonymousFn = match func {
            Obj::AnonymousFn(af) => af,
            Obj::FnObj(fo) => {
                if !fo.body.is_empty() {
                    return None;
                }
                match fo.head.as_ref() {
                    FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                    _ => return None,
                }
            }
            _ => return None,
        };
        if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
            return None;
        }
        let param_names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
        let param_name = param_names.first()?;
        Self::set_for_unary_param(&af.body.params_def_with_set, param_name.as_str())
    }

    pub(super) fn verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
        &mut self,
        param_name: String,
        set: Obj,
        then_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![param_name],
                ParamType::Obj(set),
            )]);
            rt.define_params_with_type(&params_def, false, ParamObjType::Forall)?;
            rt.verify_atomic_fact_by_known_atomic_or_builtin_only(then_fact, verify_state)
        })
    }

    pub(super) fn finite_set_enumeration_summand_shape(
        &mut self,
        sum: &Sum,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<FiniteSetEnumerationSummand>, RuntimeError> {
        let af = match sum.func.as_ref() {
            Obj::AnonymousFn(af) => af,
            Obj::FnObj(fo) if fo.body.is_empty() => match fo.head.as_ref() {
                FnObjHead::AnonymousFnLiteral(a) => a.as_ref(),
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        if ParamGroupWithSet::number_of_params(&af.body.params_def_with_set) != 1 {
            return Ok(None);
        }
        let param_names = ParamGroupWithSet::collect_param_names(&af.body.params_def_with_set);
        let Some(param_name) = param_names.first() else {
            return Ok(None);
        };
        let Some(index_set) =
            Self::set_for_unary_param(&af.body.params_def_with_set, param_name.as_str())
        else {
            return Ok(None);
        };
        let sum_index_set: Obj =
            ClosedRange::new(sum.start.as_ref().clone(), sum.end.as_ref().clone()).into();
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &index_set,
                &sum_index_set,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }

        let Obj::FnObj(outer_call) = af.equal_to.as_ref() else {
            return Ok(None);
        };
        if outer_call.body.len() != 1 || outer_call.body[0].len() != 1 {
            return Ok(None);
        }
        let Obj::FnObj(enumerator_call) = outer_call.body[0][0].as_ref() else {
            return Ok(None);
        };
        if enumerator_call.body.len() != 1 || enumerator_call.body[0].len() != 1 {
            return Ok(None);
        }
        let index_obj = obj_for_bound_param_in_scope(param_name.clone(), ParamObjType::FnSet);
        if !verify_equality_by_they_are_the_same(enumerator_call.body[0][0].as_ref(), &index_obj) {
            return Ok(None);
        }

        let outer_function: Obj = outer_call.head.as_ref().clone().into();
        let enumerator: Obj = enumerator_call.head.as_ref().clone().into();
        let Some(outer_body) = self.get_fn_range_function_body(&outer_function) else {
            return Ok(None);
        };
        if ParamGroupWithSet::number_of_params(&outer_body.params_def_with_set) != 1 {
            return Ok(None);
        }
        let outer_param_names =
            ParamGroupWithSet::collect_param_names(&outer_body.params_def_with_set);
        let Some(outer_param_name) = outer_param_names.first() else {
            return Ok(None);
        };
        let Some(target_set) =
            Self::set_for_unary_param(&outer_body.params_def_with_set, outer_param_name.as_str())
        else {
            return Ok(None);
        };

        let Some(enumerator_body) = self.get_fn_range_function_body(&enumerator) else {
            return Ok(None);
        };
        if ParamGroupWithSet::number_of_params(&enumerator_body.params_def_with_set) != 1 {
            return Ok(None);
        }
        let enumerator_param_names =
            ParamGroupWithSet::collect_param_names(&enumerator_body.params_def_with_set);
        let Some(enumerator_param_name) = enumerator_param_names.first() else {
            return Ok(None);
        };
        let Some(enumerator_index_set) = Self::set_for_unary_param(
            &enumerator_body.params_def_with_set,
            enumerator_param_name.as_str(),
        ) else {
            return Ok(None);
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &enumerator_index_set,
                &index_set,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                enumerator_body.ret_set.as_ref(),
                &target_set,
                line_file,
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }

        Ok(Some(FiniteSetEnumerationSummand {
            outer_function,
            enumerator_head: enumerator_call.head.as_ref().clone(),
            index_set,
            target_set,
        }))
    }

    pub(super) fn verify_unique_preimage_enumerator_fact(
        &mut self,
        shape: &FiniteSetEnumerationSummand,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let x_name = self.generate_random_unused_name();
        let i_name = format!("{}_idx", x_name);
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
        let i_obj = obj_for_bound_param_in_scope(i_name.clone(), ParamObjType::Exist);
        let enumerator_at_i: Obj =
            FnObj::new(shape.enumerator_head.clone(), vec![vec![Box::new(i_obj)]]).into();
        let body_fact: AtomicFact =
            EqualFact::new(enumerator_at_i, x_obj, line_file.clone()).into();
        let exist_body = ExistFactBody::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![i_name],
                ParamType::Obj(shape.index_set.clone()),
            )]),
            vec![ExistBodyFact::AtomicFact(body_fact)],
            line_file.clone(),
        )?;
        let forall_fact = ForallFact::new(
            ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                vec![x_name],
                ParamType::Obj(shape.target_set.clone()),
            )]),
            vec![],
            vec![ExistFactEnum::ExistUniqueFact(exist_body).into()],
            line_file,
        )?;
        let fact: Fact = forall_fact.into();
        let result = self.verify_fact_full(&fact, verify_state)?;
        Ok(result.is_true())
    }

    pub(super) fn set_for_unary_param(
        params_def: &ParamDefWithSet,
        param_name: &str,
    ) -> Option<Obj> {
        for group in params_def.iter() {
            if group.params.iter().any(|p| p == param_name) {
                return Some(group.set_obj().clone());
            }
        }
        None
    }
}

pub(super) struct FiniteSetEnumerationSummand {
    pub(super) outer_function: Obj,
    pub(super) enumerator_head: FnObjHead,
    pub(super) index_set: Obj,
    pub(super) target_set: Obj,
}

pub(super) struct NestedFiniteSetSumCartesianShape {
    pub(super) product_set: Obj,
    pub(super) function: Obj,
}
