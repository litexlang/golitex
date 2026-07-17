use super::*;

impl Runtime {
    // A finite-set sum over the empty set is zero.
    // Example: `finite_set_sum({}, fn(x Z) Z {x}) = 0`.
    pub(crate) fn try_verify_finite_set_sum_empty(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let empty_set: Obj = ListSet::new(vec![]).into();
        let zero: Obj = Number::new("0".to_string()).into();
        for (sum_side, other) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(s) = sum_side else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    s.set.as_ref(),
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
                    &zero,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set sum over empty set is zero",
                )));
            }
        }
        Ok(None)
    }

    // A finite-set sum over a displayed finite set, or a name equal to one,
    // expands to the left-associated sum of the summand at each listed element.
    // Example: `P = {1, 2}` gives `finite_set_sum(P, fn(x P) Z {x}) = 1 + 2`.
    pub(crate) fn try_verify_finite_set_sum_list_expansion(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (sum_side, other) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(s) = sum_side else {
                continue;
            };
            let mut list_sets = Vec::new();
            match s.set.as_ref() {
                Obj::ListSet(list_set) => list_sets.push(list_set.clone()),
                set => {
                    for representative in self.get_all_obj_representatives_equal_to_given(set) {
                        if let Obj::ListSet(list_set) = representative {
                            list_sets.push(list_set);
                        }
                    }
                }
            }

            for list_set in list_sets {
                let mut terms = Vec::with_capacity(list_set.list.len());
                for element in list_set.list.iter() {
                    let Some(term) =
                        self.instantiate_unary_function_at(s.func.as_ref(), element.as_ref())?
                    else {
                        terms.clear();
                        break;
                    };
                    terms.push(term);
                }
                if terms.len() != list_set.list.len() {
                    continue;
                }
                let expected = Self::left_assoc_add_from_terms(terms);
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
                        "equality: finite-set sum over displayed set expands elementwise",
                    )));
                }
            }
        }
        Ok(None)
    }

    // A finite-set sum over an integer closed range agrees with the existing range sum.
    // Example: `finite_set_sum(1...3, fn(x Z) Z {x}) = sum(1, 3, fn(x Z) Z {x})`.
    pub(crate) fn try_verify_finite_set_sum_closed_range_bridge(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        for (finite_side, range_side) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(finite_sum) = finite_side else {
                continue;
            };
            let Obj::ClosedRange(range) = finite_sum.set.as_ref() else {
                continue;
            };
            let Obj::Sum(range_sum) = range_side else {
                continue;
            };
            if !self
                .verify_objs_are_equal_in_equality_builtin(
                    range.start.as_ref(),
                    range_sum.start.as_ref(),
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
                    range_sum.end.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
            {
                continue;
            }
            let exact_func_result = self.verify_objs_are_equal_in_equality_builtin(
                finite_sum.func.as_ref(),
                range_sum.func.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !exact_func_result.is_true() {
                let x_name = self.generate_random_unused_name();
                let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
                let Some(finite_inst) =
                    self.instantiate_unary_function_at(finite_sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let Some(range_inst) =
                    self.instantiate_unary_function_at(range_sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let pointwise_fact: AtomicFact =
                    EqualFact::new(finite_inst, range_inst, line_file.clone()).into();
                let dom_lo: Fact = LessEqualFact::new(
                    (*range_sum.start).clone(),
                    x_obj.clone(),
                    line_file.clone(),
                )
                .into();
                let dom_hi: Fact =
                    LessEqualFact::new(x_obj, (*range_sum.end).clone(), line_file.clone()).into();
                let pointwise_result = self
                    .verify_integer_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                        x_name,
                        vec![dom_lo, dom_hi],
                        &pointwise_fact,
                        verify_state,
                    )?;
                if !pointwise_result.is_true() {
                    continue;
                }
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set sum over closed integer range equals range sum",
            )));
        }
        Ok(None)
    }

    // A constant finite-set summand is the set cardinality times the constant.
    // Example: `finite_set_sum(X, fn(x X) R {c}) = finite_set_size(X) * c`.
    pub(crate) fn try_verify_finite_set_sum_constant_summand(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (sum_side, other) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(s) = sum_side else {
                continue;
            };
            let af = match s.func.as_ref() {
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
            let finite_set_size: Obj = FiniteSetSize::new((*s.set).clone()).into();
            let m1: Obj = Mul::new(finite_set_size.clone(), c.clone()).into();
            let m2: Obj = Mul::new(c, finite_set_size).into();
            if self
                .verify_objs_are_equal_in_equality_builtin(
                    other,
                    &m1,
                    line_file.clone(),
                    verify_state,
                )?
                .is_true()
                || self
                    .verify_objs_are_equal_in_equality_builtin(
                        other,
                        &m2,
                        line_file.clone(),
                        verify_state,
                    )?
                    .is_true()
            {
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set sum of a constant summand",
                )));
            }
        }
        Ok(None)
    }

    // Finite-set sums are equal when their summands are pointwise equal on the same finite set.
    // Example: from `forall x X: f(x) = g(x)`, prove
    // `finite_set_sum(X, f) = finite_set_sum(X, g)`.
    pub(crate) fn try_verify_finite_set_sum_pointwise_equality(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let (left_sum, right_sum) = match (left, right) {
            (Obj::SumOfFiniteSet(l), Obj::SumOfFiniteSet(r)) => (l, r),
            _ => return Ok(None),
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                left_sum.set.as_ref(),
                right_sum.set.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        let x_name = self.generate_random_unused_name();
        let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
        let Some(left_inst) = self.instantiate_unary_function_at(left_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let Some(right_inst) =
            self.instantiate_unary_function_at(right_sum.func.as_ref(), &x_obj)?
        else {
            return Ok(None);
        };
        let then_fact: AtomicFact = EqualFact::new(left_inst, right_inst, line_file.clone()).into();
        let r = self.verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
            x_name,
            left_sum.set.as_ref().clone(),
            &then_fact,
            verify_state,
        )?;
        if r.is_true() {
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set sums from pointwise equality on the finite set",
            )));
        }
        Ok(None)
    }

    // Finite-set sum substitution along a bijection onto the original set.
    // Example: from `forall x X: exist! y Y st {g(y) = x}`, prove
    // `finite_set_sum(X, f) = finite_set_sum(Y, fn(y Y) R {f(g(y))})`.
    pub(crate) fn try_verify_finite_set_sum_substitution(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (source_side, pullback_side) in [(left, right), (right, left)] {
            let (Obj::SumOfFiniteSet(source_sum), Obj::SumOfFiniteSet(pullback_sum)) =
                (source_side, pullback_side)
            else {
                continue;
            };

            let y_name = self.generate_random_unused_name();
            let y_obj = obj_for_bound_param_in_scope(y_name.clone(), ParamObjType::Forall);
            let Some(pullback_at_y) =
                self.instantiate_unary_function_at(pullback_sum.func.as_ref(), &y_obj)?
            else {
                continue;
            };
            let Some(map_y) = Self::unary_application_arg_matching_callable(
                &pullback_at_y,
                source_sum.func.as_ref(),
            ) else {
                continue;
            };
            let Some(source_at_map_y) =
                self.instantiate_unary_function_at(source_sum.func.as_ref(), &map_y)?
            else {
                continue;
            };
            let pointwise_fact: AtomicFact =
                EqualFact::new(pullback_at_y, source_at_map_y, line_file.clone()).into();
            let pointwise_result = self
                .verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                    y_name,
                    pullback_sum.set.as_ref().clone(),
                    &pointwise_fact,
                    verify_state,
                )?;
            if !pointwise_result.is_true() {
                continue;
            }

            let base_name = self.generate_random_unused_name();
            let x_name = format!("{}a", base_name);
            let exist_y_name = format!("{}b", base_name);
            let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
            let exist_y_obj =
                obj_for_bound_param_in_scope(exist_y_name.clone(), ParamObjType::Exist);
            let Some(pullback_at_exist_y) =
                self.instantiate_unary_function_at(pullback_sum.func.as_ref(), &exist_y_obj)?
            else {
                continue;
            };
            let Some(map_exist_y) = Self::unary_application_arg_matching_callable(
                &pullback_at_exist_y,
                source_sum.func.as_ref(),
            ) else {
                continue;
            };
            let preimage_eq: AtomicFact =
                EqualFact::new(map_exist_y, x_obj, line_file.clone()).into();
            let exist_body = ExistFactBody::new(
                ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec![exist_y_name],
                    ParamType::Obj(pullback_sum.set.as_ref().clone()),
                )]),
                vec![ExistBodyFact::AtomicFact(preimage_eq)],
                line_file.clone(),
            )?;
            let unique_preimage_fact: Fact = ExistFactEnum::ExistUniqueFact(exist_body).into();
            let unique_preimage_result = self.run_in_local_env(|rt| {
                let params_def = ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                    vec![x_name],
                    ParamType::Obj(source_sum.set.as_ref().clone()),
                )]);
                rt.define_params_with_type(&params_def, false, ParamObjType::Forall)?;
                rt.verify_fact_full(&unique_preimage_fact, verify_state)
            })?;
            if !unique_preimage_result.is_true() {
                continue;
            }

            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set sum substitution along a uniquely-covered index set",
            )));
        }
        Ok(None)
    }

    // Finite-set sums split over disjoint unions.
    // Example: from `intersect(X, Y) = {}`, prove
    // `finite_set_sum(union(X, Y), f) = finite_set_sum(X, f|X) + finite_set_sum(Y, f|Y)`.
    pub(crate) fn try_verify_finite_set_sum_disjoint_union(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (union_side, add_side) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(union_sum) = union_side else {
                continue;
            };
            let Obj::Add(add) = add_side else {
                continue;
            };
            for (first_side, second_side) in [
                (add.left.as_ref(), add.right.as_ref()),
                (add.right.as_ref(), add.left.as_ref()),
            ] {
                let (Obj::SumOfFiniteSet(first_sum), Obj::SumOfFiniteSet(second_sum)) =
                    (first_side, second_side)
                else {
                    continue;
                };
                let expected_union: Obj = Union::new(
                    first_sum.set.as_ref().clone(),
                    second_sum.set.as_ref().clone(),
                )
                .into();
                let union_result = self.verify_objs_are_equal_in_equality_builtin(
                    union_sum.set.as_ref(),
                    &expected_union,
                    line_file.clone(),
                    verify_state,
                )?;
                if !union_result.is_true() {
                    continue;
                }
                let empty_set: Obj = ListSet::new(vec![]).into();
                let intersection: Obj = Intersect::new(
                    first_sum.set.as_ref().clone(),
                    second_sum.set.as_ref().clone(),
                )
                .into();
                let disjoint_result = self.verify_objs_are_equal_in_equality_builtin(
                    &intersection,
                    &empty_set,
                    line_file.clone(),
                    verify_state,
                )?;
                if !disjoint_result.is_true() {
                    continue;
                }
                let first_pointwise = self.verify_finite_set_sum_functions_pointwise_equal(
                    union_sum.func.as_ref(),
                    first_sum.func.as_ref(),
                    first_sum.set.as_ref().clone(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !first_pointwise.is_true() {
                    continue;
                }
                let second_pointwise = self.verify_finite_set_sum_functions_pointwise_equal(
                    union_sum.func.as_ref(),
                    second_sum.func.as_ref(),
                    second_sum.set.as_ref().clone(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !second_pointwise.is_true() {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set sum over a disjoint union",
                )));
            }
        }
        Ok(None)
    }

    // Finite-set sums distribute over pointwise addition on the same finite set.
    // Example: `finite_set_sum(X, fn(x X) R {f(x) + g(x)}) =
    // finite_set_sum(X, f) + finite_set_sum(X, g)`.
    pub(crate) fn try_verify_finite_set_sum_add(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (sum_side, add_side) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(sum) = sum_side else {
                continue;
            };
            let Obj::Add(add) = add_side else {
                continue;
            };
            let (Obj::SumOfFiniteSet(first_sum), Obj::SumOfFiniteSet(second_sum)) =
                (add.left.as_ref(), add.right.as_ref())
            else {
                continue;
            };
            let first_set_result = self.verify_objs_are_equal_in_equality_builtin(
                sum.set.as_ref(),
                first_sum.set.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !first_set_result.is_true() {
                continue;
            }
            let second_set_result = self.verify_objs_are_equal_in_equality_builtin(
                sum.set.as_ref(),
                second_sum.set.as_ref(),
                line_file.clone(),
                verify_state,
            )?;
            if !second_set_result.is_true() {
                continue;
            }

            let x_name = self.generate_random_unused_name();
            let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
            let Some(sum_inst) = self.instantiate_unary_function_at(sum.func.as_ref(), &x_obj)?
            else {
                continue;
            };
            let Some(first_inst) =
                self.instantiate_unary_function_at(first_sum.func.as_ref(), &x_obj)?
            else {
                continue;
            };
            let Some(second_inst) =
                self.instantiate_unary_function_at(second_sum.func.as_ref(), &x_obj)?
            else {
                continue;
            };
            let expected: Obj = Add::new(first_inst, second_inst).into();
            let pointwise_fact: AtomicFact =
                EqualFact::new(sum_inst, expected, line_file.clone()).into();
            let pointwise_result = self
                .verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                    x_name,
                    sum.set.as_ref().clone(),
                    &pointwise_fact,
                    verify_state,
                )?;
            if !pointwise_result.is_true() {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: finite-set sum distributes over pointwise addition",
            )));
        }
        Ok(None)
    }

    // Scalars factor out of finite-set sums on the same finite set.
    // Example: `finite_set_sum(X, fn(x X) R {c * f(x)}) = c * finite_set_sum(X, f)`.
    pub(crate) fn try_verify_finite_set_sum_scalar_mul(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (sum_side, product_side) in [(left, right), (right, left)] {
            let Obj::SumOfFiniteSet(sum) = sum_side else {
                continue;
            };
            let Obj::Mul(product) = product_side else {
                continue;
            };
            for (base_side, scalar) in [
                (product.left.as_ref(), product.right.as_ref()),
                (product.right.as_ref(), product.left.as_ref()),
            ] {
                let Obj::SumOfFiniteSet(base_sum) = base_side else {
                    continue;
                };
                let set_result = self.verify_objs_are_equal_in_equality_builtin(
                    sum.set.as_ref(),
                    base_sum.set.as_ref(),
                    line_file.clone(),
                    verify_state,
                )?;
                if !set_result.is_true() {
                    continue;
                }

                let x_name = self.generate_random_unused_name();
                let x_obj = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Forall);
                let Some(sum_inst) =
                    self.instantiate_unary_function_at(sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let Some(base_inst) =
                    self.instantiate_unary_function_at(base_sum.func.as_ref(), &x_obj)?
                else {
                    continue;
                };
                let expected: Obj = Mul::new(scalar.clone(), base_inst).into();
                let pointwise_fact: AtomicFact =
                    EqualFact::new(sum_inst, expected, line_file.clone()).into();
                let pointwise_result = self
                    .verify_set_pointwise_atomic_fact_by_known_atomic_or_builtin_only(
                        x_name,
                        sum.set.as_ref().clone(),
                        &pointwise_fact,
                        verify_state,
                    )?;
                if !pointwise_result.is_true() {
                    continue;
                }
                return Ok(Some(factual_equal_success_by_builtin_reason(
                    left,
                    right,
                    line_file,
                    "equality: finite-set sum scalar multiplication",
                )));
            }
        }
        Ok(None)
    }

    // A nested finite-set sum over two finite sets is the finite-set sum over
    // their Cartesian product.
    // Example: `finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})})
    // = finite_set_sum(cart(X, Y), f)`.
    pub(crate) fn try_verify_finite_set_sum_over_cartesian_product(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        for (nested_side, flat_side) in [(left, right), (right, left)] {
            let Some(nested_shape) = self.nested_finite_set_sum_cartesian_shape(
                nested_side,
                line_file.clone(),
                verify_state,
            )?
            else {
                continue;
            };
            let Obj::SumOfFiniteSet(flat_sum) = flat_side else {
                continue;
            };
            let set_result = self.verify_objs_are_equal_in_equality_builtin(
                flat_sum.set.as_ref(),
                &nested_shape.product_set,
                line_file.clone(),
                verify_state,
            )?;
            if !set_result.is_true() {
                continue;
            }
            let func_result = self.verify_objs_are_equal_in_equality_builtin(
                flat_sum.func.as_ref(),
                &nested_shape.function,
                line_file.clone(),
                verify_state,
            )?;
            if !func_result.is_true() {
                continue;
            }
            return Ok(Some(factual_equal_success_by_builtin_reason(
                left,
                right,
                line_file,
                "equality: double finite-set sum over Cartesian product",
            )));
        }
        Ok(None)
    }

    // Fubini for finite-set sums: two nested sums with the same flattened
    // Cartesian-product summand can swap their summation order.
    // Example: `sum_X sum_Y f((x, y)) = sum_Y sum_X f((x, y))`.
    pub(crate) fn try_verify_finite_set_sum_fubini(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let Some(left_shape) =
            self.nested_finite_set_sum_cartesian_shape(left, line_file.clone(), verify_state)?
        else {
            return Ok(None);
        };
        let Some(right_shape) =
            self.nested_finite_set_sum_cartesian_shape(right, line_file.clone(), verify_state)?
        else {
            return Ok(None);
        };
        let set_result = self.verify_objs_are_equal_in_equality_builtin(
            &left_shape.product_set,
            &right_shape.product_set,
            line_file.clone(),
            verify_state,
        )?;
        if !set_result.is_true() {
            return Ok(None);
        }
        let func_result = self.verify_objs_are_equal_in_equality_builtin(
            &left_shape.function,
            &right_shape.function,
            line_file.clone(),
            verify_state,
        )?;
        if !func_result.is_true() {
            return Ok(None);
        }
        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: finite-set Fubini over Cartesian product",
        )))
    }

    // Range sums over two bijective enumerations of the same finite set are equal.
    // Example: from `forall x X: exist! i 1...finite_set_size(X) st {g(i) = x}` and the
    // analogous fact for `h`, prove `sum(1, finite_set_size(X), fn(i 1...finite_set_size(X)) R {f(g(i))})
    // = sum(1, finite_set_size(X), fn(i 1...finite_set_size(X)) R {f(h(i))})`.
    pub(crate) fn try_verify_sum_over_bijective_finite_set_enumerations(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if !verify_state.is_round_0() {
            return Ok(None);
        }
        let (left_sum, right_sum) = match (left, right) {
            (Obj::Sum(l), Obj::Sum(r)) => (l, r),
            _ => return Ok(None),
        };
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                left_sum.start.as_ref(),
                right_sum.start.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                left_sum.end.as_ref(),
                right_sum.end.as_ref(),
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }

        let Some(left_shape) =
            self.finite_set_enumeration_summand_shape(left_sum, line_file.clone(), verify_state)?
        else {
            return Ok(None);
        };
        let Some(right_shape) =
            self.finite_set_enumeration_summand_shape(right_sum, line_file.clone(), verify_state)?
        else {
            return Ok(None);
        };

        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &left_shape.outer_function,
                &right_shape.outer_function,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &left_shape.index_set,
                &right_shape.index_set,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_objs_are_equal_in_equality_builtin(
                &left_shape.target_set,
                &right_shape.target_set,
                line_file.clone(),
                verify_state,
            )?
            .is_true()
        {
            return Ok(None);
        }

        let finite_target: AtomicFact =
            IsFiniteSetFact::new(left_shape.target_set.clone(), line_file.clone()).into();
        if !self
            .verify_non_equational_known_then_builtin_rules_only(&finite_target, verify_state)?
            .is_true()
        {
            return Ok(None);
        }
        if !self.verify_unique_preimage_enumerator_fact(
            &left_shape,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(None);
        }
        if !self.verify_unique_preimage_enumerator_fact(
            &right_shape,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(None);
        }

        Ok(Some(factual_equal_success_by_builtin_reason(
            left,
            right,
            line_file,
            "equality: sums over bijective enumerations of the same finite set",
        )))
    }
}
