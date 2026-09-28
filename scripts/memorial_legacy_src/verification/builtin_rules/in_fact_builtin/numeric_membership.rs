use super::*;

impl Runtime {
    /// A generic reduce inhabits the homogeneous carrier defined by its
    /// binary operation. This rule is intentionally carrier-generic rather
    /// than restricted to the standard number hierarchy.
    pub(super) fn verify_reduce_membership_from_operation_carrier(
        &self,
        in_fact: &InFact,
    ) -> Option<ProveFactResult> {
        let (operation, name) = match &in_fact.element {
            Obj::Reduce(reduce) => (reduce.op.as_ref(), "reduce"),
            Obj::FiniteSetReduce(reduce) => (reduce.op.as_ref(), "finite_set_reduce"),
            _ => return None,
        };
        let carrier = self.reduce_carrier_from_operation(operation)?;
        let carrier_is_contained = objs_match_for_pattern(&carrier, &in_fact.set)
            || matches!(
                (&carrier, &in_fact.set),
                (Obj::StandardSet(source), Obj::StandardSet(target))
                    if source.is_subset_eq(target)
            );
        if !carrier_is_contained {
            return None;
        }
        Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                format!(
                    "{name}: operation carrier {carrier} is contained in {}",
                    in_fact.set
                ),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyReduceMembershipFromOperationCarrier,
                ),
                Vec::new(),
            )
            .into(),
        )
    }

    pub(super) fn verify_refined_integer_carrier_from_known_sign(
        &mut self,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Obj::StandardSet(target) = &in_fact.set else {
            return Ok(None);
        };
        let zero: Obj = Number::new("0".to_string()).into();
        let sign_fact: AtomicFact = match target {
            StandardSet::NPos => self
                .new_greater_fact(in_fact.element.clone(), zero, in_fact.line_file.clone())
                .into(),
            StandardSet::ZNeg => self
                .new_less_fact(in_fact.element.clone(), zero, in_fact.line_file.clone())
                .into(),
            _ => return Ok(None),
        };
        let Some(sign_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&sign_fact, builtin_state)?
        else {
            return Ok(None);
        };

        for source_set in self.known_sets_containing_obj(&in_fact.element) {
            let Obj::StandardSet(source_carrier) = &source_set else {
                continue;
            };
            if !source_carrier.is_subset_eq(&StandardSet::Z) {
                continue;
            }
            let source_membership: AtomicFact = self
                .new_in_fact(
                    in_fact.element.clone(),
                    source_set,
                    in_fact.line_file.clone(),
                )
                .into();
            let Some(source_result) = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &source_membership,
                builtin_state,
            )?
            else {
                continue;
            };
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "refined integer carrier from known integer membership and strict sign"
                        .to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyRefinedIntegerCarrierFromKnownSign,
                    ),
                    vec![source_result, sign_result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    // A nonempty integer-range sum/product inherits the narrowest standard scalar carrier
    // defined by its iterand. The anonymous-function checker separately verifies the body
    // against that definition.
    // Example: `sum(1, 2, fn(k Z) C {i}) $in C`, but not in R.
    pub(super) fn verify_in_fact_sum_or_product_by_iterand_ret_set(
        &mut self,
        in_fact: &InFact,
        func: &Obj,
        target_set: StandardSet,
        _builtin_state: &BuiltinRuleSearchState,
        op: &str,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Some(Obj::StandardSet(ret_set)) = self.iterated_op_func_ret_set(func) else {
            return Ok(UnknownGenericStmtResult::new().into());
        };
        if !ret_set.is_subset_eq(&target_set) {
            return Ok(UnknownGenericStmtResult::new().into());
        }
        let reason = format!("{op}: iterand return set {ret_set} is contained in {target_set}");
        if op == "sum" && matches!(ret_set, StandardSet::Z) && matches!(target_set, StandardSet::Z)
        {
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    reason,
                    BuiltinRuleEvidence::IntegerRangeSumMembership,
                    Vec::new(),
                )
                .into(),
            );
        }
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact, &reason,
        ))
    }

    pub fn iterated_op_func_ret_set(&self, func: &Obj) -> Option<Obj> {
        match func {
            Obj::AnonymousFn(anon) => Some((*anon.body.ret_set).clone()),
            Obj::FnObj(fn_obj) if fn_obj.body.is_empty() => match fn_obj.head.as_ref() {
                FnObjHead::AnonymousFnLiteral(anon) => Some((*anon.body.ret_set).clone()),
                _ => {
                    let function_name_obj: Obj = (*fn_obj.head).clone().into();
                    self.get_object_in_fn_set(&function_name_obj)
                        .map(|fn_set_body| (*fn_set_body.ret_set).clone())
                }
            },
            _ => self
                .get_object_in_fn_set(func)
                .map(|fn_set_body| (*fn_set_body.ret_set).clone()),
        }
    }

    // Finite-set sum: the return set of the summand controls the numeric set of the sum.
    // Example: `finite_set_sum({1, 2}, fn(x Z) Z {x}) $in Z`; for `N+`, the domain must be nonempty.
    pub(super) fn verify_in_fact_finite_set_sum_by_iterand_ret_set(
        &mut self,
        in_fact: &InFact,
        sum: &SumOfFiniteSet,
        target_set: StandardSet,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Some(ret_set) = self.iterated_op_func_ret_set(sum.func.as_ref()) else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Obj::StandardSet(ret_standard_set) = ret_set else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        if matches!(&target_set, StandardSet::NPos) {
            if !matches!(&ret_standard_set, StandardSet::NPos) {
                return Ok((UnknownGenericStmtResult::new()).into());
            }
            let nonempty_fact: AtomicFact = self
                .new_is_nonempty_set_fact((*sum.set).clone(), in_fact.line_file.clone())
                .into();
            let nonempty_result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&nonempty_fact, builtin_state)?;
            let structurally_nonempty = match sum.set.as_ref() {
                Obj::StandardSet(_) | Obj::PowerSet(_) => true,
                Obj::ListSet(list) => !list.list.is_empty(),
                _ => false,
            };
            let subgoals = match nonempty_result {
                Some(nonempty_result) => vec![nonempty_result],
                None if structurally_nonempty => Vec::new(),
                None => return Ok((UnknownGenericStmtResult::new()).into()),
            };
            return Ok(
                number_in_set_verified_by_builtin_rules_result_with_subgoals(
                    in_fact,
                    "finite_set_sum: positive summand over a nonempty finite set",
                    subgoals,
                ),
            );
        }
        if !ret_standard_set.is_subset_eq(&target_set) {
            return Ok((UnknownGenericStmtResult::new()).into());
        }
        let reason = format!(
            "finite_set_sum: summand return set {} is contained in {}",
            ret_standard_set, target_set
        );
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            reason.as_str(),
        ))
    }

    // Finite-set product: the return set of the factor controls the numeric set of the product.
    // Example: `finite_set_product({1, 2}, fn(x Z) Z {x}) $in Z`; for `N+`, the empty product is `1`.
    pub(super) fn verify_in_fact_finite_set_product_by_iterand_ret_set(
        &mut self,
        in_fact: &InFact,
        product: &ProductOfFiniteSet,
        target_set: StandardSet,
        _builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Some(ret_set) = self.iterated_op_func_ret_set(product.func.as_ref()) else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Obj::StandardSet(ret_standard_set) = ret_set else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        if matches!(&target_set, StandardSet::NPos) {
            if !matches!(&ret_standard_set, StandardSet::NPos) {
                return Ok((UnknownGenericStmtResult::new()).into());
            }
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "finite_set_product: positive factors give a positive finite product",
            ));
        }
        if !ret_standard_set.is_subset_eq(&target_set) {
            return Ok((UnknownGenericStmtResult::new()).into());
        }
        let reason = format!(
            "finite_set_product: factor return set {} is contained in {}",
            ret_standard_set, target_set
        );
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            reason.as_str(),
        ))
    }

    // `sum(start, end, f)` / `product(start, end, f)` in `N+` when the iterand's defined
    // return set is `N+` and the whole iterated object is well-defined on the integer interval.
    // Example: `product(1, a, fn(x N+) N+ {x}) $in N+`.
    pub(super) fn verify_in_fact_sum_or_product_in_n_pos_by_iterand_ret_set(
        &mut self,
        in_fact: &InFact,
        func: &Obj,
        _builtin_state: &BuiltinRuleSearchState,
        op: &str,
    ) -> Result<ProveFactResult, RuntimeError> {
        let Some(ret_set) = self.iterated_op_func_ret_set(func) else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let n_pos_obj: Obj = StandardSet::NPos.into();
        if !objs_match_for_pattern(&ret_set, &n_pos_obj) {
            return Ok((UnknownGenericStmtResult::new()).into());
        }
        let reason = format!("{op}: iterand return set is N+");
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            reason.as_str(),
        ))
    }

    /// `f(args) $in S` when the head's defined return set is `S`, or a standard numeric
    /// subset of `S`, and the application is well-defined in the current environment.
    /// This also covers function-valued returns, e.g. `seq_add_R(a, b) $in fn(k N+) R`.
    /// Example: if `floor fn(x R) Z`, then `floor(x) $in R` because `Z subset R`.
    pub(super) fn verify_in_fact_fn_application_in_typed_return_set(
        &mut self,
        fn_obj: &FnObj,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let (head_obj, initial_function_set) = match fn_obj.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(function) => (
                Obj::AnonymousFn((**function).clone()),
                FnSet::from_body(function.body.clone())?,
            ),
            _ => {
                let head_obj: Obj = (*fn_obj.head.clone()).into();
                let Some(body) = self.get_cloned_object_in_fn_set(&head_obj) else {
                    return Ok((UnknownGenericStmtResult::new()).into());
                };
                (head_obj, FnSet::from_body(body)?)
            }
        };
        let Some(typed_ret) = self.fn_obj_return_set_after_application(fn_obj)? else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let target = &in_fact.set;
        let ret_matches = self
            .verify_equal_fact_by_known_equality(&self.new_equal_fact_from_refs(
                target,
                &typed_ret,
                in_fact.line_file.clone(),
            ))
            .is_success();
        let ret_matches_alpha_renamed_fn_set =
            if let (Obj::FnSet(typed_fn_set), Obj::FnSet(target_fn_set)) = (&typed_ret, target) {
                let flat_typed = SetBoundParameterGroup::collect_param_names(
                    &typed_fn_set.body.set_bound_parameters,
                );
                let flat_target = SetBoundParameterGroup::collect_param_names(
                    &target_fn_set.body.set_bound_parameters,
                );
                if flat_typed.len() == flat_target.len() {
                    let shared_names = self.generate_random_unused_names(flat_typed.len());
                    let typed_norm = self.fn_set_alpha_renamed_for_display_compare(
                        &typed_fn_set.body,
                        &shared_names,
                    )?;
                    let target_norm = self.fn_set_alpha_renamed_for_display_compare(
                        &target_fn_set.body,
                        &shared_names,
                    )?;
                    typed_norm.to_string() == target_norm.to_string()
                } else {
                    false
                }
            } else {
                false
            };
        let ret_is_standard_subset = match (&typed_ret, target) {
            (Obj::StandardSet(ret_set), Obj::StandardSet(target_set)) => {
                ret_set.is_subset_eq(target_set)
            }
            _ => false,
        };
        if !ret_matches && !ret_matches_alpha_renamed_fn_set && !ret_is_standard_subset {
            return Ok((UnknownGenericStmtResult::new()).into());
        }
        if objs_equal_with_nested_binder_alpha_equivalence(target, &typed_ret) {
            let head_membership: AtomicFact = self
                .new_in_fact(
                    head_obj,
                    initial_function_set.clone().into(),
                    in_fact.line_file.clone(),
                )
                .into();
            let Some(head_membership_result) = self
                .try_verify_atomic_fact_as_builtin_rule_premise(&head_membership, builtin_state)?
            else {
                return Ok((UnknownGenericStmtResult::new()).into());
            };
            let target_fact: Fact = in_fact.clone().into();
            let head_membership_fact: Fact = head_membership.into();
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    target_fact.clone(),
                    "fn application in its exact instantiated defined return set".to_string(),
                    BuiltinRuleEvidence::FunctionApplicationReturnMembership(
                        FunctionApplicationReturnMembershipBuiltinRuleEvidence::new(
                            typed_ret,
                            target_fact,
                            head_membership_fact,
                        ),
                    ),
                    vec![head_membership_result],
                )
                .into(),
            );
        }
        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "fn application in defined return set or standard numeric superset (well-defined under typing)".to_string(),
                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactFnApplicationInTypedReturnSet),
                Vec::new(),
            )
            .into(),
        )
    }

    // `a + b $in N` when `a $in N` and `b $in N` (closure under addition).
    // Example: `forall a, b N: a + b $in N`.
    pub(super) fn verify_in_fact_add_in_n_from_summands_in_n(
        &mut self,
        in_fact: &InFact,
        add: &Add,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::N,
            ));
        }
        let n: Obj = StandardSet::N.into();
        let lf = in_fact.line_file.clone();
        let f_left: AtomicFact = self
            .new_in_fact(add.left.as_ref().clone(), n.clone(), lf.clone())
            .into();
        let f_right: AtomicFact = self
            .new_in_fact(add.right.as_ref().clone(), n, lf.clone())
            .into();
        let Some(r_left) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&f_left, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Some(r_right) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&f_right, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "N: a + b from a in N and b in N".to_string(),
                BuiltinRuleEvidence::NaturalMembershipClosure(
                    NaturalMembershipClosureBuiltinRule::Add,
                ),
                vec![r_left, r_right],
            )
            .into(),
        )
    }

    // Integer subtraction stays in `N` when the result is nonnegative.
    // Example: `forall n N+: n - 1 $in N`, since `n, 1 $in Z` and `1 <= n`.
    pub(super) fn verify_in_fact_sub_in_n_from_integer_terms_and_bound(
        &mut self,
        in_fact: &InFact,
        sub: &Sub,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::N,
            ));
        }

        // A positive natural has a natural predecessor.
        // Examples: `n $in N+` => `n - 1 $in N`, or
        // `n $in N`, `n > 0` => `n - 1 $in N`.
        if matches!(sub.right.as_ref(), Obj::Number(number) if number.normalized_value == "1") {
            let lf = in_fact.line_file.clone();
            let left = sub.left.as_ref().clone();
            let left_in_n_pos: AtomicFact = self
                .new_in_fact(left.clone(), StandardSet::NPos.into(), lf.clone())
                .into();
            let positive_natural_result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&left_in_n_pos, builtin_state)?;
            if let Some(positive_natural_result) = positive_natural_result {
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        "N: n - 1 from n in N+".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactSubInNFromIntegerTermsAndBound01),
                        vec![positive_natural_result],
                    )
                    .into(),
                );
            }
            let left_in_n: AtomicFact = self
                .new_in_fact(left.clone(), StandardSet::N.into(), lf.clone())
                .into();
            let left_positive: AtomicFact = self
                .new_greater_fact(left, Number::new("0".to_string()).into(), lf)
                .into();
            let membership_result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&left_in_n, builtin_state)?;
            let positive_result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&left_positive, builtin_state)?;
            if let (Some(membership_result), Some(positive_result)) =
                (membership_result, positive_result)
            {
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        "N: n - 1 from n in N and n > 0".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactSubInNFromIntegerTermsAndBound02),
                        vec![membership_result, positive_result],
                    )
                    .into(),
                );
            }
        }

        let lf = in_fact.line_file.clone();
        let z: Obj = StandardSet::Z.into();
        let left_in_z: AtomicFact = self
            .new_in_fact(sub.left.as_ref().clone(), z.clone(), lf.clone())
            .into();
        let right_in_z: AtomicFact = self
            .new_in_fact(sub.right.as_ref().clone(), z, lf.clone())
            .into();
        let right_le_left: AtomicFact = self
            .new_less_equal_fact(
                sub.right.as_ref().clone(),
                sub.left.as_ref().clone(),
                lf.clone(),
            )
            .into();

        let left_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&left_in_z, builtin_state)?;
        let Some(left_result) = left_result else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let right_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&right_in_z, builtin_state)?;
        let Some(right_result) = right_result else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let bound_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&right_le_left, builtin_state)?;
        if let Some(bound_result) = bound_result {
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "N: a - b from a,b in Z and b <= a".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyInFactSubInNFromIntegerTermsAndBound03,
                    ),
                    vec![left_result, right_result, bound_result],
                )
                .into(),
            );
        }

        let zero: Obj = Number::new("0".to_string()).into();
        let elem = in_fact.element.clone();
        let order_facts: [AtomicFact; 4] = [
            self.new_greater_equal_fact(elem.clone(), zero.clone(), lf.clone())
                .into(),
            self.new_less_equal_fact(zero.clone(), elem.clone(), lf.clone())
                .into(),
            self.new_greater_fact(elem.clone(), zero.clone(), lf.clone())
                .into(),
            self.new_less_fact(zero, elem, lf).into(),
        ];
        for order_fact in order_facts.iter() {
            let order_result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(order_fact, builtin_state)?;
            if let Some(order_result) = order_result {
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        "N: a - b from a,b in Z and known nonnegative difference".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactSubInNFromIntegerTermsAndBound04),
                        vec![left_result, right_result, order_result],
                    )
                    .into(),
                );
            }
        }

        Ok((UnknownGenericStmtResult::new()).into())
    }

    // `a * b $in N` when `a $in N` and `b $in N` (closure under multiplication).
    // Example: `forall a, b N: a * b $in N`.
    pub(super) fn verify_in_fact_mul_in_n_from_factors_in_n(
        &mut self,
        in_fact: &InFact,
        mul: &Mul,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::N,
            ));
        }
        let n: Obj = StandardSet::N.into();
        let lf = in_fact.line_file.clone();
        let f_left: AtomicFact = self
            .new_in_fact(mul.left.as_ref().clone(), n.clone(), lf.clone())
            .into();
        let f_right: AtomicFact = self
            .new_in_fact(mul.right.as_ref().clone(), n, lf.clone())
            .into();
        let Some(r_left) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&f_left, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Some(r_right) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&f_right, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "N: a * b from a in N and b in N".to_string(),
                BuiltinRuleEvidence::NaturalMembershipClosure(
                    NaturalMembershipClosureBuiltinRule::Mul,
                ),
                vec![r_left, r_right],
            )
            .into(),
        )
    }

    // Natural-number powers preserve standard integer-like sets.
    // Example: `forall a Z, k N: a^k $in Z`.
    pub(super) fn verify_in_fact_pow_in_standard_set_from_base_and_natural_exponent(
        &mut self,
        in_fact: &InFact,
        pow: &Pow,
        builtin_state: &BuiltinRuleSearchState,
        base_set: StandardSet,
        reason: &str,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &base_set,
            ));
        }
        let lf = in_fact.line_file.clone();
        let base_in_target: AtomicFact = self
            .new_in_fact(pow.base.as_ref().clone(), base_set.into(), lf.clone())
            .into();
        let exponent_in_n: AtomicFact = self
            .new_in_fact(
                pow.exponent.as_ref().clone(),
                StandardSet::N.into(),
                lf.clone(),
            )
            .into();

        let base_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&base_in_target, builtin_state)?;
        let Some(base_result) = base_result else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let exponent_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&exponent_in_n, builtin_state)?;
        let Some(exponent_result) = exponent_result else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                reason.to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactPowInStandardSetFromBaseAndNaturalExponent,
                ),
                vec![base_result, exponent_result],
            )
            .into(),
        )
    }

    // Positive real bases raised to real exponents are positive reals.
    // Example: `forall a R+, x R: a^x $in R+`.
    pub(super) fn verify_in_fact_pow_in_r_pos_from_positive_base_real_exponent(
        &mut self,
        in_fact: &InFact,
        pow: &Pow,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let lf = in_fact.line_file.clone();
        let zero: Obj = Number::new("0".to_string()).into();
        let base_positive: AtomicFact = self
            .new_less_fact(zero, pow.base.as_ref().clone(), lf.clone())
            .into();
        let exponent_in_r: AtomicFact = self
            .new_in_fact(pow.exponent.as_ref().clone(), StandardSet::R.into(), lf)
            .into();

        let Some(base_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&base_positive, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Some(exponent_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&exponent_in_r, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "R+: a^x from 0 < a and x in R".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactPowInRPosFromPositiveBaseRealExponent,
                ),
                vec![base_result, exponent_result],
            )
            .into(),
        )
    }

    // A positive natural greater than one has a positive natural predecessor.
    // Example: `n $in N+`, `n > 1` => `n - 1 $in N+`.
    pub(super) fn verify_in_fact_sub_in_n_pos_from_n_pos_and_greater_than_one(
        &mut self,
        in_fact: &InFact,
        sub: &Sub,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if !matches!(sub.right.as_ref(), Obj::Number(number) if number.normalized_value == "1") {
            return Ok((UnknownGenericStmtResult::new()).into());
        }

        let lf = in_fact.line_file.clone();
        let left = sub.left.as_ref().clone();
        let left_in_n_pos: AtomicFact = self
            .new_in_fact(left.clone(), StandardSet::NPos.into(), lf.clone())
            .into();
        let left_greater_than_one: AtomicFact = self
            .new_greater_fact(
                left.clone(),
                Number::new("1".to_string()).into(),
                lf.clone(),
            )
            .into();
        let two_le_left: AtomicFact = self
            .new_less_equal_fact(Number::new("2".to_string()).into(), left, lf)
            .into();
        let Some(membership_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&left_in_n_pos, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let mut bound_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
            &left_greater_than_one,
            builtin_state,
        )?;
        if bound_result.is_none() {
            // Over naturals, the common induction premise `2 <= n` is the
            // discrete spelling of `n > 1`; accept it directly so a caller
            // does not need a second builtin-order step.
            bound_result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&two_le_left, builtin_state)?;
        }
        let Some(bound_result) = bound_result else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "N+: n - 1 from n in N+ and n > 1".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactSubInNPosFromNPosAndGreaterThanOne,
                ),
                vec![membership_result, bound_result],
            )
            .into(),
        )
    }

    // `a + b $in N+` when both summands are in `N+`, or one summand is in
    // `N+` and the other is in `N`.
    // Example: `forall a, b N+: a + b $in N+`.
    pub(super) fn verify_in_fact_add_in_n_pos_from_n_pos_and_n(
        &mut self,
        in_fact: &InFact,
        add: &Add,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::NPos,
            ));
        }
        let n_pos: Obj = StandardSet::NPos.into();
        let n: Obj = StandardSet::N.into();
        let lf = in_fact.line_file.clone();

        let left_n_pos: AtomicFact = self
            .new_in_fact(add.left.as_ref().clone(), n_pos.clone(), lf.clone())
            .into();
        let right_n_pos_for_pair: AtomicFact = self
            .new_in_fact(add.right.as_ref().clone(), n_pos.clone(), lf.clone())
            .into();
        let right_n: AtomicFact = self
            .new_in_fact(add.right.as_ref().clone(), n.clone(), lf.clone())
            .into();
        let left_n: AtomicFact = self
            .new_in_fact(add.left.as_ref().clone(), n.clone(), lf.clone())
            .into();
        let right_n_pos: AtomicFact = self
            .new_in_fact(add.right.as_ref().clone(), n_pos, lf.clone())
            .into();
        let r_left_n_pos_for_pair =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&left_n_pos, builtin_state)?;
        if let Some(r_left_n_pos_for_pair) = r_left_n_pos_for_pair {
            let r_right_n_pos_for_pair = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &right_n_pos_for_pair,
                builtin_state,
            )?;
            if let Some(r_right_n_pos_for_pair) = r_right_n_pos_for_pair {
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        "N+: a + b from a in N+ and b in N+".to_string(),
                        BuiltinRuleEvidence::PositiveNaturalMembershipClosure(
                            PositiveNaturalMembershipClosureBuiltinRule::AddBothPositive,
                        ),
                        vec![r_left_n_pos_for_pair, r_right_n_pos_for_pair],
                    )
                    .into(),
                );
            }
        }

        let r_left_n_pos =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&left_n_pos, builtin_state)?;
        if let Some(r_left_n_pos) = r_left_n_pos {
            let r_right_n =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&right_n, builtin_state)?;
            if let Some(r_right_n) = r_right_n {
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        "N+: a + b from a in N+ and b in N".to_string(),
                        BuiltinRuleEvidence::PositiveNaturalMembershipClosure(
                            PositiveNaturalMembershipClosureBuiltinRule::AddLeftPositive,
                        ),
                        vec![r_left_n_pos, r_right_n],
                    )
                    .into(),
                );
            }
        }

        let r_left_n =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&left_n, builtin_state)?;
        let r_right_n_pos =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&right_n_pos, builtin_state)?;
        if let (Some(r_left_n), Some(r_right_n_pos)) = (r_left_n, r_right_n_pos) {
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "N+: a + b from a in N and b in N+".to_string(),
                    BuiltinRuleEvidence::PositiveNaturalMembershipClosure(
                        PositiveNaturalMembershipClosureBuiltinRule::AddRightPositive,
                    ),
                    vec![r_left_n, r_right_n_pos],
                )
                .into(),
            );
        }

        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            vec![
                vec![left_n_pos, right_n_pos_for_pair],
                vec![
                    self.new_in_fact(
                        add.left.as_ref().clone(),
                        StandardSet::NPos.into(),
                        lf.clone(),
                    )
                    .into(),
                    right_n,
                ],
                vec![left_n, right_n_pos],
            ],
            lf,
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "N+: a + b from complete positive-natural carrier alternatives".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyInFactAddInNPosFromNPosAndN04,
                    ),
                    vec![premise_result],
                )
                .into(),
            );
        }

        Ok(UnknownGenericStmtResult::new().into())
    }

    // `a * b $in N+` when `a $in N+` and `b $in N+` (positive naturals are closed under multiplication).
    // Example: `forall a, b N+: a * b $in N+`.
    pub(super) fn verify_in_fact_mul_in_n_pos_from_factors_in_n_pos(
        &mut self,
        in_fact: &InFact,
        mul: &Mul,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::NPos,
            ));
        }
        let n_pos: Obj = StandardSet::NPos.into();
        let lf = in_fact.line_file.clone();
        let f_left: AtomicFact = self
            .new_in_fact(mul.left.as_ref().clone(), n_pos.clone(), lf.clone())
            .into();
        let f_right: AtomicFact = self
            .new_in_fact(mul.right.as_ref().clone(), n_pos, lf.clone())
            .into();
        let Some(r_left) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&f_left, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Some(r_right) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&f_right, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "N+: a * b from a in N+ and b in N+".to_string(),
                BuiltinRuleEvidence::PositiveNaturalMembershipClosure(
                    PositiveNaturalMembershipClosureBuiltinRule::MulBothPositive,
                ),
                vec![r_left, r_right],
            )
            .into(),
        )
    }

    // `N+` = positive integers: from `0 < x` and (`x $in Z` or `x $in N`).
    // Also proves a nonzero natural is positive.
    // Example: `forall n N: n != 0 =>: n $in N+`.
    pub(super) fn verify_in_fact_n_pos_by_zero_less_and_in_z_or_n(
        &mut self,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let in_n: AtomicFact = self
            .new_in_fact(elem.clone(), StandardSet::N.into(), lf.clone())
            .into();
        let zero: Obj = Number::new("0".to_string()).into();
        let nonzero: AtomicFact = self
            .new_not_equal_fact(elem.clone(), zero.clone(), lf.clone())
            .into();
        let zero_lt_elem: AtomicFact = self.new_less_fact(zero, elem.clone(), lf.clone()).into();
        let in_z: AtomicFact = self
            .new_in_fact(elem.clone(), StandardSet::Z.into(), lf.clone())
            .into();
        let in_n_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_n, builtin_state)?;
        if let Some(in_n_result) = in_n_result {
            let nonzero_result =
                self.try_verify_atomic_fact_as_builtin_rule_premise(&nonzero, builtin_state)?;
            if let Some(nonzero_result) = nonzero_result {
                return Ok(
                    number_in_set_verified_by_builtin_rules_result_with_subgoals(
                        in_fact,
                        "N+: x in N and x != 0",
                        vec![in_n_result, nonzero_result],
                    ),
                );
            }
        }

        let zero_lt_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&zero_lt_elem, builtin_state)?;
        let in_z_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_z, builtin_state)?;
        if zero_lt_result.is_some() && in_z_result.is_some() {
            let zero_lt_result = zero_lt_result.expect("checked above");
            let in_z_result = in_z_result.expect("checked above");
            return Ok(
                number_in_set_verified_by_builtin_rules_result_with_subgoals(
                    in_fact,
                    "N+: 0 < x and x in Z",
                    vec![zero_lt_result, in_z_result],
                ),
            );
        }

        let in_n_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_n, builtin_state)?;
        if let (Some(zero_lt_result), Some(in_n_result)) = (zero_lt_result, in_n_result) {
            return Ok(
                number_in_set_verified_by_builtin_rules_result_with_subgoals(
                    in_fact,
                    "N+: 0 < x and x in N",
                    vec![zero_lt_result, in_n_result],
                ),
            );
        }

        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            vec![
                vec![in_n, nonzero],
                vec![zero_lt_elem.clone(), in_z],
                vec![
                    zero_lt_elem,
                    self.new_in_fact(elem.clone(), StandardSet::N.into(), lf.clone())
                        .into(),
                ],
            ],
            lf,
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(
                number_in_set_verified_by_builtin_rules_result_with_subgoals(
                    in_fact,
                    "N+: complete nonzero-natural or positive-integer carrier alternatives",
                    vec![premise_result],
                ),
            );
        }

        Ok((UnknownGenericStmtResult::new()).into())
    }

    // `Q+` and `R+` are the positive elements of their base sets.
    // Example: from `a $in Q` and `0 < a`, prove `a $in Q+`.
    pub(super) fn verify_in_fact_standard_positive_by_zero_less_and_base_set(
        &mut self,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
        base_set: StandardSet,
        rule_name: &str,
    ) -> Result<ProveFactResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let zero: Obj = Number::new("0".to_string()).into();
        let zero_lt_elem: AtomicFact = self.new_less_fact(zero, elem.clone(), lf.clone()).into();
        let zero_lt_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&zero_lt_elem, builtin_state)?;
        let Some(zero_lt_result) = zero_lt_result else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        let in_base_set: AtomicFact = self.new_in_fact(elem.clone(), base_set.into(), lf).into();
        let in_base_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_base_set, builtin_state)?;
        let Some(in_base_result) = in_base_result else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        Ok(
            number_in_set_verified_by_builtin_rules_result_with_subgoals(
                in_fact,
                rule_name,
                vec![zero_lt_result, in_base_result],
            ),
        )
    }

    // `N` = nonnegative integers: from `x $in Z` and `x >= 0`; strict `x > 0` also suffices.
    // Example: after `a, b $in Z` and `b - a >= 0`, Litex verifies `b - a $in N`.
    // Also covers predecessors of positive naturals: `forall n N+: n - 1 $in N`.
    pub(super) fn verify_in_fact_n_by_nonnegative_integer(
        &mut self,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();

        let in_n_pos: AtomicFact = self
            .new_in_fact(elem.clone(), StandardSet::NPos.into(), lf.clone())
            .into();
        let in_n_pos_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_n_pos, builtin_state)?;
        if let Some(in_n_pos_result) = in_n_pos_result {
            return Ok(
                number_in_set_verified_by_builtin_rules_result_with_subgoals(
                    in_fact,
                    "N: x in N+",
                    vec![in_n_pos_result],
                ),
            );
        }

        let in_z: AtomicFact = self
            .new_in_fact(elem.clone(), StandardSet::Z.into(), lf.clone())
            .into();
        let zero: Obj = Number::new("0".to_string()).into();
        let order_facts: [AtomicFact; 4] = [
            self.new_greater_equal_fact(elem.clone(), zero.clone(), lf.clone())
                .into(),
            self.new_less_equal_fact(zero.clone(), elem.clone(), lf.clone())
                .into(),
            self.new_greater_fact(elem.clone(), zero.clone(), lf.clone())
                .into(),
            self.new_less_fact(zero, elem.clone(), lf).into(),
        ];
        let in_z_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_z, builtin_state)?;
        if let Some(in_z_result) = in_z_result {
            for order_fact in &order_facts {
                let order_result =
                    self.try_verify_atomic_fact_as_builtin_rule_premise(order_fact, builtin_state)?;
                if let Some(order_result) = order_result {
                    return Ok(
                        number_in_set_verified_by_builtin_rules_result_with_subgoals(
                            in_fact,
                            "N: x in Z and x >= 0 or x > 0",
                            vec![in_z_result, order_result],
                        ),
                    );
                }
            }
        }

        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            order_facts
                .into_iter()
                .map(|order_fact| vec![in_z.clone(), order_fact])
                .collect(),
            in_fact.line_file.clone(),
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(
                number_in_set_verified_by_builtin_rules_result_with_subgoals(
                    in_fact,
                    "N: complete integer-and-nonnegative-order alternatives",
                    vec![premise_result],
                ),
            );
        }

        Ok((UnknownGenericStmtResult::new()).into())
    }

    pub(super) fn verify_in_fact_closed_range_by_order_bounds(
        &mut self,
        in_fact: &InFact,
        closed_range: &ClosedRange,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let chain_premise = QuantifierFreeFact::ChainFact(self.new_chain_fact(
            vec![
                closed_range.start.as_ref().clone(),
                elem.clone(),
                closed_range.end.as_ref().clone(),
            ],
            vec![
                AtomicName::WithoutMod(LESS_EQUAL.to_string()),
                AtomicName::WithoutMod(LESS_EQUAL.to_string()),
            ],
            lf.clone(),
        ));
        let chain_result = self.try_verify_builtin_rule_premise(&chain_premise, builtin_state)?;
        if let Some(chain_result) = chain_result {
            return Ok(
                number_in_set_verified_by_builtin_rules_result_with_subgoals(
                    in_fact,
                    "in closed_range from complete bound chain",
                    vec![chain_result],
                ),
            );
        }

        let Some(mut subgoals) = self.order_lower_bound_from_literals(
            elem,
            closed_range.start.as_ref(),
            &lf,
            builtin_state,
        )?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Some(mut upper_subgoals) = self.order_upper_bound_closed_from_literals(
            elem,
            closed_range.end.as_ref(),
            &lf,
            builtin_state,
        )?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        subgoals.append(&mut upper_subgoals);
        Ok(
            number_in_set_verified_by_builtin_rules_result_with_subgoals(
                in_fact,
                "in closed_range: a <= i and i <= b",
                subgoals,
            ),
        )
    }

    pub(super) fn verify_in_fact_open_range_by_order_bounds(
        &mut self,
        in_fact: &InFact,
        range: &Range,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let chain_premise = QuantifierFreeFact::ChainFact(self.new_chain_fact(
            vec![
                range.start.as_ref().clone(),
                elem.clone(),
                range.end.as_ref().clone(),
            ],
            vec![
                AtomicName::WithoutMod(LESS_EQUAL.to_string()),
                AtomicName::WithoutMod(LESS.to_string()),
            ],
            lf.clone(),
        ));
        let chain_result = self.try_verify_builtin_rule_premise(&chain_premise, builtin_state)?;
        if let Some(chain_result) = chain_result {
            return Ok(
                number_in_set_verified_by_builtin_rules_result_with_subgoals(
                    in_fact,
                    "in range from complete bound chain",
                    vec![chain_result],
                ),
            );
        }

        let Some(mut subgoals) =
            self.order_lower_bound_from_literals(elem, range.start.as_ref(), &lf, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Some(mut upper_subgoals) = self.order_upper_bound_open_from_literals(
            elem,
            range.end.as_ref(),
            &lf,
            builtin_state,
        )?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        subgoals.append(&mut upper_subgoals);
        Ok(
            number_in_set_verified_by_builtin_rules_result_with_subgoals(
                in_fact,
                "in range: a <= i and i < b",
                subgoals,
            ),
        )
    }

    pub(super) fn verify_in_fact_interval_by_real_order_bounds(
        &mut self,
        in_fact: &InFact,
        interval: &IntervalObj,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        // Real interval membership requires a real element and the endpoint inequalities.
        // Example: `x $in '(a, b]` follows from `x $in R`, `a < x`, and `x <= b`.
        let in_r: AtomicFact = self
            .new_in_fact(elem.clone(), StandardSet::R.into(), lf.clone())
            .into();
        let lower: AtomicFact = if interval.left_closed() {
            self.new_less_equal_fact(interval.start().clone(), elem.clone(), lf.clone())
                .into()
        } else {
            self.new_less_fact(interval.start().clone(), elem.clone(), lf.clone())
                .into()
        };
        let upper: AtomicFact = if interval.right_closed() {
            self.new_less_equal_fact(elem.clone(), interval.end().clone(), lf.clone())
                .into()
        } else {
            self.new_less_fact(elem.clone(), interval.end().clone(), lf.clone())
                .into()
        };
        let conjunction = QuantifierFreeFact::AndFact(
            self.new_and_fact(vec![in_r.clone(), lower.clone(), upper.clone()], lf.clone()),
        );
        let conjunction_result =
            self.try_verify_builtin_rule_premise(&conjunction, builtin_state)?;
        if let Some(conjunction_result) = conjunction_result {
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "in real interval from complete carrier-and-bounds conjunction".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyInFactIntervalByRealOrderBounds01,
                    ),
                    vec![conjunction_result],
                )
                .into(),
            );
        }

        let mut step_results = Vec::new();
        let Some(in_r_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_r, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        step_results.push(in_r_result);
        let lower_result =
            self.verify_known_interval_order_bound(&lower, builtin_state.verify_state())?;
        if !lower_result.is_success() {
            return Ok((UnknownGenericStmtResult::new()).into());
        }
        step_results.push(lower_result);
        let upper_result =
            self.verify_known_interval_order_bound(&upper, builtin_state.verify_state())?;
        if !upper_result.is_success() {
            return Ok((UnknownGenericStmtResult::new()).into());
        }
        step_results.push(upper_result);

        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "in real interval: x in R and endpoint bounds".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactIntervalByRealOrderBounds02,
                ),
                step_results,
            )
            .into(),
        )
    }

    pub(super) fn verify_in_fact_one_side_infinity_interval_by_real_order_bound(
        &mut self,
        in_fact: &InFact,
        interval: &OneSideInfinityIntervalObj,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        // Half-infinite real interval membership requires a real element and the finite endpoint bound.
        // Example: `x $in '[a,)` follows from `x $in R` and `a <= x`.
        let in_r: AtomicFact = self
            .new_in_fact(elem.clone(), StandardSet::R.into(), lf.clone())
            .into();
        let bound: AtomicFact = match interval {
            OneSideInfinityIntervalObj::LeftOpen(_) => self
                .new_less_fact(interval.start().clone(), elem.clone(), lf.clone())
                .into(),
            OneSideInfinityIntervalObj::LeftClosed(_) => self
                .new_less_equal_fact(interval.start().clone(), elem.clone(), lf.clone())
                .into(),
            OneSideInfinityIntervalObj::RightOpen(_) => self
                .new_less_fact(elem.clone(), interval.start().clone(), lf.clone())
                .into(),
            OneSideInfinityIntervalObj::RightClosed(_) => self
                .new_less_equal_fact(elem.clone(), interval.start().clone(), lf.clone())
                .into(),
        };
        let conjunction =
            QuantifierFreeFact::AndFact(self.new_and_fact(vec![in_r.clone(), bound.clone()], lf));
        let conjunction_result =
            self.try_verify_builtin_rule_premise(&conjunction, builtin_state)?;
        if let Some(conjunction_result) = conjunction_result {
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "in half-infinite real interval from complete carrier-and-bound conjunction"
                        .to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactOneSideInfinityIntervalByRealOrderBound01),
                    vec![conjunction_result],
                )
                .into(),
            );
        }

        let mut step_results = Vec::new();
        let Some(in_r_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_r, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        step_results.push(in_r_result);
        let bound_result =
            self.verify_known_interval_order_bound(&bound, builtin_state.verify_state())?;
        if !bound_result.is_success() {
            return Ok((UnknownGenericStmtResult::new()).into());
        }
        step_results.push(bound_result);

        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "in half-infinite real interval: x in R and endpoint bound".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactOneSideInfinityIntervalByRealOrderBound02,
                ),
                step_results,
            )
            .into(),
        )
    }

    fn verify_known_interval_order_bound(
        &mut self,
        bound: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        let exact = self.verify_atomic_except_equality_with_known_atomic_facts(bound)?;
        if exact.is_success() {
            return self.complete_atomic_fact_proof_result(bound, exact, verify_state);
        }
        let computed = self.verify_atomic_except_equality_with_zero_premise_verification(bound)?;
        if computed.is_success() {
            return self.complete_atomic_fact_proof_result(bound, computed, verify_state);
        }

        let stronger = match bound {
            AtomicFact::LessEqualFact(fact) => Some((
                self.new_less_fact(
                    fact.left.clone(),
                    fact.right.clone(),
                    fact.line_file.clone(),
                )
                .into(),
                ArithmeticBuiltinRule::LessEqualFromStrictOrder,
            )),
            AtomicFact::GreaterEqualFact(fact) => Some((
                self.new_greater_fact(
                    fact.left.clone(),
                    fact.right.clone(),
                    fact.line_file.clone(),
                )
                .into(),
                ArithmeticBuiltinRule::GreaterEqualFromStrictOrder,
            )),
            _ => None,
        };
        let Some((stronger, rule)) = stronger else {
            return self.complete_atomic_fact_proof_result(
                bound,
                UnknownGenericStmtResult::new().into(),
                verify_state,
            );
        };
        let stronger_proof =
            self.verify_atomic_except_equality_with_known_atomic_facts(&stronger)?;
        if !stronger_proof.is_success() {
            return self.complete_atomic_fact_proof_result(bound, stronger_proof, verify_state);
        }
        let stronger_result =
            self.complete_atomic_fact_proof_result(&stronger, stronger_proof, verify_state)?;
        let proof =
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                bound.clone().into(),
                "weak interval bound from known strict order".to_string(),
                BuiltinRuleEvidence::Arithmetic(rule),
                vec![stronger_result],
            )
            .into();
        self.complete_atomic_fact_proof_result(bound, proof, verify_state)
    }

    // When `x $in Z` and endpoints are integer literals: `lo <= x` iff `lo - 1 < x` (discrete lower).
    // Example: dom `1 < i` with `i $in Z` proves the lower side of `i $in range(2, 6)` / `closed_range(2, 5)`.
    pub(super) fn order_lower_bound_from_literals(
        &mut self,
        elem: &Obj,
        lower: &Obj,
        lf: &LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let weak: AtomicFact = self
            .new_less_equal_fact(lower.clone(), elem.clone(), lf.clone())
            .into();
        let weak_result =
            self.verify_known_interval_order_bound(&weak, builtin_state.verify_state())?;
        if weak_result.is_success() {
            return Ok(Some(vec![weak_result]));
        }
        let in_z: AtomicFact = self
            .new_in_fact(elem.clone(), StandardSet::Z.into(), lf.clone())
            .into();
        let Some(in_z_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_z, builtin_state)?
        else {
            return Ok(None);
        };
        let Some(lower_num) = self.resolve_obj_to_number_resolved(lower) else {
            return Ok(None);
        };
        if !is_integer_after_simplification(&lower_num) {
            return Ok(None);
        }
        let pred = Obj::Sub(Sub::new(lower.clone(), Number::new("1".to_string()).into()));
        let Some(pred_n) = pred.evaluate_to_normalized_decimal_number() else {
            return Ok(None);
        };
        let strict: AtomicFact = self
            .new_less_fact(pred_n.into(), elem.clone(), lf.clone())
            .into();
        let strict_result =
            self.verify_known_interval_order_bound(&strict, builtin_state.verify_state())?;
        if strict_result.is_success() {
            Ok(Some(vec![in_z_result, strict_result]))
        } else {
            Ok(None)
        }
    }

    // When `x $in Z` and `hi` is an integer literal: `x < hi` iff `x <= hi - 1`.
    // Example: `i <= 5` and `i $in Z` gives the upper side of `i $in range(2, 6)`.
    pub(super) fn order_upper_bound_open_from_literals(
        &mut self,
        elem: &Obj,
        upper: &Obj,
        lf: &LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let strict: AtomicFact = self
            .new_less_fact(elem.clone(), upper.clone(), lf.clone())
            .into();
        let strict_result =
            self.verify_known_interval_order_bound(&strict, builtin_state.verify_state())?;
        if strict_result.is_success() {
            return Ok(Some(vec![strict_result]));
        }
        let in_z: AtomicFact = self
            .new_in_fact(elem.clone(), StandardSet::Z.into(), lf.clone())
            .into();
        let Some(in_z_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_z, builtin_state)?
        else {
            return Ok(None);
        };
        let Some(upper_num) = self.resolve_obj_to_number_resolved(upper) else {
            return Ok(None);
        };
        if !is_integer_after_simplification(&upper_num) {
            return Ok(None);
        }
        let upper_minus_one =
            Obj::Sub(Sub::new(upper.clone(), Number::new("1".to_string()).into()));
        let Some(um) = upper_minus_one.evaluate_to_normalized_decimal_number() else {
            return Ok(None);
        };
        let weak: AtomicFact = self
            .new_less_equal_fact(elem.clone(), um.into(), lf.clone())
            .into();
        let weak_result =
            self.verify_known_interval_order_bound(&weak, builtin_state.verify_state())?;
        if weak_result.is_success() {
            Ok(Some(vec![in_z_result, weak_result]))
        } else {
            Ok(None)
        }
    }

    // When `x $in Z` and `hi` is an integer literal: `x <= hi` iff `x < hi + 1`.
    pub(super) fn order_upper_bound_closed_from_literals(
        &mut self,
        elem: &Obj,
        upper: &Obj,
        lf: &LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let weak: AtomicFact = self
            .new_less_equal_fact(elem.clone(), upper.clone(), lf.clone())
            .into();
        let weak_result =
            self.verify_known_interval_order_bound(&weak, builtin_state.verify_state())?;
        if weak_result.is_success() {
            return Ok(Some(vec![weak_result]));
        }
        let in_z: AtomicFact = self
            .new_in_fact(elem.clone(), StandardSet::Z.into(), lf.clone())
            .into();
        let Some(in_z_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_z, builtin_state)?
        else {
            return Ok(None);
        };
        let Some(upper_num) = self.resolve_obj_to_number_resolved(upper) else {
            return Ok(None);
        };
        if !is_integer_after_simplification(&upper_num) {
            return Ok(None);
        }
        let hi_plus_one = Obj::Add(Add::new(upper.clone(), Number::new("1".to_string()).into()));
        let Some(hp) = hi_plus_one.evaluate_to_normalized_decimal_number() else {
            return Ok(None);
        };
        let strict: AtomicFact = self
            .new_less_fact(elem.clone(), hp.into(), lf.clone())
            .into();
        let strict_result =
            self.verify_known_interval_order_bound(&strict, builtin_state.verify_state())?;
        if strict_result.is_success() {
            Ok(Some(vec![in_z_result, strict_result]))
        } else {
            Ok(None)
        }
    }

    // Complex scalar closure. Well-definedness already establishes the complex operand domains,
    // the nonzero divisor/base obligations, and the allowed exponent set.
    // Example: `z C, n N` implies `z^n $in C`.
    pub(super) fn verify_in_fact_arithmetic_expression_in_c(
        &mut self,
        in_fact: &InFact,
        _builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let rule = match &in_fact.element {
            Obj::Add(_) => Some(ComplexArithmeticMembershipClosureBuiltinRule::Add),
            Obj::Sub(_) => Some(ComplexArithmeticMembershipClosureBuiltinRule::Sub),
            Obj::Mul(_) => Some(ComplexArithmeticMembershipClosureBuiltinRule::Mul),
            Obj::Div(_) => Some(ComplexArithmeticMembershipClosureBuiltinRule::Div),
            _ => None,
        };
        let Some(rule) = rule else {
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "complex scalar arithmetic is closed in C",
            ));
        };
        Ok(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "complex scalar arithmetic is closed in C".to_string(),
                BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule),
                Vec::new(),
            )
            .into(),
        )
    }

    // Real closure requires real operands. This deliberately does not infer that every
    // well-defined arithmetic expression is real: a complex square remains complex.
    // Example: `a, b R` implies `a+b $in R`, while `i+1 $in R` remains unknown.
    pub(super) fn verify_in_fact_arithmetic_expression_in_r(
        &mut self,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        let real: Obj = StandardSet::R.into();
        let lf = in_fact.line_file.clone();
        let (required, evidence) = match &in_fact.element {
            Obj::Add(add) => (
                vec![
                    self.new_in_fact(add.left.as_ref().clone(), real.clone(), lf.clone())
                        .into(),
                    self.new_in_fact(add.right.as_ref().clone(), real.clone(), lf.clone())
                        .into(),
                ],
                Some(RealArithmeticMembershipClosureBuiltinRule::Add),
            ),
            Obj::Sub(sub) => (
                vec![
                    self.new_in_fact(sub.left.as_ref().clone(), real.clone(), lf.clone())
                        .into(),
                    self.new_in_fact(sub.right.as_ref().clone(), real.clone(), lf.clone())
                        .into(),
                ],
                Some(RealArithmeticMembershipClosureBuiltinRule::Sub),
            ),
            Obj::Mul(mul) => (
                vec![
                    self.new_in_fact(mul.left.as_ref().clone(), real.clone(), lf.clone())
                        .into(),
                    self.new_in_fact(mul.right.as_ref().clone(), real.clone(), lf.clone())
                        .into(),
                ],
                Some(RealArithmeticMembershipClosureBuiltinRule::Mul),
            ),
            Obj::Div(div) => (
                vec![
                    self.new_in_fact(div.left.as_ref().clone(), real.clone(), lf.clone())
                        .into(),
                    self.new_in_fact(div.right.as_ref().clone(), real.clone(), lf.clone())
                        .into(),
                ],
                Some(RealArithmeticMembershipClosureBuiltinRule::Div),
            ),
            Obj::Pow(pow) => (
                vec![self
                    .new_in_fact(pow.base.as_ref().clone(), real.clone(), lf.clone())
                    .into()],
                Some(RealArithmeticMembershipClosureBuiltinRule::Pow),
            ),
            Obj::Abs(_) => (
                Vec::new(),
                Some(RealArithmeticMembershipClosureBuiltinRule::Abs),
            ),
            Obj::Mod(_)
            | Obj::Quot(_)
            | Obj::Sin(_)
            | Obj::Arcsin(_)
            | Obj::Cos(_)
            | Obj::Tan(_)
            | Obj::Cot(_)
            | Obj::Sqrt(_)
            | Obj::Log(_) => (Vec::new(), None),
            _ => return Ok(UnknownGenericStmtResult::new().into()),
        };
        let Some(subgoals) = self.verify_builtin_rule_premises(&required, builtin_state)? else {
            return Ok(UnknownGenericStmtResult::new().into());
        };
        Ok(match evidence {
            Some(rule) => {
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "real arithmetic has real operands and result".to_string(),
                    BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule),
                    subgoals,
                )
                .into()
            }
            None => number_in_set_verified_by_builtin_rules_result_with_subgoals(
                in_fact,
                "real arithmetic has real operands and result",
                subgoals,
            ),
        })
    }

    pub fn verify_objects_are_known_reals_in_builtin(
        &mut self,
        objs: &[&Obj],
        line_file: &LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let mut direct_premises = Vec::new();
        let mut direct_seen = Vec::new();
        for obj in objs {
            let key = obj.to_string();
            if direct_seen.contains(&key) {
                continue;
            }
            direct_seen.push(key);
            direct_premises.push(
                self.new_in_fact((*obj).clone(), StandardSet::R.into(), line_file.clone())
                    .into(),
            );
        }
        if direct_premises.len() > 1 {
            if let Some(results) =
                self.verify_builtin_rule_premises(&direct_premises, builtin_state)?
            {
                return Ok(Some(results));
            }
        }

        let mut seen = Vec::new();
        let mut steps = Vec::new();
        for obj in objs {
            let key = obj.to_string();
            if seen.contains(&key) {
                continue;
            }
            seen.push(key);
            let Some(mut object_steps) =
                self.verify_one_object_is_known_real_in_builtin(obj, line_file, builtin_state)?
            else {
                return Ok(None);
            };
            steps.append(&mut object_steps);
        }
        Ok(Some(steps))
    }

    /// Requires every operand to belong to the native scalar field `C`.
    /// Real operands are accepted through the standard-set inclusion `R subset C`.
    /// Example: both real and complex factors may use field zero-product laws.
    pub fn verify_objects_are_known_real_or_complex_scalars_in_builtin(
        &mut self,
        objs: &[&Obj],
        line_file: &LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let mut premises = Vec::new();
        let mut seen = Vec::new();
        for obj in objs {
            let key = obj.to_string();
            if seen.contains(&key) {
                continue;
            }
            seen.push(key);
            premises.push(
                self.new_in_fact((*obj).clone(), StandardSet::C.into(), line_file.clone())
                    .into(),
            );
        }
        self.verify_builtin_rule_premises(&premises, builtin_state)
    }

    pub fn verify_objects_are_known_integers_in_builtin_leaf(
        &mut self,
        objs: &[&Obj],
        line_file: &LineFile,
        verify_state: &VerifyState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let mut seen = Vec::new();
        let mut steps = Vec::new();
        for obj in objs {
            let key = obj.to_string();
            if seen.contains(&key) {
                continue;
            }
            seen.push(key);

            let in_z: AtomicFact = self
                .new_in_fact((*obj).clone(), StandardSet::Z.into(), line_file.clone())
                .into();
            let direct_proof = if let Some(result) =
                self.verification_result_from_proof_search_memo(&in_z, verify_state)
            {
                result
            } else {
                self.verify_atomic_except_equality_with_zero_premise_verification(&in_z)?
            };
            if let Some(direct_result) = self.complete_proven_fact_candidate(
                in_z.clone().into(),
                direct_proof,
                verify_state,
            )? {
                steps.push(direct_result);
                continue;
            }

            // Integer expressions are closed under addition, subtraction,
            // and multiplication. Recurse only through these strictly smaller
            // syntax nodes so order rules can recognize composite endpoints
            // without opening general builtin proof search.
            let integer_operands: Option<([&Obj; 2], IntegerMembershipClosureBuiltinRule)> =
                match obj {
                    Obj::Add(add) => Some((
                        [add.left.as_ref(), add.right.as_ref()],
                        IntegerMembershipClosureBuiltinRule::Add,
                    )),
                    Obj::Sub(sub) => Some((
                        [sub.left.as_ref(), sub.right.as_ref()],
                        IntegerMembershipClosureBuiltinRule::Sub,
                    )),
                    Obj::Mul(mul) => Some((
                        [mul.left.as_ref(), mul.right.as_ref()],
                        IntegerMembershipClosureBuiltinRule::Mul,
                    )),
                    _ => None,
                };
            if let Some((integer_operands, rule)) = integer_operands {
                if let Some(operator_steps) = self
                    .verify_objects_are_known_integers_in_builtin_leaf(
                        &integer_operands,
                        line_file,
                        verify_state,
                    )?
                {
                    let proof =
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            in_z.clone().into(),
                            "integer expression closure under +, -, and *".to_string(),
                            BuiltinRuleEvidence::IntegerMembershipClosure(rule),
                            operator_steps,
                        )
                        .into();
                    if let Some(result) = self.complete_proven_fact_candidate(
                        in_z.clone().into(),
                        proof,
                        verify_state,
                    )? {
                        steps.push(result);
                        continue;
                    }
                }
            }

            // `finite_set_size(S)` is natural once `S` is already known finite.
            // This integer leaf may reuse that exact premise, but must not prove
            // it with another direct builtin rule. Example: a finite-set binder
            // lets integer discreteness treat `finite_set_size(S)` as integral.
            if let Obj::FiniteSetSize(finite_set_size) = obj {
                let in_n =
                    self.new_in_fact((*obj).clone(), StandardSet::N.into(), line_file.clone());
                let finite_fact: AtomicFact = self
                    .new_is_finite_set_fact(finite_set_size.set.as_ref().clone(), line_file.clone())
                    .into();
                let finite_proof = if let Some(result) =
                    self.verification_result_from_proof_search_memo(&finite_fact, verify_state)
                {
                    result
                } else {
                    self.verify_atomic_except_equality_with_known_atomic_facts(&finite_fact)?
                };
                if let Some(finite_result) = self.complete_proven_fact_candidate(
                    finite_fact.clone().into(),
                    finite_proof,
                    verify_state,
                )? {
                    let proof = number_in_set_verified_by_builtin_rules_result_with_subgoals(
                        &in_n,
                        "finite_set_size of a known finite set is a natural number",
                        vec![finite_result],
                    );
                    let in_n_atomic: AtomicFact = in_n.into();
                    let Some(result) = self.complete_proven_fact_candidate(
                        in_n_atomic.into(),
                        proof,
                        verify_state,
                    )?
                    else {
                        return Ok(None);
                    };
                    steps.push(result);
                    continue;
                }
            }

            let mut carrier_steps = None;
            for source_set in self.known_sets_containing_obj(obj) {
                let Obj::StandardSet(source_standard_set) = &source_set else {
                    continue;
                };
                if !source_standard_set.is_subset_eq(&StandardSet::Z) {
                    continue;
                }
                let source_membership: AtomicFact = self
                    .new_in_fact((*obj).clone(), source_set.clone(), line_file.clone())
                    .into();
                let source_proof =
                    self.verify_atomic_except_equality_with_known_atomic_facts(&source_membership)?;
                let Some(source_result) = self.complete_proven_fact_candidate(
                    source_membership.clone().into(),
                    source_proof,
                    verify_state,
                )?
                else {
                    continue;
                };
                let subset_fact: AtomicFact = self
                    .new_subset_fact(source_set, StandardSet::Z.into(), line_file.clone())
                    .into();
                let subset_proof =
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        subset_fact.clone().into(),
                        "standard_set_subset".to_string(),
                        BuiltinRuleEvidence::StandardSetSubset,
                        Vec::new(),
                    )
                    .into();
                let Some(subset_result) = self.complete_proven_fact_candidate(
                    subset_fact.clone().into(),
                    subset_proof,
                    verify_state,
                )?
                else {
                    continue;
                };
                carrier_steps = Some(vec![source_result, subset_result]);
                break;
            }
            let Some(mut carrier_steps) = carrier_steps else {
                return Ok(None);
            };
            steps.append(&mut carrier_steps);
        }
        Ok(Some(steps))
    }

    fn verify_one_object_is_known_real_in_builtin(
        &mut self,
        obj: &Obj,
        line_file: &LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<Vec<VerifyFactResult>>, RuntimeError> {
        let in_r: AtomicFact = self
            .new_in_fact(obj.clone(), StandardSet::R.into(), line_file.clone())
            .into();
        if let Some(direct_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_r, builtin_state)?
        {
            return Ok(Some(vec![direct_result]));
        }

        // Equality-class resolution and literal evaluation are pure normalization, not a
        // recursive proof in another fact family.  This keeps finite enumeration cases such as
        // `a = 1` usable by numeric builtin rules without opening another semantic rule.
        if self.resolve_obj_to_number_resolved(obj).is_some() {
            return Ok(Some(Vec::new()));
        }

        for source_set in self.known_sets_containing_obj(obj) {
            let source_membership: AtomicFact = self
                .new_in_fact(obj.clone(), source_set.clone(), line_file.clone())
                .into();
            let source_proof =
                self.verify_atomic_except_equality_with_known_atomic_facts(&source_membership)?;
            let source_result = self.complete_atomic_fact_proof_result(
                &source_membership,
                source_proof,
                builtin_state.verify_state(),
            )?;
            if !source_result.is_success() {
                continue;
            }
            for carrier in [
                StandardSet::R,
                StandardSet::NPos,
                StandardSet::N,
                StandardSet::ZNeg,
                StandardSet::ZStar,
                StandardSet::Z,
                StandardSet::Q,
                StandardSet::QPos,
                StandardSet::QNeg,
                StandardSet::QStar,
                StandardSet::RPos,
                StandardSet::RNeg,
                StandardSet::RStar,
            ] {
                let subset: AtomicFact = self
                    .new_subset_fact(
                        source_set.clone(),
                        carrier.clone().into(),
                        line_file.clone(),
                    )
                    .into();
                if let (Obj::StandardSet(source), AtomicFact::SubsetFact(subset_fact)) =
                    (&source_set, &subset)
                {
                    if source.is_subset_eq(&carrier) {
                        let subset_proof =
                            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                subset_fact.clone().into(),
                                "standard_set_subset".to_string(),
                                BuiltinRuleEvidence::StandardSetSubset,
                                Vec::new(),
                            )
                            .into();
                        let subset_result = self.complete_atomic_fact_proof_result(
                            &subset,
                            subset_proof,
                            builtin_state.verify_state(),
                        )?;
                        return Ok(Some(vec![source_result, subset_result]));
                    }
                }
                let subset_proof =
                    self.verify_atomic_except_equality_with_known_atomic_facts(&subset)?;
                let subset_result = self.complete_atomic_fact_proof_result(
                    &subset,
                    subset_proof,
                    builtin_state.verify_state(),
                )?;
                if subset_result.is_success() {
                    return Ok(Some(vec![source_result, subset_result]));
                }
            }
        }

        if matches!(obj, Obj::Number(_) | Obj::EulerNumber(_) | Obj::Pi(_)) {
            return Ok(Some(Vec::new()));
        }

        let iterated_func = match obj {
            Obj::Sum(sum) => Some(sum.func.as_ref()),
            Obj::SumOfFiniteSet(sum) => Some(sum.func.as_ref()),
            Obj::Product(product) => Some(product.func.as_ref()),
            Obj::ProductOfFiniteSet(product) => Some(product.func.as_ref()),
            _ => None,
        };
        if let Some(func) = iterated_func {
            let Some(Obj::StandardSet(ret_set)) = self.iterated_op_func_ret_set(func) else {
                return Ok(None);
            };
            return if ret_set.is_subset_eq(&StandardSet::R) {
                Ok(Some(Vec::new()))
            } else {
                Ok(None)
            };
        }

        let child_objects: Vec<&Obj> = match obj {
            Obj::Add(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Sub(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Mul(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Div(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Mod(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Gcd(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Lcm(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Min(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Max(x) => vec![x.left.as_ref(), x.right.as_ref()],
            Obj::Pow(x) => vec![x.base.as_ref(), x.exponent.as_ref()],
            Obj::Log(x) => vec![x.base.as_ref(), x.arg.as_ref()],
            Obj::Floor(x) => vec![x.arg.as_ref()],
            Obj::Ceil(x) => vec![x.arg.as_ref()],
            Obj::Exp(x) => vec![x.arg.as_ref()],
            Obj::Ln(x) => vec![x.arg.as_ref()],
            Obj::Sign(x) => vec![x.arg.as_ref()],
            Obj::Factorial(x) => vec![x.arg.as_ref()],
            Obj::Abs(x) => vec![x.arg.as_ref()],
            Obj::Sin(x) => vec![x.arg.as_ref()],
            Obj::Arcsin(x) => vec![x.arg.as_ref()],
            Obj::Cos(x) => vec![x.arg.as_ref()],
            Obj::Tan(x) => vec![x.arg.as_ref()],
            Obj::Cot(x) => vec![x.arg.as_ref()],
            // These operators have real codomain. Their complex-domain obligation
            // belongs to the enclosing fact's well-definedness phase, not to a
            // separate builtin-rule premise.
            Obj::RealPart(_) | Obj::ImaginaryPart(_) | Obj::ComplexAbs(_) => {
                return Ok(Some(Vec::new()));
            }
            Obj::Sqrt(x) => vec![x.arg.as_ref()],
            Obj::FiniteSetSize(_) | Obj::FiniteSetMax(_) | Obj::FiniteSetMin(_) => {
                return Ok(Some(Vec::new()));
            }
            _ => return Ok(None),
        };

        let mut steps = Vec::new();
        for child in child_objects {
            let Some(mut child_steps) =
                self.verify_one_object_is_known_real_in_builtin(child, line_file, builtin_state)?
            else {
                return Ok(None);
            };
            steps.append(&mut child_steps);
        }
        Ok(Some(steps))
    }

    // Builtin closure of `Z` under `+`, `-`, `*`, `mod`, Euclidean quotient, and natural-number powers.
    // Example: `forall a Z, k N: a^k $in Z`.
    pub(super) fn verify_in_fact_arithmetic_expression_in_z(
        &mut self,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::Z,
            ));
        }
        let z_obj: Obj = StandardSet::Z.into();
        let n_obj: Obj = StandardSet::N.into();
        let n_pos_obj: Obj = StandardSet::NPos.into();
        let lf = in_fact.line_file.clone();

        let subgoals = match &in_fact.element {
            Obj::Add(a) => self.verify_builtin_rule_premises(
                &[
                    self.new_in_fact(a.left.as_ref().clone(), z_obj.clone(), lf.clone())
                        .into(),
                    self.new_in_fact(a.right.as_ref().clone(), z_obj.clone(), lf.clone())
                        .into(),
                ],
                builtin_state,
            )?,
            Obj::Sub(s) => self.verify_builtin_rule_premises(
                &[
                    self.new_in_fact(s.left.as_ref().clone(), z_obj.clone(), lf.clone())
                        .into(),
                    self.new_in_fact(s.right.as_ref().clone(), z_obj.clone(), lf.clone())
                        .into(),
                ],
                builtin_state,
            )?,
            Obj::Mul(m) => self.verify_builtin_rule_premises(
                &[
                    self.new_in_fact(m.left.as_ref().clone(), z_obj.clone(), lf.clone())
                        .into(),
                    self.new_in_fact(m.right.as_ref().clone(), z_obj.clone(), lf.clone())
                        .into(),
                ],
                builtin_state,
            )?,
            Obj::Mod(m) => self.verify_builtin_rule_premises(
                &[
                    self.new_in_fact(m.left.as_ref().clone(), z_obj.clone(), lf.clone())
                        .into(),
                    self.new_in_fact(m.right.as_ref().clone(), z_obj.clone(), lf.clone())
                        .into(),
                ],
                builtin_state,
            )?,
            Obj::Quot(x) => self.verify_builtin_rule_premises(
                &[
                    self.new_in_fact(x.left.as_ref().clone(), z_obj.clone(), lf.clone())
                        .into(),
                    self.new_in_fact(x.right.as_ref().clone(), n_pos_obj.clone(), lf.clone())
                        .into(),
                ],
                builtin_state,
            )?,
            Obj::Pow(p) => {
                let exponent_in_n: AtomicFact = self
                    .new_in_fact(p.exponent.as_ref().clone(), n_obj.clone(), lf.clone())
                    .into();
                let base_in_z: AtomicFact = self
                    .new_in_fact(p.base.as_ref().clone(), z_obj.clone(), lf.clone())
                    .into();
                let base_in_n_pos: AtomicFact = self
                    .new_in_fact(p.base.as_ref().clone(), n_pos_obj.clone(), lf.clone())
                    .into();
                let premise_result = self.try_verify_builtin_rule_premise_alternatives(
                    vec![
                        vec![base_in_z, exponent_in_n.clone()],
                        vec![base_in_n_pos, exponent_in_n],
                    ],
                    lf.clone(),
                    builtin_state,
                )?;
                premise_result.map(|premise_result| vec![premise_result])
            }
            Obj::Abs(a) => self.verify_builtin_rule_premises(
                &[self.new_in_fact(a.arg.as_ref().clone(), z_obj, lf).into()],
                builtin_state,
            )?,
            _ => None,
        };

        let Some(subgoals) = subgoals else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        // Integer closure is a specialized recursive certificate: the target
        // syntax fixes the operator, while the two retained children prove
        // the operands are integers. Example: `a, b $in Z` proves
        // `a % b $in Z` after `%` well-definedness has checked `b != 0`.
        let closure_rule = match &in_fact.element {
            Obj::Add(_) => Some(IntegerMembershipClosureBuiltinRule::Add),
            Obj::Sub(_) => Some(IntegerMembershipClosureBuiltinRule::Sub),
            Obj::Mul(_) => Some(IntegerMembershipClosureBuiltinRule::Mul),
            Obj::Mod(_) => Some(IntegerMembershipClosureBuiltinRule::Mod),
            Obj::Pow(_) => Some(IntegerMembershipClosureBuiltinRule::PowNat),
            _ => None,
        };
        if let Some(rule) = closure_rule {
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "Z closure: binary integer arithmetic".to_string(),
                    BuiltinRuleEvidence::IntegerMembershipClosure(rule),
                    subgoals,
                )
                .into(),
            );
        }

        Ok(
            (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "Z closure: integer arithmetic; quot dividend in Z and divisor in N+; pow base in Z or N+ and exponent in N"
                    .to_string(),
                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactArithmeticExpressionInZ),
                subgoals,
            ))
            .into(),
        )
    }

    // Builtin closure of `Q` under `+`, `-`, `*`, `/` when both operands are in `Q`. For `^`, require
    // `base` in `Q` and `exponent` in `Z` (rational base with integer exponent stays in `Q`).
    pub(super) fn verify_in_fact_arithmetic_expression_in_q(
        &mut self,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::Q,
            ));
        }
        let q_obj: Obj = StandardSet::Q.into();
        let z_obj: Obj = StandardSet::Z.into();
        let lf = in_fact.line_file.clone();

        let required = match &in_fact.element {
            Obj::Add(a) => vec![
                self.new_in_fact(a.left.as_ref().clone(), q_obj.clone(), lf.clone())
                    .into(),
                self.new_in_fact(a.right.as_ref().clone(), q_obj.clone(), lf.clone())
                    .into(),
            ],
            Obj::Sub(s) => vec![
                self.new_in_fact(s.left.as_ref().clone(), q_obj.clone(), lf.clone())
                    .into(),
                self.new_in_fact(s.right.as_ref().clone(), q_obj.clone(), lf.clone())
                    .into(),
            ],
            Obj::Mul(m) => vec![
                self.new_in_fact(m.left.as_ref().clone(), q_obj.clone(), lf.clone())
                    .into(),
                self.new_in_fact(m.right.as_ref().clone(), q_obj.clone(), lf.clone())
                    .into(),
            ],
            Obj::Div(d) => vec![
                self.new_in_fact(d.left.as_ref().clone(), q_obj.clone(), lf.clone())
                    .into(),
                self.new_in_fact(d.right.as_ref().clone(), q_obj.clone(), lf.clone())
                    .into(),
            ],
            Obj::Pow(p) => vec![
                self.new_in_fact(p.base.as_ref().clone(), q_obj.clone(), lf.clone())
                    .into(),
                self.new_in_fact(p.exponent.as_ref().clone(), z_obj, lf.clone())
                    .into(),
            ],
            Obj::Abs(a) => vec![self
                .new_in_fact(a.arg.as_ref().clone(), q_obj, lf.clone())
                .into()],
            Obj::Quot(_) => Vec::new(),
            _ => return Ok((UnknownGenericStmtResult::new()).into()),
        };

        let Some(subgoals) = self.verify_builtin_rule_premises(&required, builtin_state)? else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };

        let closure_rule = match &in_fact.element {
            Obj::Add(_) => Some(RationalMembershipClosureBuiltinRule::Add),
            Obj::Sub(_) => Some(RationalMembershipClosureBuiltinRule::Sub),
            Obj::Mul(_) => Some(RationalMembershipClosureBuiltinRule::Mul),
            Obj::Div(_) => Some(RationalMembershipClosureBuiltinRule::Div),
            Obj::Pow(_) => Some(RationalMembershipClosureBuiltinRule::Pow),
            _ => None,
        };
        if let Some(rule) = closure_rule {
            return Ok(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "Q closure: binary rational arithmetic".to_string(),
                    BuiltinRuleEvidence::RationalMembershipClosure(rule),
                    subgoals,
                )
                .into(),
            );
        }

        Ok(
            (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                in_fact.clone().into(),
                "Q closure: +-*/ operands in Q; pow base in Q and exponent in Z".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyInFactArithmeticExpressionInQ,
                ),
                subgoals,
            ))
            .into(),
        )
    }

    pub(super) fn verify_in_fact_arithmetic_expression_in_standard_negative_set(
        &mut self,
        in_fact: &InFact,
        builtin_state: &BuiltinRuleSearchState,
        target_negative_standard_set: StandardSet,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &target_negative_standard_set,
            ));
        }
        let mul = match &in_fact.element {
            Obj::Mul(mul) => mul,
            _ => return Ok((UnknownGenericStmtResult::new()).into()),
        };
        let is_literal_neg_one =
            |obj: &Obj| matches!(obj, Obj::Number(number) if number.normalized_value == "-1");
        let negated = if is_literal_neg_one(mul.left.as_ref()) {
            Some(mul.right.as_ref())
        } else if is_literal_neg_one(mul.right.as_ref()) {
            Some(mul.left.as_ref())
        } else {
            None
        };
        if let Some(negated) = negated {
            let positive_carrier = match target_negative_standard_set {
                StandardSet::ZNeg => StandardSet::NPos,
                StandardSet::QNeg => StandardSet::QPos,
                StandardSet::RNeg => StandardSet::RPos,
                _ => return Ok((UnknownGenericStmtResult::new()).into()),
            };
            let positive_membership: AtomicFact = self
                .new_in_fact(
                    negated.clone(),
                    positive_carrier.into(),
                    in_fact.line_file.clone(),
                )
                .into();
            let positive_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                &positive_membership,
                builtin_state,
            )?;
            if let Some(positive_result) = positive_result {
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        in_fact.clone().into(),
                        "negation maps a positive scalar into the matching negative carrier"
                            .to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactArithmeticExpressionInStandardNegativeSet01),
                        vec![positive_result],
                    )
                    .into(),
                );
            }
        }
        let product_in_r_fact = self
            .new_in_fact(
                in_fact.element.clone(),
                StandardSet::R.into(),
                in_fact.line_file.clone(),
            )
            .into();
        let Some(product_in_r_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&product_in_r_fact, builtin_state)?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let Some(mut sign_subgoals) = self
            .mul_product_negative_when_factors_have_strict_opposite_sign_by_atomic_except_equality_verify(
                &mul.left,
                &mul.right,
                in_fact.line_file.clone(),
                builtin_state,
            )?
        else {
            return Ok((UnknownGenericStmtResult::new()).into());
        };
        let mut base_subgoals = vec![product_in_r_result];
        base_subgoals.append(&mut sign_subgoals);
        match target_negative_standard_set {
            StandardSet::RNeg => Ok(
                (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    in_fact.clone().into(),
                    "mul_opposite_signs_product_in_negative_reals".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactArithmeticExpressionInStandardNegativeSet02),
                    base_subgoals,
                ))
                .into(),
            ),
            StandardSet::QNeg => {
                let product_in_q_fact = self.new_in_fact(
                    in_fact.element.clone(),
                    StandardSet::Q.into(),
                    in_fact.line_file.clone(),
                )
                .into();
                let product_in_q_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                    &product_in_q_fact,
                    builtin_state,
                )?;
                if let Some(product_in_q_result) = product_in_q_result {
                    base_subgoals.push(product_in_q_result);
                    Ok(
                        (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            in_fact.clone().into(),
                            "mul_opposite_signs_product_in_negative_rationals".to_string(),
                            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactArithmeticExpressionInStandardNegativeSet03),
                            base_subgoals,
                        ))
                        .into(),
                    )
                } else {
                    Ok((UnknownGenericStmtResult::new()).into())
                }
            }
            StandardSet::ZNeg => {
                let product_in_z_fact = self.new_in_fact(
                    in_fact.element.clone(),
                    StandardSet::Z.into(),
                    in_fact.line_file.clone(),
                )
                .into();
                let product_in_z_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                    &product_in_z_fact,
                    builtin_state,
                )?;
                if let Some(product_in_z_result) = product_in_z_result {
                    base_subgoals.push(product_in_z_result);
                    Ok(
                        (SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            in_fact.clone().into(),
                            "mul_opposite_signs_product_in_negative_integers".to_string(),
                            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyInFactArithmeticExpressionInStandardNegativeSet04),
                            base_subgoals,
                        ))
                        .into(),
                    )
                } else {
                    Ok((UnknownGenericStmtResult::new()).into())
                }
            }
            _ => Ok((UnknownGenericStmtResult::new()).into()),
        }
    }
}
