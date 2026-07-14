use super::*;

impl Runtime {
    pub(super) fn maybe_verify_in_fact_max_min_pair_closed_standard_set(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (left, right, set) = match (&in_fact.element, &in_fact.set) {
            (Obj::Max(m), Obj::StandardSet(s)) => (m.left.as_ref(), m.right.as_ref(), s.clone()),
            (Obj::Min(m), Obj::StandardSet(s)) => (m.left.as_ref(), m.right.as_ref(), s.clone()),
            _ => return Ok(None),
        };
        if !matches!(
            set,
            StandardSet::RPos
                | StandardSet::QPos
                | StandardSet::RNeg
                | StandardSet::QNeg
                | StandardSet::ZNeg
                | StandardSet::N
                | StandardSet::NPos
        ) {
            return Ok(None);
        }
        let reason = format!("max/min: both operands in {}", set);
        let set_obj: Obj = set.into();
        let lf = in_fact.line_file.clone();
        for operand in [left, right] {
            let f: AtomicFact = InFact::new(operand.clone(), set_obj.clone(), lf.clone()).into();
            if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                &f,
                verify_state,
            )? {
                return Ok(Some((StmtUnknown::new()).into()));
            }
        }
        Ok(Some(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            reason.as_str(),
        )))
    }

    // Finite `sum` / `product` over a closed integer range: if the object is well-defined, its value
    // is a real (used e.g. for `+` on real-valued operands).
    pub(super) fn verify_in_fact_sum_or_product_in_r(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
        reason: &str,
    ) -> Result<StmtResult, RuntimeError> {
        if self
            .verify_obj_well_defined_and_store_cache(&in_fact.element, verify_state)
            .is_ok()
        {
            Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact, reason,
            ))
        } else {
            Ok((StmtUnknown::new()).into())
        }
    }

    pub(super) fn iterated_op_func_ret_set(&self, func: &Obj) -> Option<Obj> {
        match func {
            Obj::AnonymousFn(anon) => Some((*anon.body.ret_set).clone()),
            Obj::FnObj(fn_obj) if fn_obj.body.is_empty() => match fn_obj.head.as_ref() {
                FnObjHead::AnonymousFnLiteral(anon) => Some((*anon.body.ret_set).clone()),
                _ => {
                    let function_name_obj: Obj = (*fn_obj.head).clone().into();
                    self.get_object_in_fn_set_or_restrict(&function_name_obj)
                        .map(|fn_set_body| (*fn_set_body.ret_set).clone())
                }
            },
            _ => self
                .get_object_in_fn_set_or_restrict(func)
                .map(|fn_set_body| (*fn_set_body.ret_set).clone()),
        }
    }

    // Finite-set sum: the return set of the summand controls the numeric set of the sum.
    // Example: `finite_set_sum({1, 2}, fn(x Z) Z {x}) $in Z`; for `N_pos`, the domain must be nonempty.
    pub(super) fn verify_in_fact_finite_set_sum_by_iterand_ret_set(
        &mut self,
        in_fact: &InFact,
        sum: &SumOfFiniteSet,
        target_set: StandardSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if self
            .verify_obj_well_defined_and_store_cache(&in_fact.element, verify_state)
            .is_err()
        {
            return Ok((StmtUnknown::new()).into());
        }
        let Some(ret_set) = self.iterated_op_func_ret_set(sum.func.as_ref()) else {
            return Ok((StmtUnknown::new()).into());
        };
        let Obj::StandardSet(ret_standard_set) = ret_set else {
            return Ok((StmtUnknown::new()).into());
        };
        if matches!(&target_set, StandardSet::NPos) {
            if !matches!(&ret_standard_set, StandardSet::NPos) {
                return Ok((StmtUnknown::new()).into());
            }
            let nonempty_fact: AtomicFact =
                IsNonemptySetFact::new((*sum.set).clone(), in_fact.line_file.clone()).into();
            let nonempty_result = self.verify_non_equational_known_then_builtin_rules_only(
                &nonempty_fact,
                verify_state,
            )?;
            if !nonempty_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "finite_set_sum: positive summand over a nonempty finite set",
            ));
        }
        if !Self::standard_set_is_subset_eq(&ret_standard_set, &target_set) {
            return Ok((StmtUnknown::new()).into());
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
    // Example: `finite_set_product({1, 2}, fn(x Z) Z {x}) $in Z`; for `N_pos`, the empty product is `1`.
    pub(super) fn verify_in_fact_finite_set_product_by_iterand_ret_set(
        &mut self,
        in_fact: &InFact,
        product: &ProductOfFiniteSet,
        target_set: StandardSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if self
            .verify_obj_well_defined_and_store_cache(&in_fact.element, verify_state)
            .is_err()
        {
            return Ok((StmtUnknown::new()).into());
        }
        let Some(ret_set) = self.iterated_op_func_ret_set(product.func.as_ref()) else {
            return Ok((StmtUnknown::new()).into());
        };
        let Obj::StandardSet(ret_standard_set) = ret_set else {
            return Ok((StmtUnknown::new()).into());
        };
        if matches!(&target_set, StandardSet::NPos) {
            if !matches!(&ret_standard_set, StandardSet::NPos) {
                return Ok((StmtUnknown::new()).into());
            }
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "finite_set_product: positive factors give a positive finite product",
            ));
        }
        if !Self::standard_set_is_subset_eq(&ret_standard_set, &target_set) {
            return Ok((StmtUnknown::new()).into());
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

    // `sum(start, end, f)` / `product(start, end, f)` in `Z` when the iterand's declared return
    // set is `Z` or `N_pos` (positive naturals are integers) and the whole iterated object is
    // well-defined on the integer interval.
    // Example: `sum(1, n, fn(x Z) Z {x}) $in Z`, `product(1, a, fn(x N_pos) N_pos {x}) $in Z`.
    pub(super) fn verify_in_fact_sum_or_product_in_z_by_iterand_ret_set(
        &mut self,
        in_fact: &InFact,
        func: &Obj,
        verify_state: &VerifyState,
        op: &str,
    ) -> Result<StmtResult, RuntimeError> {
        if self
            .verify_obj_well_defined_and_store_cache(&in_fact.element, verify_state)
            .is_err()
        {
            return Ok((StmtUnknown::new()).into());
        }
        let Some(ret_set) = self.iterated_op_func_ret_set(func) else {
            return Ok((StmtUnknown::new()).into());
        };
        let z_obj: Obj = StandardSet::Z.into();
        let n_pos_obj: Obj = StandardSet::NPos.into();
        let reason = if verify_equality_by_they_are_the_same(&ret_set, &z_obj) {
            format!("{op}: iterand return set is Z")
        } else if verify_equality_by_they_are_the_same(&ret_set, &n_pos_obj) {
            format!("{op}: iterand return set is N_pos (subset of Z)")
        } else {
            return Ok((StmtUnknown::new()).into());
        };
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            reason.as_str(),
        ))
    }

    // `sum(start, end, f)` / `product(start, end, f)` in `Q` when the iterand's declared return
    // set is `Q` and the whole iterated object is well-defined on the integer interval.
    pub(super) fn verify_in_fact_sum_or_product_in_q_by_iterand_ret_set(
        &mut self,
        in_fact: &InFact,
        func: &Obj,
        verify_state: &VerifyState,
        op: &str,
    ) -> Result<StmtResult, RuntimeError> {
        if self
            .verify_obj_well_defined_and_store_cache(&in_fact.element, verify_state)
            .is_err()
        {
            return Ok((StmtUnknown::new()).into());
        }
        let Some(ret_set) = self.iterated_op_func_ret_set(func) else {
            return Ok((StmtUnknown::new()).into());
        };
        let q_obj: Obj = StandardSet::Q.into();
        if !verify_equality_by_they_are_the_same(&ret_set, &q_obj) {
            return Ok((StmtUnknown::new()).into());
        }
        let reason = format!("{op}: iterand return set is Q");
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            reason.as_str(),
        ))
    }

    // `sum(start, end, f)` / `product(start, end, f)` in `N_pos` when the iterand's declared
    // return set is `N_pos` and the whole iterated object is well-defined on the integer interval.
    // Example: `product(1, a, fn(x N_pos) N_pos {x}) $in N_pos`.
    pub(super) fn verify_in_fact_sum_or_product_in_n_pos_by_iterand_ret_set(
        &mut self,
        in_fact: &InFact,
        func: &Obj,
        verify_state: &VerifyState,
        op: &str,
    ) -> Result<StmtResult, RuntimeError> {
        if self
            .verify_obj_well_defined_and_store_cache(&in_fact.element, verify_state)
            .is_err()
        {
            return Ok((StmtUnknown::new()).into());
        }
        let Some(ret_set) = self.iterated_op_func_ret_set(func) else {
            return Ok((StmtUnknown::new()).into());
        };
        let n_pos_obj: Obj = StandardSet::NPos.into();
        if !verify_equality_by_they_are_the_same(&ret_set, &n_pos_obj) {
            return Ok((StmtUnknown::new()).into());
        }
        let reason = format!("{op}: iterand return set is N_pos");
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            reason.as_str(),
        ))
    }

    /// `f(args) $in S` when the head's declared return set is `S`, or a standard numeric
    /// subset of `S`, and the application is well-defined in the current environment.
    /// This also covers function-valued returns, e.g. `seq_add_R(a, b) $in fn(k N_pos) R`.
    /// Example: if `floor fn(x R) Z`, then `floor(x) $in R` because `Z subset R`.
    pub(super) fn verify_in_fact_fn_application_in_typed_return_set(
        &mut self,
        fn_obj: &FnObj,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let typed_ret = match fn_obj.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(a) => (*a.body.ret_set).clone(),
            _ => {
                let head_obj: Obj = (*fn_obj.head.clone()).into();
                let Some(fn_set) = self.get_cloned_object_in_fn_set(&head_obj) else {
                    return Ok((StmtUnknown::new()).into());
                };
                (*fn_set.ret_set).clone()
            }
        };
        let target = &in_fact.set;
        let ret_matches = self
            .verify_objs_are_equal_known_only(target, &typed_ret, in_fact.line_file.clone())
            .is_true();
        let ret_matches_alpha_renamed_fn_set =
            if let (Obj::FnSet(typed_fn_set), Obj::FnSet(target_fn_set)) = (&typed_ret, target) {
                let flat_typed =
                    ParamGroupWithSet::collect_param_names(&typed_fn_set.body.params_def_with_set);
                let flat_target =
                    ParamGroupWithSet::collect_param_names(&target_fn_set.body.params_def_with_set);
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
                Self::standard_set_is_subset_eq(ret_set, target_set)
            }
            _ => false,
        };
        if !ret_matches && !ret_matches_alpha_renamed_fn_set && !ret_is_standard_subset {
            return Ok((StmtUnknown::new()).into());
        }
        if self
            .verify_obj_well_defined_and_store_cache(&Obj::FnObj(fn_obj.clone()), verify_state)
            .is_err()
        {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "fn application in declared return set or standard numeric superset (well-defined under typing)".to_string(),
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
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::N,
            ));
        }
        let n: Obj = StandardSet::N.into();
        let lf = in_fact.line_file.clone();
        let f_left: AtomicFact =
            InFact::new(add.left.as_ref().clone(), n.clone(), lf.clone()).into();
        let f_right: AtomicFact = InFact::new(add.right.as_ref().clone(), n, lf.clone()).into();
        let r_left =
            self.verify_non_equational_known_then_builtin_rules_only(&f_left, verify_state)?;
        if !r_left.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        let r_right =
            self.verify_non_equational_known_then_builtin_rules_only(&f_right, verify_state)?;
        if !r_right.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "N: a + b from a in N and b in N".to_string(),
                vec![r_left, r_right],
            )
            .into(),
        )
    }

    // Integer subtraction stays in `N` when the result is nonnegative.
    // Example: `forall n N_pos: n - 1 $in N`, since `n, 1 $in Z` and `1 <= n`.
    pub(super) fn verify_in_fact_sub_in_n_from_integer_terms_and_bound(
        &mut self,
        in_fact: &InFact,
        sub: &Sub,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::N,
            ));
        }

        let lf = in_fact.line_file.clone();
        let z: Obj = StandardSet::Z.into();
        let left_in_z: AtomicFact =
            InFact::new(sub.left.as_ref().clone(), z.clone(), lf.clone()).into();
        let right_in_z: AtomicFact = InFact::new(sub.right.as_ref().clone(), z, lf.clone()).into();
        let right_le_left: AtomicFact = LessEqualFact::new(
            sub.right.as_ref().clone(),
            sub.left.as_ref().clone(),
            lf.clone(),
        )
        .into();

        let left_result =
            self.verify_non_equational_known_then_builtin_rules_only(&left_in_z, verify_state)?;
        if !left_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        let right_result =
            self.verify_non_equational_known_then_builtin_rules_only(&right_in_z, verify_state)?;
        if !right_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        let bound_result =
            self.verify_non_equational_known_then_builtin_rules_only(&right_le_left, verify_state)?;
        if bound_result.is_true() {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "N: a - b from a,b in Z and b <= a".to_string(),
                    vec![left_result, right_result, bound_result],
                )
                .into(),
            );
        }

        let zero: Obj = Number::new("0".to_string()).into();
        let elem = in_fact.element.clone();
        let order_facts: [AtomicFact; 4] = [
            GreaterEqualFact::new(elem.clone(), zero.clone(), lf.clone()).into(),
            LessEqualFact::new(zero.clone(), elem.clone(), lf.clone()).into(),
            GreaterFact::new(elem.clone(), zero.clone(), lf.clone()).into(),
            LessFact::new(zero, elem, lf).into(),
        ];
        for order_fact in order_facts.iter() {
            let order_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(order_fact)?;
            if order_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        "N: a - b from a,b in Z and known nonnegative difference".to_string(),
                        vec![left_result, right_result, order_result],
                    )
                    .into(),
                );
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    // `a * b $in N` when `a $in N` and `b $in N` (closure under multiplication).
    // Example: `forall a, b N: a * b $in N`.
    pub(super) fn verify_in_fact_mul_in_n_from_factors_in_n(
        &mut self,
        in_fact: &InFact,
        mul: &Mul,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::N,
            ));
        }
        let n: Obj = StandardSet::N.into();
        let lf = in_fact.line_file.clone();
        let f_left: AtomicFact =
            InFact::new(mul.left.as_ref().clone(), n.clone(), lf.clone()).into();
        let f_right: AtomicFact = InFact::new(mul.right.as_ref().clone(), n, lf.clone()).into();
        let r_left =
            self.verify_non_equational_known_then_builtin_rules_only(&f_left, verify_state)?;
        if !r_left.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        let r_right =
            self.verify_non_equational_known_then_builtin_rules_only(&f_right, verify_state)?;
        if !r_right.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "N: a * b from a in N and b in N".to_string(),
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
        verify_state: &VerifyState,
        base_set: StandardSet,
        reason: &str,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &base_set,
            ));
        }
        let lf = in_fact.line_file.clone();
        let base_in_target: AtomicFact =
            InFact::new(pow.base.as_ref().clone(), base_set.into(), lf.clone()).into();
        let exponent_in_n: AtomicFact = InFact::new(
            pow.exponent.as_ref().clone(),
            StandardSet::N.into(),
            lf.clone(),
        )
        .into();

        let base_result = self
            .verify_non_equational_known_then_builtin_rules_only(&base_in_target, verify_state)?;
        if !base_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        let exponent_result =
            self.verify_non_equational_known_then_builtin_rules_only(&exponent_in_n, verify_state)?;
        if !exponent_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                reason.to_string(),
                vec![base_result, exponent_result],
            )
            .into(),
        )
    }

    // Positive real bases raised to real exponents are positive reals.
    // Example: `forall a R_pos, x R: a^x $in R_pos`.
    pub(super) fn verify_in_fact_pow_in_r_pos_from_positive_base_real_exponent(
        &mut self,
        in_fact: &InFact,
        pow: &Pow,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let lf = in_fact.line_file.clone();
        let zero: Obj = Number::new("0".to_string()).into();
        let base_positive: AtomicFact =
            LessFact::new(zero, pow.base.as_ref().clone(), lf.clone()).into();
        let exponent_in_r: AtomicFact =
            InFact::new(pow.exponent.as_ref().clone(), StandardSet::R.into(), lf).into();

        let base_result =
            self.verify_non_equational_known_then_builtin_rules_only(&base_positive, verify_state)?;
        if !base_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        let exponent_result =
            self.verify_non_equational_known_then_builtin_rules_only(&exponent_in_r, verify_state)?;
        if !exponent_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "R_pos: a^x from 0 < a and x in R".to_string(),
                vec![base_result, exponent_result],
            )
            .into(),
        )
    }

    // `a + b $in N_pos` when both summands are in `N_pos`, or one summand is in
    // `N_pos` and the other is in `N`.
    // Example: `forall a, b N_pos: a + b $in N_pos`.
    pub(super) fn verify_in_fact_add_in_n_pos_from_n_pos_and_n(
        &mut self,
        in_fact: &InFact,
        add: &Add,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
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

        let left_n_pos: AtomicFact =
            InFact::new(add.left.as_ref().clone(), n_pos.clone(), lf.clone()).into();
        let right_n_pos_for_pair: AtomicFact =
            InFact::new(add.right.as_ref().clone(), n_pos.clone(), lf.clone()).into();
        let r_left_n_pos_for_pair =
            self.verify_non_equational_known_then_builtin_rules_only(&left_n_pos, verify_state)?;
        if r_left_n_pos_for_pair.is_true() {
            let r_right_n_pos_for_pair = self.verify_non_equational_known_then_builtin_rules_only(
                &right_n_pos_for_pair,
                verify_state,
            )?;
            if r_right_n_pos_for_pair.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        "N_pos: a + b from a in N_pos and b in N_pos".to_string(),
                        vec![r_left_n_pos_for_pair, r_right_n_pos_for_pair],
                    )
                    .into(),
                );
            }
        }

        let right_n: AtomicFact =
            InFact::new(add.right.as_ref().clone(), n.clone(), lf.clone()).into();
        let r_left_n_pos =
            self.verify_non_equational_known_then_builtin_rules_only(&left_n_pos, verify_state)?;
        if r_left_n_pos.is_true() {
            let r_right_n =
                self.verify_non_equational_known_then_builtin_rules_only(&right_n, verify_state)?;
            if r_right_n.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        "N_pos: a + b from a in N_pos and b in N".to_string(),
                        vec![r_left_n_pos, r_right_n],
                    )
                    .into(),
                );
            }
        }

        let left_n: AtomicFact =
            InFact::new(add.left.as_ref().clone(), n.clone(), lf.clone()).into();
        let right_n_pos: AtomicFact =
            InFact::new(add.right.as_ref().clone(), n_pos, lf.clone()).into();
        let r_left_n =
            self.verify_non_equational_known_then_builtin_rules_only(&left_n, verify_state)?;
        if !r_left_n.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        let r_right_n_pos =
            self.verify_non_equational_known_then_builtin_rules_only(&right_n_pos, verify_state)?;
        if !r_right_n_pos.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "N_pos: a + b from a in N and b in N_pos".to_string(),
                vec![r_left_n, r_right_n_pos],
            )
            .into(),
        )
    }

    // `a * b $in N_pos` when `a $in N_pos` and `b $in N_pos` (positive naturals are closed under multiplication).
    // Example: `forall a, b N_pos: a * b $in N_pos`.
    pub(super) fn verify_in_fact_mul_in_n_pos_from_factors_in_n_pos(
        &mut self,
        in_fact: &InFact,
        mul: &Mul,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &StandardSet::NPos,
            ));
        }
        let n_pos: Obj = StandardSet::NPos.into();
        let lf = in_fact.line_file.clone();
        let f_left: AtomicFact =
            InFact::new(mul.left.as_ref().clone(), n_pos.clone(), lf.clone()).into();
        let f_right: AtomicFact = InFact::new(mul.right.as_ref().clone(), n_pos, lf.clone()).into();
        let r_left =
            self.verify_non_equational_known_then_builtin_rules_only(&f_left, verify_state)?;
        if !r_left.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        let r_right =
            self.verify_non_equational_known_then_builtin_rules_only(&f_right, verify_state)?;
        if !r_right.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "N_pos: a * b from a in N_pos and b in N_pos".to_string(),
                vec![r_left, r_right],
            )
            .into(),
        )
    }

    // `N_pos` = positive integers: from `0 < x` and (`x $in Z` or `x $in N`).
    // Also proves a nonzero natural is positive.
    // Example: `forall n N: n != 0 =>: n $in N_pos`.
    pub(super) fn verify_in_fact_n_pos_by_zero_less_and_in_z_or_n(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let in_n: AtomicFact = InFact::new(elem.clone(), StandardSet::N.into(), lf.clone()).into();
        if self
            .verify_non_equational_known_then_builtin_rules_only(&in_n, verify_state)?
            .is_true()
        {
            let zero: Obj = Number::new("0".to_string()).into();
            let nonzero: AtomicFact = NotEqualFact::new(elem.clone(), zero, lf.clone()).into();
            if self
                .verify_non_equational_atomic_fact_with_known_atomic_facts(&nonzero)?
                .is_true()
            {
                return Ok(number_in_set_verified_by_builtin_rules_result(
                    in_fact,
                    "N_pos: x in N and x != 0",
                ));
            }
        }

        let zero: Obj = Number::new("0".to_string()).into();
        let zero_lt_elem = LessFact::new(zero, elem.clone(), lf.clone()).into();
        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &zero_lt_elem,
            verify_state,
        )? {
            return Ok((StmtUnknown::new()).into());
        }

        let in_z = InFact::new(elem.clone(), StandardSet::Z.into(), lf.clone()).into();
        if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &in_z,
            verify_state,
        )? {
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "N_pos: 0 < x and x in Z",
            ));
        }

        if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &in_n,
            verify_state,
        )? {
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "N_pos: 0 < x and x in N",
            ));
        }

        Ok((StmtUnknown::new()).into())
    }

    // `Q_pos` and `R_pos` are the positive elements of their base sets.
    // Example: from `a $in Q` and `0 < a`, prove `a $in Q_pos`.
    pub(super) fn verify_in_fact_standard_positive_by_zero_less_and_base_set(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
        base_set: StandardSet,
        rule_name: &str,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let zero: Obj = Number::new("0".to_string()).into();
        let zero_lt_elem: AtomicFact = LessFact::new(zero, elem.clone(), lf.clone()).into();
        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &zero_lt_elem,
            verify_state,
        )? {
            return Ok((StmtUnknown::new()).into());
        }

        let in_base_set: AtomicFact = InFact::new(elem.clone(), base_set.into(), lf).into();
        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &in_base_set,
            verify_state,
        )? {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact, rule_name,
        ))
    }

    // `N` = nonnegative integers: from `x $in Z` and `x >= 0`; strict `x > 0` also suffices.
    // Example: after `a, b $in Z` and `b - a >= 0`, Litex verifies `b - a $in N`.
    // Also covers predecessors of positive naturals: `forall n N_pos: n - 1 $in N`.
    pub(super) fn verify_in_fact_n_by_nonnegative_integer(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();

        let in_n_pos: AtomicFact =
            InFact::new(elem.clone(), StandardSet::NPos.into(), lf.clone()).into();
        if self
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&in_n_pos)?
            .is_true()
        {
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "N: x in N_pos",
            ));
        }

        let in_z: AtomicFact = InFact::new(elem.clone(), StandardSet::Z.into(), lf.clone()).into();
        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &in_z,
            verify_state,
        )? {
            return Ok((StmtUnknown::new()).into());
        }

        let zero: Obj = Number::new("0".to_string()).into();
        let order_facts: [AtomicFact; 4] = [
            GreaterEqualFact::new(elem.clone(), zero.clone(), lf.clone()).into(),
            LessEqualFact::new(zero.clone(), elem.clone(), lf.clone()).into(),
            GreaterFact::new(elem.clone(), zero.clone(), lf.clone()).into(),
            LessFact::new(zero, elem.clone(), lf).into(),
        ];
        for order_fact in order_facts.iter() {
            if self
                .verify_non_equational_atomic_fact_with_known_atomic_facts(order_fact)?
                .is_true()
            {
                return Ok(number_in_set_verified_by_builtin_rules_result(
                    in_fact,
                    "N: x in Z and x >= 0 or x > 0",
                ));
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub(super) fn verify_in_fact_closed_range_by_order_bounds(
        &mut self,
        in_fact: &InFact,
        closed_range: &ClosedRange,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        if !self.order_lower_bound_from_literals(
            elem,
            closed_range.start.as_ref(),
            &lf,
            verify_state,
        )? {
            return Ok((StmtUnknown::new()).into());
        }
        if !self.order_upper_bound_closed_from_literals(
            elem,
            closed_range.end.as_ref(),
            &lf,
            verify_state,
        )? {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            "in closed_range: a <= i and i <= b",
        ))
    }

    pub(super) fn verify_in_fact_open_range_by_order_bounds(
        &mut self,
        in_fact: &InFact,
        range: &Range,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        if !self.order_lower_bound_from_literals(elem, range.start.as_ref(), &lf, verify_state)? {
            return Ok((StmtUnknown::new()).into());
        }
        if !self.order_upper_bound_open_from_literals(
            elem,
            range.end.as_ref(),
            &lf,
            verify_state,
        )? {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            "in range: a <= i and i < b",
        ))
    }

    pub(super) fn verify_in_fact_interval_by_real_order_bounds(
        &mut self,
        in_fact: &InFact,
        interval: &IntervalObj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let mut step_results = Vec::new();

        // Real interval membership requires a real element and the endpoint inequalities.
        // Example: `x $in '(a, b]` follows from `x $in R`, `a < x`, and `x <= b`.
        let in_r: AtomicFact = InFact::new(elem.clone(), StandardSet::R.into(), lf.clone()).into();
        let in_r_result =
            self.verify_non_equational_known_then_builtin_rules_only(&in_r, verify_state)?;
        if !in_r_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(in_r_result);

        let lower: AtomicFact = if interval.left_closed() {
            LessEqualFact::new(interval.start().clone(), elem.clone(), lf.clone()).into()
        } else {
            LessFact::new(interval.start().clone(), elem.clone(), lf.clone()).into()
        };
        let lower_result =
            self.verify_non_equational_known_then_builtin_rules_only(&lower, verify_state)?;
        if !lower_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(lower_result);

        let upper: AtomicFact = if interval.right_closed() {
            LessEqualFact::new(elem.clone(), interval.end().clone(), lf.clone()).into()
        } else {
            LessFact::new(elem.clone(), interval.end().clone(), lf.clone()).into()
        };
        let upper_result =
            self.verify_non_equational_known_then_builtin_rules_only(&upper, verify_state)?;
        if !upper_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(upper_result);

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "in real interval: x in R and endpoint bounds".to_string(),
                step_results,
            )
            .into(),
        )
    }

    pub(super) fn verify_in_fact_one_side_infinity_interval_by_real_order_bound(
        &mut self,
        in_fact: &InFact,
        interval: &OneSideInfinityIntervalObj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let mut step_results = Vec::new();

        // Half-infinite real interval membership requires a real element and the finite endpoint bound.
        // Example: `x $in '[a,)` follows from `x $in R` and `a <= x`.
        let in_r: AtomicFact = InFact::new(elem.clone(), StandardSet::R.into(), lf.clone()).into();
        let in_r_result =
            self.verify_non_equational_known_then_builtin_rules_only(&in_r, verify_state)?;
        if !in_r_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(in_r_result);

        let bound: AtomicFact = match interval {
            OneSideInfinityIntervalObj::LeftOpen(_) => {
                LessFact::new(interval.start().clone(), elem.clone(), lf.clone()).into()
            }
            OneSideInfinityIntervalObj::LeftClosed(_) => {
                LessEqualFact::new(interval.start().clone(), elem.clone(), lf.clone()).into()
            }
            OneSideInfinityIntervalObj::RightOpen(_) => {
                LessFact::new(elem.clone(), interval.start().clone(), lf.clone()).into()
            }
            OneSideInfinityIntervalObj::RightClosed(_) => {
                LessEqualFact::new(elem.clone(), interval.start().clone(), lf.clone()).into()
            }
        };
        let bound_result =
            self.verify_non_equational_known_then_builtin_rules_only(&bound, verify_state)?;
        if !bound_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(bound_result);

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "in half-infinite real interval: x in R and endpoint bound".to_string(),
                step_results,
            )
            .into(),
        )
    }

    // When `x $in Z` and endpoints are integer literals: `lo <= x` iff `lo - 1 < x` (discrete lower).
    // Example: dom `1 < i` with `i $in Z` proves the lower side of `i $in range(2, 6)` / `closed_range(2, 5)`.
    pub(super) fn order_lower_bound_from_literals(
        &mut self,
        elem: &Obj,
        lower: &Obj,
        lf: &LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let weak: AtomicFact = LessEqualFact::new(lower.clone(), elem.clone(), lf.clone()).into();
        if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &weak,
            verify_state,
        )? {
            return Ok(true);
        }
        let in_z: AtomicFact = InFact::new(elem.clone(), StandardSet::Z.into(), lf.clone()).into();
        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &in_z,
            verify_state,
        )? {
            return Ok(false);
        }
        let Some(lower_num) = self.resolve_obj_to_number_resolved(lower) else {
            return Ok(false);
        };
        if !is_integer_after_simplification(&lower_num) {
            return Ok(false);
        }
        let pred = Obj::Sub(Sub::new(lower.clone(), Number::new("1".to_string()).into()));
        let Some(pred_n) = pred.evaluate_to_normalized_decimal_number() else {
            return Ok(false);
        };
        let strict: AtomicFact = LessFact::new(pred_n.into(), elem.clone(), lf.clone()).into();
        self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &strict,
            verify_state,
        )
    }

    // When `x $in Z` and `hi` is an integer literal: `x < hi` iff `x <= hi - 1`.
    // Example: `i <= 5` and `i $in Z` gives the upper side of `i $in range(2, 6)`.
    pub(super) fn order_upper_bound_open_from_literals(
        &mut self,
        elem: &Obj,
        upper: &Obj,
        lf: &LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let strict: AtomicFact = LessFact::new(elem.clone(), upper.clone(), lf.clone()).into();
        if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &strict,
            verify_state,
        )? {
            return Ok(true);
        }
        let in_z: AtomicFact = InFact::new(elem.clone(), StandardSet::Z.into(), lf.clone()).into();
        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &in_z,
            verify_state,
        )? {
            return Ok(false);
        }
        let Some(upper_num) = self.resolve_obj_to_number_resolved(upper) else {
            return Ok(false);
        };
        if !is_integer_after_simplification(&upper_num) {
            return Ok(false);
        }
        let upper_minus_one =
            Obj::Sub(Sub::new(upper.clone(), Number::new("1".to_string()).into()));
        let Some(um) = upper_minus_one.evaluate_to_normalized_decimal_number() else {
            return Ok(false);
        };
        let weak: AtomicFact = LessEqualFact::new(elem.clone(), um.into(), lf.clone()).into();
        self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(&weak, verify_state)
    }

    // When `x $in Z` and `hi` is an integer literal: `x <= hi` iff `x < hi + 1`.
    pub(super) fn order_upper_bound_closed_from_literals(
        &mut self,
        elem: &Obj,
        upper: &Obj,
        lf: &LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let weak: AtomicFact = LessEqualFact::new(elem.clone(), upper.clone(), lf.clone()).into();
        if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &weak,
            verify_state,
        )? {
            return Ok(true);
        }
        let in_z: AtomicFact = InFact::new(elem.clone(), StandardSet::Z.into(), lf.clone()).into();
        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &in_z,
            verify_state,
        )? {
            return Ok(false);
        }
        let Some(upper_num) = self.resolve_obj_to_number_resolved(upper) else {
            return Ok(false);
        };
        if !is_integer_after_simplification(&upper_num) {
            return Ok(false);
        }
        let hi_plus_one = Obj::Add(Add::new(upper.clone(), Number::new("1".to_string()).into()));
        let Some(hp) = hi_plus_one.evaluate_to_normalized_decimal_number() else {
            return Ok(false);
        };
        let strict: AtomicFact = LessFact::new(elem.clone(), hp.into(), lf.clone()).into();
        self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &strict,
            verify_state,
        )
    }

    // Builtin closure of `Z` under `+`, `-`, `*`, `mod`, and natural-number powers.
    // Example: `forall a Z, k N: a^k $in Z`.
    pub(super) fn verify_in_fact_arithmetic_expression_in_z(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
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

        let mut require_in_z = |o: &Obj| -> Result<bool, RuntimeError> {
            let f = InFact::new(o.clone(), z_obj.clone(), lf.clone()).into();
            self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(&f, verify_state)
        };

        let ok = match &in_fact.element {
            Obj::Add(a) => require_in_z(&a.left)? && require_in_z(&a.right)?,
            Obj::Sub(s) => require_in_z(&s.left)? && require_in_z(&s.right)?,
            Obj::Mul(m) => require_in_z(&m.left)? && require_in_z(&m.right)?,
            Obj::Mod(m) => require_in_z(&m.left)? && require_in_z(&m.right)?,
            Obj::Pow(p) => {
                let exponent_in_n: AtomicFact =
                    InFact::new(p.exponent.as_ref().clone(), n_obj.clone(), lf.clone()).into();
                let base_z_and_natural_exponent = require_in_z(&p.base)?
                    && self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                        &exponent_in_n,
                        verify_state,
                    )?;
                if base_z_and_natural_exponent {
                    true
                } else {
                    let base_in_n_pos: AtomicFact =
                        InFact::new(p.base.as_ref().clone(), n_pos_obj.clone(), lf.clone()).into();
                    let exponent_in_n: AtomicFact =
                        InFact::new(p.exponent.as_ref().clone(), n_obj.clone(), lf.clone()).into();
                    self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                        &base_in_n_pos,
                        verify_state,
                    )? && self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                        &exponent_in_n,
                        verify_state,
                    )?
                }
            }
            Obj::Max(m) => require_in_z(&m.left)? && require_in_z(&m.right)?,
            Obj::Min(m) => require_in_z(&m.left)? && require_in_z(&m.right)?,
            Obj::Abs(a) => require_in_z(a.arg.as_ref())?,
            _ => false,
        };

        if !ok {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "Z closure: arithmetic operands in Z; pow base in Z and exponent in N, or base in N_pos and exponent in N"
                    .to_string(),
                Vec::new(),
            ))
            .into(),
        )
    }

    // Builtin closure of `Q` under `+`, `-`, `*`, `/` when both operands are in `Q`. For `^`, require
    // `base` in `Q` and `exponent` in `Z` (rational base with integer exponent stays in `Q`).
    pub(super) fn verify_in_fact_arithmetic_expression_in_q(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
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

        let in_q = |slf: &mut Self, o: &Obj| -> Result<bool, RuntimeError> {
            let f = InFact::new(o.clone(), q_obj.clone(), lf.clone()).into();
            slf.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(&f, verify_state)
        };
        let in_z = |slf: &mut Self, o: &Obj| -> Result<bool, RuntimeError> {
            let f = InFact::new(o.clone(), z_obj.clone(), lf.clone()).into();
            slf.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(&f, verify_state)
        };

        let ok = match &in_fact.element {
            Obj::Add(a) => in_q(self, &a.left)? && in_q(self, &a.right)?,
            Obj::Sub(s) => in_q(self, &s.left)? && in_q(self, &s.right)?,
            Obj::Mul(m) => in_q(self, &m.left)? && in_q(self, &m.right)?,
            Obj::Div(d) => in_q(self, &d.left)? && in_q(self, &d.right)?,
            Obj::Pow(p) => in_q(self, &p.base)? && in_z(self, &p.exponent)?,
            Obj::Max(m) => in_q(self, &m.left)? && in_q(self, &m.right)?,
            Obj::Min(m) => in_q(self, &m.left)? && in_q(self, &m.right)?,
            Obj::Abs(a) => in_q(self, a.arg.as_ref())?,
            _ => false,
        };

        if !ok {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "Q closure: +-*/ operands in Q; pow base in Q and exponent in Z".to_string(),
                Vec::new(),
            ))
            .into(),
        )
    }

    pub(super) fn verify_in_fact_arithmetic_expression_in_standard_negative_set(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
        target_negative_standard_set: StandardSet,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &target_negative_standard_set,
            ));
        }
        let mul = match &in_fact.element {
            Obj::Mul(mul) => mul,
            _ => return Ok((StmtUnknown::new()).into()),
        };
        let product_in_r_fact = InFact::new(
            in_fact.element.clone(),
            StandardSet::R.into(),
            in_fact.line_file.clone(),
        )
        .into();
        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
            &product_in_r_fact,
            verify_state,
        )? {
            return Ok((StmtUnknown::new()).into());
        }
        if !self
            .mul_product_negative_when_factors_have_strict_opposite_sign_by_non_equational_verify(
                &mul.left,
                &mul.right,
                in_fact.line_file.clone(),
                verify_state,
            )?
        {
            return Ok((StmtUnknown::new()).into());
        }
        match target_negative_standard_set {
            StandardSet::RNeg => Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "mul_opposite_signs_product_in_R_neg".to_string(),
                    Vec::new(),
                ))
                .into(),
            ),
            StandardSet::QNeg => {
                let product_in_q_fact = InFact::new(
                    in_fact.element.clone(),
                    StandardSet::Q.into(),
                    in_fact.line_file.clone(),
                )
                .into();
                if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                    &product_in_q_fact,
                    verify_state,
                )? {
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            in_fact.clone().into(),
                            "mul_opposite_signs_product_in_Q_neg".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            StandardSet::ZNeg => {
                let product_in_z_fact = InFact::new(
                    in_fact.element.clone(),
                    StandardSet::Z.into(),
                    in_fact.line_file.clone(),
                )
                .into();
                if self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                    &product_in_z_fact,
                    verify_state,
                )? {
                    Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            in_fact.clone().into(),
                            "mul_opposite_signs_product_in_Z_neg".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            _ => Ok((StmtUnknown::new()).into()),
        }
    }
}
