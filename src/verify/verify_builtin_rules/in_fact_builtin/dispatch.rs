use super::*;

impl Runtime {
    pub fn verify_not_in_fact_with_builtin_rules(
        &mut self,
        not_in_fact: &NotInFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Obj::StandardSet(standard_set) = &not_in_fact.set {
            if matches!(standard_set, StandardSet::Z) {
                if let Some(result) = self.verify_not_in_z_for_resolved_numeric_div(not_in_fact) {
                    return Ok(result);
                }
            }
            if !matches!(&not_in_fact.element, Obj::Number(_)) {
                if let Some(evaluated_number) =
                    not_in_fact.element.evaluate_to_normalized_decimal_number()
                {
                    return Ok(
                        builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
                            not_in_fact,
                            &evaluated_number,
                            standard_set,
                        ),
                    );
                }
                let resolved_element = self.resolve_obj(&not_in_fact.element);
                if let Obj::Number(evaluated_number) = resolved_element {
                    return Ok(
                        builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
                            not_in_fact,
                            &evaluated_number,
                            standard_set,
                        ),
                    );
                }
            }
        }
        match (&not_in_fact.element, &not_in_fact.set) {
            (Obj::Number(num), Obj::StandardSet(standard_set)) => Ok(
                builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
                    not_in_fact,
                    num,
                    standard_set,
                ),
            ),
            (_, Obj::ListSet(list_set)) => self
                .verify_not_in_fact_by_not_equal_to_every_element_in_list_set(
                    not_in_fact,
                    list_set,
                    _verify_state,
                ),
            (_, Obj::Intersect(intersect)) => self
                .verify_not_in_fact_not_in_intersect_by_non_member_of_either_side(
                    not_in_fact,
                    intersect,
                    _verify_state,
                ),
            _ => Ok((StmtUnknown::new()).into()),
        }
    }

    pub fn verify_in_fact_with_builtin_rules(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Obj::StandardSet(standard_set) = &in_fact.set {
            if !matches!(&in_fact.element, Obj::Number(_)) {
                if let Some(evaluated_number) =
                    in_fact.element.evaluate_to_normalized_decimal_number()
                {
                    let evaluation_membership_result =
                        builtin_in_fact_result_for_evaluated_number_in_standard_set(
                            in_fact,
                            &evaluated_number,
                            standard_set,
                        );
                    if evaluation_membership_result.is_true() {
                        return Ok(evaluation_membership_result);
                    }
                }
                let resolved_element = self.resolve_obj(&in_fact.element);
                if let Obj::Number(evaluated_number) = resolved_element {
                    let resolved_membership_result =
                        builtin_in_fact_result_for_evaluated_number_in_standard_set(
                            in_fact,
                            &evaluated_number,
                            standard_set,
                        );
                    if resolved_membership_result.is_true() {
                        return Ok(resolved_membership_result);
                    }
                }
            }
        }
        if let Some(result) =
            self.maybe_verify_in_fact_finite_set_extremum(in_fact, verify_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self.maybe_verify_in_fact_builtin_operator_signature(in_fact) {
            return Ok(result);
        }
        if let Some(result) =
            self.maybe_verify_in_fact_in_unfolded_user_defined_set(in_fact, verify_state)?
        {
            return Ok(result);
        }
        if !matches!(&in_fact.set, Obj::Cart(_)) {
            if let Some(result) = self.try_verify_in_fact_by_symbolic_cart(in_fact, verify_state)? {
                return Ok(result);
            }
        }
        match (&in_fact.element, &in_fact.set) {
            (_, Obj::Union(union)) => {
                return self.verify_in_fact_in_union_by_member_of_either_side(
                    in_fact,
                    union,
                    verify_state,
                );
            }
            (_, Obj::Intersect(intersect)) => {
                return self.verify_in_fact_in_intersect_by_member_of_both_sides(
                    in_fact,
                    intersect,
                    verify_state,
                );
            }
            (_, Obj::SetMinus(set_minus)) => {
                return self.verify_in_fact_in_set_minus_by_member_and_non_member(
                    in_fact,
                    set_minus,
                    verify_state,
                );
            }
            (_, Obj::BigUnion(big_union)) => {
                return self.verify_in_fact_in_big_union_by_member_witness(
                    in_fact,
                    big_union,
                    verify_state,
                );
            }
            (_, Obj::Replacement(replacement)) => {
                return self.verify_in_fact_in_replacement_by_relation_witness(
                    in_fact,
                    replacement,
                    verify_state,
                );
            }
            (_, Obj::StructObj(struct_obj)) => {
                return self.verify_in_fact_by_struct_obj(in_fact, struct_obj, verify_state);
            }
            (Obj::Tuple(tuple), Obj::Cart(cart)) => {
                return self.verify_in_fact_by_left_is_tuple_right_is_cart(
                    in_fact,
                    tuple,
                    cart,
                    verify_state,
                );
            }
            (Obj::Number(num), Obj::StandardSet(standard_set)) => {
                Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                    in_fact,
                    num,
                    standard_set,
                ))
            }
            (Obj::Sum(sum), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_sum_or_product_in_n_pos_by_iterand_ret_set(
                    in_fact,
                    sum.func.as_ref(),
                    verify_state,
                    "sum",
                ),
            (Obj::Product(product), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_sum_or_product_in_n_pos_by_iterand_ret_set(
                    in_fact,
                    product.func.as_ref(),
                    verify_state,
                    "product",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::NPos,
                    verify_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::NPos,
                    verify_state,
                ),
            (Obj::Add(add), Obj::StandardSet(StandardSet::N)) => {
                self.verify_in_fact_add_in_n_from_summands_in_n(in_fact, add, verify_state)
            }
            (Obj::Sub(sub), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_sub_in_n_from_integer_terms_and_bound(in_fact, sub, verify_state),
            (Obj::Mul(mul), Obj::StandardSet(StandardSet::N)) => {
                self.verify_in_fact_mul_in_n_from_factors_in_n(in_fact, mul, verify_state)
            }
            (Obj::Pow(pow), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_pow_in_standard_set_from_base_and_natural_exponent(
                    in_fact,
                    pow,
                    verify_state,
                    StandardSet::N,
                    "N: a^k from a in N and k in N",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::N,
                    verify_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::N,
                    verify_state,
                ),
            (Obj::FiniteSetSize(finite_set_size), Obj::StandardSet(StandardSet::N))
            | (Obj::FiniteSetSize(finite_set_size), Obj::StandardSet(StandardSet::Z))
            | (Obj::FiniteSetSize(finite_set_size), Obj::StandardSet(StandardSet::Q))
            | (Obj::FiniteSetSize(finite_set_size), Obj::StandardSet(StandardSet::R)) => self
                .verify_finite_set_size_in_standard_number_set(
                    in_fact,
                    finite_set_size,
                    verify_state,
                ),
            (Obj::FnObj(fn_obj), Obj::FnRange(fn_range)) => {
                self.verify_in_fact_fn_application_in_fn_range(in_fact, fn_obj, fn_range)
            }
            (Obj::IntegerQuotient(quotient), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_nonnegative_integer_quotient_in_n(in_fact, quotient, verify_state),
            (_, Obj::StandardSet(StandardSet::N)) => {
                self.verify_in_fact_n_by_nonnegative_integer(in_fact, verify_state)
            }
            (Obj::Add(add), Obj::StandardSet(StandardSet::NPos)) => {
                self.verify_in_fact_add_in_n_pos_from_n_pos_and_n(in_fact, add, verify_state)
            }
            (Obj::Mul(mul), Obj::StandardSet(StandardSet::NPos)) => {
                self.verify_in_fact_mul_in_n_pos_from_factors_in_n_pos(in_fact, mul, verify_state)
            }
            (Obj::Pow(pow), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_pow_in_standard_set_from_base_and_natural_exponent(
                    in_fact,
                    pow,
                    verify_state,
                    StandardSet::NPos,
                    "N_pos: a^k from a in N_pos and k in N",
                ),
            (Obj::Pow(pow), Obj::StandardSet(StandardSet::RPos)) => self
                .verify_in_fact_pow_in_r_pos_from_positive_base_real_exponent(
                    in_fact,
                    pow,
                    verify_state,
                ),
            (_, Obj::StandardSet(StandardSet::NPos)) => {
                self.verify_in_fact_n_pos_by_zero_less_and_in_z_or_n(in_fact, verify_state)
            }
            (_, Obj::StandardSet(StandardSet::QPos)) => self
                .verify_in_fact_standard_positive_by_zero_less_and_base_set(
                    in_fact,
                    verify_state,
                    StandardSet::Q,
                    "Q_pos: 0 < x and x in Q",
                ),
            (_, Obj::StandardSet(StandardSet::RPos)) => self
                .verify_in_fact_standard_positive_by_zero_less_and_base_set(
                    in_fact,
                    verify_state,
                    StandardSet::R,
                    "R_pos: 0 < x and x in R",
                ),
            (_, Obj::ClosedRange(closed_range)) => self
                .verify_in_fact_closed_range_by_order_bounds(in_fact, closed_range, verify_state),
            (_, Obj::Range(range)) => {
                self.verify_in_fact_open_range_by_order_bounds(in_fact, range, verify_state)
            }
            (_, Obj::IntervalObj(interval)) => {
                self.verify_in_fact_interval_by_real_order_bounds(in_fact, interval, verify_state)
            }
            (_, Obj::OneSideInfinityIntervalObj(interval)) => self
                .verify_in_fact_one_side_infinity_interval_by_real_order_bound(
                    in_fact,
                    interval,
                    verify_state,
                ),
            (
                Obj::Add(_)
                | Obj::Sub(_)
                | Obj::Mul(_)
                | Obj::Mod(_)
                | Obj::IntegerQuotient(_)
                | Obj::Pow(_)
                | Obj::Abs(_),
                Obj::StandardSet(StandardSet::Z),
            ) => self.verify_in_fact_arithmetic_expression_in_z(in_fact, verify_state),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Pow(_) | Obj::Abs(_),
                Obj::StandardSet(StandardSet::Q),
            ) => self.verify_in_fact_arithmetic_expression_in_q(in_fact, verify_state),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet(StandardSet::RNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::RNeg,
            ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet(StandardSet::QNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::QNeg,
            ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet(StandardSet::ZNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::ZNeg,
            ),
            (
                Obj::Add(_)
                | Obj::Sub(_)
                | Obj::Mul(_)
                | Obj::Div(_)
                | Obj::Mod(_)
                | Obj::IntegerQuotient(_)
                | Obj::Pow(_)
                | Obj::Abs(_)
                | Obj::Sqrt(_)
                | Obj::Log(_),
                Obj::StandardSet(StandardSet::R),
            ) => Ok(arithmetic_obj_in_r_verified_by_builtin_rules_result(
                in_fact,
            )),
            (Obj::Sum(_), Obj::StandardSet(StandardSet::R)) => self
                .verify_in_fact_sum_or_product_in_r(
                    in_fact,
                    verify_state,
                    "sum: well-defined on an integer range, in R",
                ),
            (Obj::Product(_), Obj::StandardSet(StandardSet::R)) => self
                .verify_in_fact_sum_or_product_in_r(
                    in_fact,
                    verify_state,
                    "product: well-defined on an integer range, in R",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::R)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::R,
                    verify_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::R)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::R,
                    verify_state,
                ),
            (Obj::Sum(sum), Obj::StandardSet(StandardSet::Z)) => self
                .verify_in_fact_sum_or_product_in_z_by_iterand_ret_set(
                    in_fact,
                    sum.func.as_ref(),
                    verify_state,
                    "sum",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::Z)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::Z,
                    verify_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::Z)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::Z,
                    verify_state,
                ),
            (Obj::Product(product), Obj::StandardSet(StandardSet::Z)) => self
                .verify_in_fact_sum_or_product_in_z_by_iterand_ret_set(
                    in_fact,
                    product.func.as_ref(),
                    verify_state,
                    "product",
                ),
            (Obj::Sum(sum), Obj::StandardSet(StandardSet::Q)) => self
                .verify_in_fact_sum_or_product_in_q_by_iterand_ret_set(
                    in_fact,
                    sum.func.as_ref(),
                    verify_state,
                    "sum",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::Q)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::Q,
                    verify_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::Q)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::Q,
                    verify_state,
                ),
            (Obj::Product(product), Obj::StandardSet(StandardSet::Q)) => self
                .verify_in_fact_sum_or_product_in_q_by_iterand_ret_set(
                    in_fact,
                    product.func.as_ref(),
                    verify_state,
                    "product",
                ),
            (Obj::ListSet(list_set), Obj::PowerSet(power_set)) => self
                .verify_in_fact_list_set_in_power_set_defines_membership(
                    in_fact,
                    list_set,
                    power_set,
                    verify_state,
                ),
            (Obj::SetBuilder(set_builder), Obj::PowerSet(power_set)) => self
                .verify_in_fact_set_builder_in_power_set_via_param_subset(
                    in_fact,
                    set_builder,
                    power_set,
                    verify_state,
                ),
            (Obj::FnRange(fn_range), Obj::PowerSet(power_set)) => self
                .verify_in_fact_fn_range_in_power_set(in_fact, fn_range, power_set, verify_state),
            (_, Obj::PowerSet(power_set)) => {
                self.verify_in_fact_in_power_set_via_subset(in_fact, power_set, verify_state)
            }
            (_, Obj::GeneralCart(general_cart)) => self
                .verify_in_fact_in_general_cart_by_defining_facts(
                    in_fact,
                    general_cart,
                    verify_state,
                ),
            (_, Obj::SetBuilder(set_builder)) => self
                .verify_in_fact_in_set_builder_by_defining_facts(
                    in_fact,
                    set_builder,
                    verify_state,
                ),
            (_, Obj::ListSet(list_set)) => self.verify_in_fact_by_equal_to_one_element_in_list_set(
                in_fact,
                list_set,
                verify_state,
            ),
            (Obj::AnonymousFn(anon), Obj::FnSet(expected_fn_set)) => self
                .verify_in_fact_anonymous_fn_signature_matches_fn_set(
                    anon,
                    expected_fn_set,
                    in_fact,
                    verify_state,
                ),
            (Obj::FnObj(fn_obj), Obj::FnSet(_)) => self
                .verify_in_fact_fn_application_in_typed_return_set(fn_obj, in_fact, verify_state),
            (element, Obj::FnSet(expected_fn_set))
                if obj_eligible_for_known_objs_in_fn_sets(element) =>
            {
                let stored_result = self.verify_in_fact_element_in_fn_set_by_stored_definition(
                    element,
                    expected_fn_set,
                    in_fact,
                )?;
                if stored_result.is_true() {
                    return Ok(stored_result);
                }
                if let Some(result) = self.verify_in_fact_element_in_fn_set_by_pointwise_values(
                    element,
                    expected_fn_set,
                    in_fact,
                    verify_state,
                )? {
                    return Ok(result);
                }
                Ok(stored_result)
            }
            (Obj::FiniteSeqListObj(list), Obj::FiniteSeqSet(fs)) => {
                let lf = in_fact.line_file.clone();
                let len_obj: Obj = Number::new(list.objs.len().to_string()).into();
                if !self
                    .verify_objs_are_equal_known_only(&len_obj, fs.n.as_ref(), lf.clone())
                    .is_true()
                {
                    return Ok((StmtUnknown::new()).into());
                }
                for o in list.objs.iter() {
                    let f: AtomicFact =
                        InFact::new((**o).clone(), (*fs.set).clone(), lf.clone()).into();
                    if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                        &f,
                        verify_state,
                    )? {
                        return Ok((StmtUnknown::new()).into());
                    }
                }
                Ok(number_in_set_verified_by_builtin_rules_result(
                    in_fact,
                    "finite_seq list: length equals n and each entry in co-domain",
                ))
            }
            // Real matrix operators preserve their symbolic matrix type.
            // Example: `A, B matrix(R, m, n)` implies `A '+ B $in matrix(R, m, n)`.
            (element, Obj::MatrixSet(expected))
                if matches!(
                    element,
                    Obj::MatrixAdd(_)
                        | Obj::MatrixSub(_)
                        | Obj::MatrixMul(_)
                        | Obj::MatrixScalarMul(_)
                        | Obj::MatrixPow(_)
                ) =>
            {
                let actual = self.real_matrix_type(element, verify_state, "operator")?;
                let real: Obj = StandardSet::R.into();
                let same_entry_set = self.verify_objs_are_equal_known_only(
                    &actual.set,
                    &expected.set,
                    in_fact.line_file.clone(),
                );
                let expected_is_real = self.verify_objs_are_equal_known_only(
                    &expected.set,
                    &real,
                    in_fact.line_file.clone(),
                );
                let same_rows = self.verify_objs_are_equal_known_only(
                    &actual.row_len,
                    &expected.row_len,
                    in_fact.line_file.clone(),
                );
                let same_cols = self.verify_objs_are_equal_known_only(
                    &actual.col_len,
                    &expected.col_len,
                    in_fact.line_file.clone(),
                );
                if same_entry_set.is_unknown()
                    || expected_is_real.is_unknown()
                    || same_rows.is_unknown()
                    || same_cols.is_unknown()
                {
                    return Ok((StmtUnknown::new()).into());
                }
                Ok(number_in_set_verified_by_builtin_rules_result(
                    in_fact,
                    "real matrix operator: result dimensions and entry set match matrix(...) type",
                ))
            }
            (Obj::MatrixListObj(list), Obj::MatrixSet(ms)) => {
                let lf = in_fact.line_file.clone();
                let n_rows_obj: Obj = Number::new(list.rows.len().to_string()).into();
                if !self
                    .verify_objs_are_equal_known_only(&n_rows_obj, ms.row_len.as_ref(), lf.clone())
                    .is_true()
                {
                    return Ok((StmtUnknown::new()).into());
                }
                for row in list.rows.iter() {
                    let n_col_obj: Obj = Number::new(row.len().to_string()).into();
                    if !self
                        .verify_objs_are_equal_known_only(
                            &n_col_obj,
                            ms.col_len.as_ref(),
                            lf.clone(),
                        )
                        .is_true()
                    {
                        return Ok((StmtUnknown::new()).into());
                    }
                    for o in row.iter() {
                        let f: AtomicFact =
                            InFact::new((**o).clone(), (*ms.set).clone(), lf.clone()).into();
                        if !self.non_equational_atomic_fact_holds_by_known_then_builtin_rules_only(
                            &f,
                            verify_state,
                        )? {
                            return Ok((StmtUnknown::new()).into());
                        }
                    }
                }
                Ok(number_in_set_verified_by_builtin_rules_result(
                    in_fact,
                    "matrix literal: shape matches matrix(...) and each entry in co-domain",
                ))
            }
            (_, Obj::FiniteSeqSet(fs)) => {
                let fn_set = self.finite_seq_set_to_fn_set(fs, in_fact.line_file.clone());
                let expanded = InFact::new(
                    in_fact.element.clone(),
                    fn_set.into(),
                    in_fact.line_file.clone(),
                );
                self.verify_atomic_fact_by_known_atomic_or_builtin_only(
                    &expanded.into(),
                    verify_state,
                )
            }
            (_, Obj::SeqSet(ss)) => {
                let fn_set = self.seq_set_to_fn_set(ss, in_fact.line_file.clone());
                let expanded = InFact::new(
                    in_fact.element.clone(),
                    fn_set.into(),
                    in_fact.line_file.clone(),
                );
                self.verify_atomic_fact_by_known_atomic_or_builtin_only(
                    &expanded.into(),
                    verify_state,
                )
            }
            (_, Obj::MatrixSet(ms)) => {
                let fn_set = self.matrix_set_to_fn_set(ms, in_fact.line_file.clone());
                let expanded = InFact::new(
                    in_fact.element.clone(),
                    fn_set.into(),
                    in_fact.line_file.clone(),
                );
                self.verify_atomic_fact_by_known_atomic_or_builtin_only(
                    &expanded.into(),
                    verify_state,
                )
            }
            (_, target_set_obj) => {
                let finite_seq_literal_application_result = self
                    .verify_in_fact_finite_seq_literal_application_in_set(
                        in_fact,
                        target_set_obj,
                        verify_state,
                    )?;
                if finite_seq_literal_application_result.is_true() {
                    return Ok(finite_seq_literal_application_result);
                }
                let cart_projection_result = self
                    .verify_in_fact_obj_at_index_in_standard_set_by_cart_factor_list_set(
                        in_fact,
                        target_set_obj,
                        verify_state,
                    )?;
                if cart_projection_result.is_true() {
                    return Ok(cart_projection_result);
                }
                if let Obj::FnObj(fn_obj) = &in_fact.element {
                    let fn_try = self.verify_in_fact_fn_application_in_typed_return_set(
                        fn_obj,
                        in_fact,
                        verify_state,
                    )?;
                    if fn_try.is_true() {
                        return Ok(fn_try);
                    }
                }
                self.verify_in_fact_by_known_standard_subset_membership(in_fact, target_set_obj)
            }
        }
    }
}
