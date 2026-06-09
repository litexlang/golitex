use crate::infer::obj_eligible_for_known_objs_in_fn_sets;
use crate::prelude::*;
use crate::verify::{
    compare_normalized_number_str_to_zero, number_is_in_n, number_is_in_n_pos, number_is_in_q_neg,
    number_is_in_q_nz, number_is_in_q_pos, number_is_in_r_neg, number_is_in_r_nz,
    number_is_in_r_pos, number_is_in_z, number_is_in_z_neg, number_is_in_z_nz,
    verify_equality_by_builtin_rules::verify_equality_by_they_are_the_same,
    verify_number_in_standard_set::is_integer_after_simplification, NumberCompareResult,
    VerifyState,
};
use std::collections::HashMap;

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
            self.maybe_verify_in_fact_max_min_pair_closed_standard_set(in_fact, verify_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.maybe_verify_in_fact_in_unfolded_user_defined_set(in_fact, verify_state)?
        {
            return Ok(result);
        }
        match (&in_fact.element, &in_fact.set) {
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
                .verify_in_fact_sum_of_finite_set_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::NPos,
                    verify_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_product_of_finite_set_by_iterand_ret_set(
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
                .verify_in_fact_sum_of_finite_set_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::N,
                    verify_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_product_of_finite_set_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::N,
                    verify_state,
                ),
            (Obj::Count(count), Obj::StandardSet(StandardSet::N))
            | (Obj::Count(count), Obj::StandardSet(StandardSet::Z))
            | (Obj::Count(count), Obj::StandardSet(StandardSet::Q))
            | (Obj::Count(count), Obj::StandardSet(StandardSet::R)) => {
                self.verify_count_in_standard_number_set(in_fact, count, verify_state)
            }
            (Obj::FnObj(fn_obj), Obj::FnRange(fn_range)) => {
                self.verify_in_fact_fn_application_in_fn_range(in_fact, fn_obj, fn_range)
            }
            (Obj::FnObj(fn_obj), Obj::FnRangeOn(fn_range_on)) => self
                .verify_in_fact_fn_application_in_fn_range_on(
                    in_fact,
                    fn_obj,
                    fn_range_on,
                    verify_state,
                ),
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
                | Obj::Pow(_)
                | Obj::Max(_)
                | Obj::Min(_)
                | Obj::Abs(_),
                Obj::StandardSet(StandardSet::Z),
            ) => self.verify_in_fact_arithmetic_expression_in_z(in_fact, verify_state),
            (
                Obj::Add(_)
                | Obj::Sub(_)
                | Obj::Mul(_)
                | Obj::Div(_)
                | Obj::Pow(_)
                | Obj::Max(_)
                | Obj::Min(_)
                | Obj::Abs(_),
                Obj::StandardSet(StandardSet::Q),
            ) => self.verify_in_fact_arithmetic_expression_in_q(in_fact, verify_state),
            (
                Obj::Add(_)
                | Obj::Sub(_)
                | Obj::Mul(_)
                | Obj::Div(_)
                | Obj::Mod(_)
                | Obj::Pow(_)
                | Obj::Max(_)
                | Obj::Min(_),
                Obj::StandardSet(StandardSet::RNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::RNeg,
            ),
            (
                Obj::Add(_)
                | Obj::Sub(_)
                | Obj::Mul(_)
                | Obj::Div(_)
                | Obj::Mod(_)
                | Obj::Pow(_)
                | Obj::Max(_)
                | Obj::Min(_),
                Obj::StandardSet(StandardSet::QNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                verify_state,
                StandardSet::QNeg,
            ),
            (
                Obj::Add(_)
                | Obj::Sub(_)
                | Obj::Mul(_)
                | Obj::Div(_)
                | Obj::Mod(_)
                | Obj::Pow(_)
                | Obj::Max(_)
                | Obj::Min(_),
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
                | Obj::Pow(_)
                | Obj::Max(_)
                | Obj::Min(_)
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
                .verify_in_fact_sum_of_finite_set_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::R,
                    verify_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::R)) => self
                .verify_in_fact_product_of_finite_set_by_iterand_ret_set(
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
                .verify_in_fact_sum_of_finite_set_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::Z,
                    verify_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::Z)) => self
                .verify_in_fact_product_of_finite_set_by_iterand_ret_set(
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
                .verify_in_fact_sum_of_finite_set_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::Q,
                    verify_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::Q)) => self
                .verify_in_fact_product_of_finite_set_by_iterand_ret_set(
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
            (Obj::FnRangeOn(fn_range_on), Obj::PowerSet(power_set)) => self
                .verify_in_fact_fn_range_on_in_power_set(
                    in_fact,
                    fn_range_on,
                    power_set,
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
                self.verify_in_fact_element_in_fn_set_by_stored_definition(
                    element,
                    expected_fn_set,
                    in_fact,
                )
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

impl Runtime {
    // Function range introduction: if `f(a)` is well-defined, then it is in `fn_range(f)`.
    // Example: `have f fn(x R: x > 0) R`, `1 > 0` proves `f(1) $in fn_range(f)`.
    fn verify_in_fact_fn_application_in_fn_range(
        &mut self,
        in_fact: &InFact,
        fn_obj: &FnObj,
        fn_range: &FnRange,
    ) -> Result<StmtResult, RuntimeError> {
        let head_obj: Obj = fn_obj.head.as_ref().clone().into();
        if head_obj.to_string() != fn_range.function.to_string() {
            return Ok((StmtUnknown::new()).into());
        }
        let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
            return Ok((StmtUnknown::new()).into());
        };
        if fn_obj.body.len() != 1
            || fn_obj.body[0].len() != body.params_def_with_set.number_of_params()
        {
            return Ok((StmtUnknown::new()).into());
        }
        if self
            .verify_obj_well_defined_and_store_cache(&in_fact.element, &VerifyState::new(0, false))
            .is_err()
        {
            return Ok((StmtUnknown::new()).into());
        }
        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "fn_range membership: a well-defined function application is in the function range"
                    .to_string(),
                Vec::new(),
            )
            .into(),
        )
    }

    // Restricted function range introduction: if `x $in S` and `f(x)` is well-defined,
    // then `f(x) $in fn_range_on(f, S)`.
    // Example: `have a seq(R)` proves `a(1) $in fn_range_on(a, 1...3)`.
    fn verify_in_fact_fn_application_in_fn_range_on(
        &mut self,
        in_fact: &InFact,
        fn_obj: &FnObj,
        fn_range_on: &FnRangeOn,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let head_obj: Obj = fn_obj.head.as_ref().clone().into();
        if head_obj.to_string() != fn_range_on.function.to_string() {
            return Ok((StmtUnknown::new()).into());
        }
        let Some(body) = self.get_fn_range_on_function_body(&fn_range_on.function) else {
            return Ok((StmtUnknown::new()).into());
        };
        if body.params_def_with_set.number_of_params() != 1 {
            return Ok((StmtUnknown::new()).into());
        }
        if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 1 {
            return Ok((StmtUnknown::new()).into());
        }

        let arg = fn_obj.body[0][0].as_ref().clone();
        let arg_in_domain: AtomicFact = InFact::new(
            arg,
            fn_range_on.set.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let arg_in_domain_result =
            self.verify_non_equational_known_then_builtin_rules_only(&arg_in_domain, verify_state)?;
        if !arg_in_domain_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        if self
            .verify_obj_well_defined_and_store_cache(&in_fact.element, verify_state)
            .is_err()
        {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "fn_range_on membership: a well-defined function application with argument in the restricted domain is in the restricted function range"
                    .to_string(),
                vec![arg_in_domain_result],
            )
            .into(),
        )
    }

    // The range of `f : ... -> T` is a subset of `T`; hence it is in `power_set(U)` when `T subset U`.
    // Example: `have f fn(x S) T` proves `fn_range(f) $in power_set(T)`.
    fn verify_in_fact_fn_range_in_power_set(
        &mut self,
        in_fact: &InFact,
        fn_range: &FnRange,
        power_set: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(body) = self.get_fn_range_function_body(&fn_range.function) else {
            return Ok((StmtUnknown::new()).into());
        };
        let subset_fact: AtomicFact = SubsetFact::new(
            body.ret_set.as_ref().clone(),
            power_set.set.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let subset_result =
            self.verify_non_equational_known_then_builtin_rules_only(&subset_fact, verify_state)?;
        if !subset_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "fn_range power_set membership: function range is contained in the codomain"
                    .to_string(),
                vec![subset_result],
            )
            .into(),
        )
    }

    // The restricted range of `f : ... -> T` is a subset of `T`;
    // hence it is in `power_set(U)` when `T subset U`.
    // Example: `have a seq(R)` proves `fn_range_on(a, 1...3) $in power_set(R)`.
    fn verify_in_fact_fn_range_on_in_power_set(
        &mut self,
        in_fact: &InFact,
        fn_range_on: &FnRangeOn,
        power_set: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(body) = self.get_fn_range_on_function_body(&fn_range_on.function) else {
            return Ok((StmtUnknown::new()).into());
        };
        let subset_fact: AtomicFact = SubsetFact::new(
            body.ret_set.as_ref().clone(),
            power_set.set.as_ref().clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let subset_result =
            self.verify_non_equational_known_then_builtin_rules_only(&subset_fact, verify_state)?;
        if !subset_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "fn_range_on power_set membership: restricted function range is contained in the codomain"
                    .to_string(),
                vec![subset_result],
            )
            .into(),
        )
    }

    fn verify_in_fact_in_set_builder_by_defining_facts(
        &mut self,
        in_fact: &InFact,
        set_builder: &SetBuilder,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let mut step_results = Vec::with_capacity(set_builder.facts.len() + 1);

        let element_in_param_set: AtomicFact = InFact::new(
            in_fact.element.clone(),
            *set_builder.param_set.clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let element_in_param_set_result = self.verify_atomic_fact_by_known_atomic_or_builtin_only(
            &element_in_param_set,
            verify_state,
        )?;
        if !element_in_param_set_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(element_in_param_set_result);

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        param_to_arg_map.insert(set_builder.param.clone(), in_fact.element.clone());

        for fact_in_set_builder in set_builder.facts.iter() {
            let instantiated_fact = self
                .inst_or_and_chain_atomic_fact(
                    fact_in_set_builder,
                    &param_to_arg_map,
                    ParamObjType::SetBuilder,
                    Some(&in_fact.line_file),
                )
                .map_err(|e| {
                    let fact: Fact = in_fact.clone().into();
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(fact.into_stmt()),
                        format!(
                            "failed to instantiate set builder fact while verifying `{}`",
                            in_fact
                        ),
                        in_fact.line_file.clone(),
                        Some(e),
                        vec![],
                    )))
                })?;

            let instantiated_fact_result = self
                .verify_or_and_chain_atomic_fact_by_known_atomic_or_builtin_only(
                    &instantiated_fact,
                    verify_state,
                )?;
            if !instantiated_fact_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            step_results.push(instantiated_fact_result);
        }

        Ok(FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            "set builder membership: element is in the base set and satisfies all defining facts"
                .to_string(),
            step_results,
        )
        .into())
    }

    // Membership through a set-valued definition: if `S(a) = {x T: P(x)}`,
    // then `y $in S(a)` is checked by unfolding one layer and proving
    // `y $in T` plus `P(y)`. Example: `(3, 4) $in circle(5)`.
    fn maybe_verify_in_fact_in_unfolded_user_defined_set(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(unfolded_set) =
            self.unfold_known_fn_application_once(&in_fact.set, verify_state)?
        else {
            return Ok(None);
        };
        let Obj::SetBuilder(set_builder) = unfolded_set else {
            return Ok(None);
        };

        let unfolded_fact = InFact::new(
            in_fact.element.clone(),
            set_builder.clone().into(),
            in_fact.line_file.clone(),
        );
        let unfolded_result = self.verify_in_fact_in_set_builder_by_defining_facts(
            &unfolded_fact,
            &set_builder,
            verify_state,
        )?;
        if !unfolded_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "membership in a set-valued user-defined function: unfold one function application to a set builder".to_string(),
                vec![unfolded_result],
            )
            .into(),
        ))
    }

    fn verify_in_fact_by_struct_obj(
        &mut self,
        in_fact: &InFact,
        struct_obj: &StructObj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(
            &Obj::StructObj(struct_obj.clone()),
            verify_state,
        )?;
        let (def, header_map) = self.struct_header_param_to_arg_map(struct_obj, verify_state)?;
        let field_types = self.instantiated_struct_field_types(struct_obj, verify_state)?;
        let cart_obj: Obj = Cart::new(field_types).into();
        let cart_membership: AtomicFact =
            InFact::new(in_fact.element.clone(), cart_obj, in_fact.line_file.clone()).into();
        let cart_result = self
            .verify_atomic_fact_by_known_atomic_or_builtin_only(&cart_membership, verify_state)?;
        if !cart_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }

        let mut step_results = vec![cart_result];
        let mut field_map = HashMap::new();
        for (index, (field_name, _)) in def.fields.iter().enumerate() {
            let field_obj = match &in_fact.element {
                Obj::Tuple(tuple) => (*tuple.args[index]).clone(),
                _ => ObjAtIndex::new(
                    in_fact.element.clone(),
                    Number::new((index + 1).to_string()).into(),
                )
                .into(),
            };
            field_map.insert(field_name.clone(), field_obj);
        }

        for fact in def.equivalent_facts.iter() {
            let after_header = self.inst_fact(
                fact,
                &header_map,
                ParamObjType::DefHeader,
                Some(in_fact.line_file.clone()),
            )?;
            let instantiated_fact = self.inst_fact(
                &after_header,
                &field_map,
                ParamObjType::DefStructField,
                Some(in_fact.line_file.clone()),
            )?;
            let fact_result =
                self.verify_fact_by_known_atomic_or_builtin_only(&instantiated_fact, verify_state)?;
            if !fact_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            step_results.push(fact_result);
        }

        Ok(FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            "struct membership: element is in the named cart base and satisfies struct equivalent facts".to_string(),
            step_results,
        )
        .into())
    }

    // The cardinality of a finite set is a natural number, hence also an integer, rational, and real.
    // Example: if `A finite_set`, then `count(A) $in N` and `count(A) $in R`.
    fn verify_count_in_standard_number_set(
        &mut self,
        in_fact: &InFact,
        count: &Count,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let finite_fact = IsFiniteSetFact::new((*count.set).clone(), in_fact.line_file.clone());
        let finite_result = self.verify_non_equational_known_then_builtin_rules_only(
            &finite_fact.into(),
            verify_state,
        )?;
        if finite_result.is_true() {
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "count of a finite set is a natural number",
            ));
        }
        Ok((StmtUnknown::new()).into())
    }
}

fn number_in_set_verified_by_builtin_rules_result(in_fact: &InFact, reason: &str) -> StmtResult {
    StmtResult::from(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

fn not_in_fact_verified_by_builtin_rules_result(
    not_in_fact: &NotInFact,
    reason: &str,
) -> StmtResult {
    StmtResult::from(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            not_in_fact.clone().into(),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

fn arithmetic_obj_in_r_verified_by_builtin_rules_result(in_fact: &InFact) -> StmtResult {
    StmtResult::from(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            "arithmetic expression is in R".to_string(),
            Vec::new(),
        ),
    )
}

fn builtin_in_fact_result_for_evaluated_number_in_standard_set(
    in_fact: &InFact,
    evaluated_number: &Number,
    standard_set: &StandardSet,
) -> StmtResult {
    match standard_set {
        StandardSet::R => number_in_set_verified_by_builtin_rules_result(in_fact, "number in R"),
        StandardSet::RPos => {
            if number_is_in_r_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_pos")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::RNeg => {
            if number_is_in_r_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_neg")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::RNz => {
            if number_is_in_r_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_nz")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::Q => number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q"),
        StandardSet::QPos => {
            if number_is_in_q_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_pos")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::QNeg => {
            if number_is_in_q_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_neg")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::QNz => {
            if number_is_in_q_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_nz")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::Z => {
            if number_is_in_z(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNeg => {
            if number_is_in_z_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z_neg")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNz => {
            if number_is_in_z_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z_nz")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::N => {
            if number_is_in_n(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::NPos => {
            if number_is_in_n_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N_pos")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
    }
}

fn builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
    not_in_fact: &NotInFact,
    evaluated_number: &Number,
    standard_set: &StandardSet,
) -> StmtResult {
    match standard_set {
        StandardSet::R | StandardSet::Q => StmtResult::Unknown(StmtUnknown::new()),
        StandardSet::RPos => {
            if !number_is_in_r_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R_pos")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::RNeg => {
            if !number_is_in_r_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R_neg")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::RNz => {
            if !number_is_in_r_nz(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R_nz")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::QPos => {
            if !number_is_in_q_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q_pos")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::QNeg => {
            if !number_is_in_q_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q_neg")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::QNz => {
            if !number_is_in_q_nz(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q_nz")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::Z => {
            if !number_is_in_z(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNeg => {
            if !number_is_in_z_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z_neg")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNz => {
            if !number_is_in_z_nz(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z_nz")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::N => {
            if !number_is_in_n(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in N")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
        StandardSet::NPos => {
            if !number_is_in_n_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in N_pos")
            } else {
                StmtResult::Unknown(StmtUnknown::new())
            }
        }
    }
}

impl Runtime {
    fn maybe_verify_in_fact_max_min_pair_closed_standard_set(
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
    fn verify_in_fact_sum_or_product_in_r(
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

    fn iterated_op_func_ret_set(&self, func: &Obj) -> Option<Obj> {
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
    // Example: `sum_of_finite_set({1, 2}, 'Z(x){x}) $in Z`; for `N_pos`, the domain must be nonempty.
    fn verify_in_fact_sum_of_finite_set_by_iterand_ret_set(
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
                "sum_of_finite_set: positive summand over a nonempty finite set",
            ));
        }
        if !Self::standard_set_is_subset_eq(&ret_standard_set, &target_set) {
            return Ok((StmtUnknown::new()).into());
        }
        let reason = format!(
            "sum_of_finite_set: summand return set {} is contained in {}",
            ret_standard_set, target_set
        );
        Ok(number_in_set_verified_by_builtin_rules_result(
            in_fact,
            reason.as_str(),
        ))
    }

    // Finite-set product: the return set of the factor controls the numeric set of the product.
    // Example: `product_of_finite_set({1, 2}, 'Z(x){x}) $in Z`; for `N_pos`, the empty product is `1`.
    fn verify_in_fact_product_of_finite_set_by_iterand_ret_set(
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
                "product_of_finite_set: positive factors give a positive finite product",
            ));
        }
        if !Self::standard_set_is_subset_eq(&ret_standard_set, &target_set) {
            return Ok((StmtUnknown::new()).into());
        }
        let reason = format!(
            "product_of_finite_set: factor return set {} is contained in {}",
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
    // Example: `sum(1, n, 'Z(x){x}) $in Z`, `product(1, a, 'N_pos(x){x}) $in Z`.
    fn verify_in_fact_sum_or_product_in_z_by_iterand_ret_set(
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
    fn verify_in_fact_sum_or_product_in_q_by_iterand_ret_set(
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
    // Example: `product(1, a, 'N_pos(x){x}) $in N_pos`.
    fn verify_in_fact_sum_or_product_in_n_pos_by_iterand_ret_set(
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
    fn verify_in_fact_fn_application_in_typed_return_set(
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
    fn verify_in_fact_add_in_n_from_summands_in_n(
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
    fn verify_in_fact_sub_in_n_from_integer_terms_and_bound(
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
    fn verify_in_fact_mul_in_n_from_factors_in_n(
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
    fn verify_in_fact_pow_in_standard_set_from_base_and_natural_exponent(
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
    fn verify_in_fact_pow_in_r_pos_from_positive_base_real_exponent(
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
    fn verify_in_fact_add_in_n_pos_from_n_pos_and_n(
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
    fn verify_in_fact_mul_in_n_pos_from_factors_in_n_pos(
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
    fn verify_in_fact_n_pos_by_zero_less_and_in_z_or_n(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
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

        let in_n = InFact::new(elem.clone(), StandardSet::N.into(), lf.clone()).into();
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
    fn verify_in_fact_standard_positive_by_zero_less_and_base_set(
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
    fn verify_in_fact_n_by_nonnegative_integer(
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

    fn verify_in_fact_closed_range_by_order_bounds(
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

    fn verify_in_fact_open_range_by_order_bounds(
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

    fn verify_in_fact_interval_by_real_order_bounds(
        &mut self,
        in_fact: &InFact,
        interval: &IntervalObj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let mut step_results = Vec::new();

        // Real interval membership requires a real element and the endpoint inequalities.
        // Example: `x $in oc(a,b)` follows from `x $in R`, `a < x`, and `x <= b`.
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

    fn verify_in_fact_one_side_infinity_interval_by_real_order_bound(
        &mut self,
        in_fact: &InFact,
        interval: &OneSideInfinityIntervalObj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let elem = &in_fact.element;
        let lf = in_fact.line_file.clone();
        let mut step_results = Vec::new();

        // Half-infinite real interval membership requires a real element and the finite endpoint bound.
        // Example: `x $in cinf(a)` follows from `x $in R` and `a <= x`.
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
    fn order_lower_bound_from_literals(
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
    fn order_upper_bound_open_from_literals(
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
    fn order_upper_bound_closed_from_literals(
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
    fn verify_in_fact_arithmetic_expression_in_z(
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
    fn verify_in_fact_arithmetic_expression_in_q(
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

    fn verify_in_fact_arithmetic_expression_in_standard_negative_set(
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

    // `{x S : …} ⊆ S` always. If `S ⊆ T` then `{x S : …} ⊆ T`, so `{x S : …} ∈ 𝒫(T)`.
    // Example: from `N $subset Z`, deduce `{x N: x = x} $in power_set(Z)` once that subset is known.
    fn verify_in_fact_set_builder_in_power_set_via_param_subset(
        &mut self,
        in_fact: &InFact,
        set_builder: &SetBuilder,
        power_set: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let base_set = power_set.set.as_ref();
        let subset_fact = SubsetFact::new(
            (*set_builder.param_set).clone(),
            base_set.clone(),
            in_fact.line_file.clone(),
        )
        .into();
        let verify_subset_result =
            self.verify_atomic_fact_by_known_atomic_or_builtin_only(&subset_fact, verify_state)?;
        if !verify_subset_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        let mut infer_result = InferResult::new();
        infer_result.new_infer_result_inside(verify_subset_result.infer_result());
        let stmt = in_fact.clone().into();
        infer_result.new_fact(&stmt);
        Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules(
            stmt.clone(),
            infer_result,
            VerifiedByResult::builtin_rule(
                "set_builder in power_set: param_set subset of base implies builder defines a subset of base"
                    .to_string(),
                stmt,
            ),
        ))
        .into())
    }

    fn verify_in_fact_list_set_in_power_set_defines_membership(
        &mut self,
        in_fact: &InFact,
        list_set: &ListSet,
        power_set: &PowerSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let base_set = power_set.set.as_ref();
        let mut infer_result = InferResult::new();
        for element_box in list_set.list.iter() {
            let element_obj = *element_box.clone();
            let element_in_base_fact =
                InFact::new(element_obj, base_set.clone(), in_fact.line_file.clone()).into();
            let verify_one_element_result = self
                .verify_atomic_fact_by_known_atomic_or_builtin_only(
                    &element_in_base_fact,
                    verify_state,
                )?;
            if !verify_one_element_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            infer_result.new_infer_result_inside(verify_one_element_result.infer_result());
        }
        let stmt = in_fact.clone().into();
        infer_result.new_fact(&stmt);
        Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules(
            stmt.clone(),
            infer_result,
            VerifiedByResult::builtin_rule(
                "list_set in power_set: each element is in the base set".to_string(),
                stmt,
            ),
        ))
        .into())
    }

    fn verify_in_fact_by_equal_to_one_element_in_list_set(
        &mut self,
        in_fact: &InFact,
        list_set: &ListSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let equality_or_result =
            self.verify_in_fact_by_equality_or_for_list_set(in_fact, list_set, verify_state)?;
        if equality_or_result.is_true() {
            return Ok(equality_or_result);
        }

        for current_element_in_list_set in list_set.list.iter() {
            let equal_fact_verify_result = self.verify_objs_are_equal_known_only(
                &in_fact.element,
                current_element_in_list_set.as_ref(),
                in_fact.line_file.clone(),
            );
            if equal_fact_verify_result.is_true() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        format!(
                            "{} equals one element in list_set {}",
                            in_fact.element, in_fact.set
                        ),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }
        Ok((StmtUnknown::new()).into())
    }

    fn verify_in_fact_by_equality_or_for_list_set(
        &mut self,
        in_fact: &InFact,
        list_set: &ListSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if list_set.list.is_empty() {
            return Ok((StmtUnknown::new()).into());
        }

        let mut left_equal_facts = Vec::with_capacity(list_set.list.len());
        let mut right_equal_facts = Vec::with_capacity(list_set.list.len());
        for current_element_in_list_set in list_set.list.iter() {
            left_equal_facts.push(AndChainAtomicFact::AtomicFact(
                EqualFact::new(
                    in_fact.element.clone(),
                    *current_element_in_list_set.clone(),
                    in_fact.line_file.clone(),
                )
                .into(),
            ));
            right_equal_facts.push(AndChainAtomicFact::AtomicFact(
                EqualFact::new(
                    *current_element_in_list_set.clone(),
                    in_fact.element.clone(),
                    in_fact.line_file.clone(),
                )
                .into(),
            ));
        }

        let candidate_or_facts = [
            OrFact::new(left_equal_facts, in_fact.line_file.clone()),
            OrFact::new(right_equal_facts, in_fact.line_file.clone()),
        ];

        for candidate_or_fact in candidate_or_facts {
            let candidate_result = self
                .verify_or_fact_known_then_builtin_rules_only(&candidate_or_fact, verify_state)?;
            if candidate_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        in_fact.clone().into(),
                        InferResult::from_fact(&in_fact.clone().into()),
                        "list_set membership: equality with one listed element".to_string(),
                        vec![candidate_result],
                    )
                    .into(),
                );
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn verify_not_in_fact_by_not_equal_to_every_element_in_list_set(
        &mut self,
        not_in_fact: &NotInFact,
        list_set: &ListSet,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        for current_element_in_list_set in list_set.list.iter() {
            let not_equal_fact = NotEqualFact::new(
                not_in_fact.element.clone(),
                *current_element_in_list_set.clone(),
                not_in_fact.line_file.clone(),
            )
            .into();
            let not_equal_fact_verify_result = self
                .verify_atomic_fact_known_then_builtin_rules_only(&not_equal_fact, verify_state)?;
            if !not_equal_fact_verify_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
        }

        Ok(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                not_in_fact.clone().into(),
                format!(
                    "{} is not equal to every element in list_set {}",
                    not_in_fact.element, not_in_fact.set
                ),
                Vec::new(),
            ))
            .into(),
        )
    }

    fn standard_subset_set_objs_for_target_set(target_set_obj: &Obj) -> Option<Vec<Obj>> {
        match target_set_obj {
            Obj::StandardSet(StandardSet::NPos) => Some(vec![]),
            Obj::StandardSet(StandardSet::N) => Some(vec![StandardSet::NPos.into()]),
            Obj::StandardSet(StandardSet::ZNeg) => Some(vec![]),
            Obj::StandardSet(StandardSet::ZNz) => {
                Some(vec![StandardSet::NPos.into(), StandardSet::ZNeg.into()])
            }
            Obj::StandardSet(StandardSet::Z) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::N.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
            ]),
            Obj::StandardSet(StandardSet::QPos) => Some(vec![StandardSet::NPos.into()]),
            Obj::StandardSet(StandardSet::QNeg) => Some(vec![StandardSet::ZNeg.into()]),
            Obj::StandardSet(StandardSet::QNz) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
            ]),
            Obj::StandardSet(StandardSet::Q) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::N.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::Z.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
                StandardSet::QNz.into(),
            ]),
            Obj::StandardSet(StandardSet::RPos) => {
                Some(vec![StandardSet::NPos.into(), StandardSet::QPos.into()])
            }
            Obj::StandardSet(StandardSet::RNeg) => {
                Some(vec![StandardSet::ZNeg.into(), StandardSet::QNeg.into()])
            }
            Obj::StandardSet(StandardSet::RNz) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
                StandardSet::QNz.into(),
                StandardSet::RPos.into(),
                StandardSet::RNeg.into(),
            ]),
            Obj::StandardSet(StandardSet::R) => Some(vec![
                StandardSet::NPos.into(),
                StandardSet::N.into(),
                StandardSet::ZNeg.into(),
                StandardSet::ZNz.into(),
                StandardSet::Z.into(),
                StandardSet::QPos.into(),
                StandardSet::QNeg.into(),
                StandardSet::QNz.into(),
                StandardSet::Q.into(),
                StandardSet::RPos.into(),
                StandardSet::RNeg.into(),
                StandardSet::RNz.into(),
            ]),
            _ => None,
        }
    }

    // If the env already has `element $in fn_def` (from `known_objs_in_fn_sets`), compare to the RHS `fn ...`.
    fn verify_in_fact_element_in_fn_set_by_stored_definition(
        &mut self,
        element: &Obj,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(stored_fn_set) = self.get_cloned_object_in_fn_set(element) else {
            return Ok((StmtUnknown::new()).into());
        };
        if stored_fn_set.to_string() == expected_fn_set.to_string() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "fn membership: stored fn signature matches RHS".to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        let flat_stored =
            ParamGroupWithSet::collect_param_names(&stored_fn_set.params_def_with_set);
        let flat_expected =
            ParamGroupWithSet::collect_param_names(&expected_fn_set.body.params_def_with_set);
        if flat_stored.len() != flat_expected.len() {
            return Ok((StmtUnknown::new()).into());
        }
        let shared_names = self.generate_random_unused_names(flat_stored.len());
        let stored_norm =
            self.fn_set_alpha_renamed_for_display_compare(&stored_fn_set, &shared_names)?;
        let expected_norm =
            self.fn_set_alpha_renamed_for_display_compare(&expected_fn_set.body, &shared_names)?;
        if stored_norm.to_string() == expected_norm.to_string() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "fn membership: stored fn signature matches RHS (alpha-renamed parameters)"
                        .to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        Ok((StmtUnknown::new()).into())
    }

    /// `anon $in S` when `S` is a function space [`FnSet`] and the anonymous function's
    /// [`FnSetBody`] (params, dom facts, return set) matches `S` (same as comparing `S` to a
    /// [`FnSet`] built from the anon's body without the braced `equal_to`).
    fn verify_in_fact_anonymous_fn_signature_matches_fn_set(
        &mut self,
        anon: &AnonymousFn,
        expected_fn_set: &FnSet,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let _ = verify_state;
        let signature_from_anon = FnSet::new(
            anon.body.params_def_with_set.clone(),
            anon.body.dom_facts.clone(),
            (*anon.body.ret_set).clone(),
        )?;
        if signature_from_anon.to_string() == expected_fn_set.to_string() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "anonymous function: signature (params, dom, co-domain) matches `fn` set"
                        .to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        let flat_a =
            ParamGroupWithSet::collect_param_names(&signature_from_anon.body.params_def_with_set);
        let flat_e =
            ParamGroupWithSet::collect_param_names(&expected_fn_set.body.params_def_with_set);
        if flat_a.len() != flat_e.len() {
            return Ok((StmtUnknown::new()).into());
        }
        let shared_names = self.generate_random_unused_names(flat_a.len());
        let a_norm = self
            .fn_set_alpha_renamed_for_display_compare(&signature_from_anon.body, &shared_names)?;
        let e_norm =
            self.fn_set_alpha_renamed_for_display_compare(&expected_fn_set.body, &shared_names)?;
        if a_norm.to_string() == e_norm.to_string() {
            return Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "anonymous function: signature matches `fn` set (alpha-renamed parameters)"
                        .to_string(),
                    Vec::new(),
                ))
                .into(),
            );
        }
        Ok((StmtUnknown::new()).into())
    }

    // If every entry of `[a, b, ...]` is in `S`, then applying it at a valid index gives an element of `S`.
    // Example: `[1, 2, 3](i) $in R` follows from `i $in N_pos`, `i <= 3`, and each entry in `R`.
    fn verify_in_fact_finite_seq_literal_application_in_set(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let Obj::FnObj(fn_obj) = &in_fact.element else {
            return Ok((StmtUnknown::new()).into());
        };
        let FnObjHead::FiniteSeqListObj(list) = fn_obj.head.as_ref() else {
            return Ok((StmtUnknown::new()).into());
        };
        if fn_obj.body.len() != 1 || fn_obj.body[0].len() != 1 {
            return Ok((StmtUnknown::new()).into());
        };

        let index_obj = fn_obj.body[0][0].as_ref().clone();
        let mut step_results = Vec::new();

        let index_in_n_pos: AtomicFact = InFact::new(
            index_obj.clone(),
            StandardSet::NPos.into(),
            in_fact.line_file.clone(),
        )
        .into();
        let index_in_n_pos_result =
            self.verify_atomic_fact_known_then_builtin_rules_only(&index_in_n_pos, verify_state)?;
        if !index_in_n_pos_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(index_in_n_pos_result);

        let list_len_obj: Obj = Number::new(list.objs.len().to_string()).into();
        let index_in_range: AtomicFact =
            LessEqualFact::new(index_obj, list_len_obj, in_fact.line_file.clone()).into();
        let index_in_range_result =
            self.verify_atomic_fact_known_then_builtin_rules_only(&index_in_range, verify_state)?;
        if !index_in_range_result.is_true() {
            return Ok((StmtUnknown::new()).into());
        }
        step_results.push(index_in_range_result);

        for element in list.objs.iter() {
            let element_in_target_set: AtomicFact = InFact::new(
                element.as_ref().clone(),
                target_set_obj.clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let result = self.verify_atomic_fact_known_then_builtin_rules_only(
                &element_in_target_set,
                verify_state,
            )?;
            if !result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            step_results.push(result);
        }

        Ok(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                format!(
                    "finite sequence literal application is in {}",
                    target_set_obj
                ),
                step_results,
            ))
            .into(),
        )
    }

    // If `x $in cart({a, b}, {c, d})` is known, then `x[1]` ranges over `{a, b}`.
    // Example: if every element of `{a, b}` is in `R`, prove `x[1] $in R`.
    fn verify_in_fact_obj_at_index_in_standard_set_by_cart_factor_list_set(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let Obj::StandardSet(_) = target_set_obj else {
            return Ok((StmtUnknown::new()).into());
        };
        let Obj::ObjAtIndex(obj_at_index) = &in_fact.element else {
            return Ok((StmtUnknown::new()).into());
        };
        let Some(cart) = self.get_object_equal_to_cart(&obj_at_index.obj.to_string()) else {
            return Ok((StmtUnknown::new()).into());
        };
        let Some(index_number) = self.resolve_obj_to_number(&obj_at_index.index) else {
            return Ok((StmtUnknown::new()).into());
        };
        let Ok(one_based_index) = index_number.normalized_value.parse::<usize>() else {
            return Ok((StmtUnknown::new()).into());
        };
        if one_based_index == 0 || one_based_index > cart.args.len() {
            return Ok((StmtUnknown::new()).into());
        }

        let factor = cart.args[one_based_index - 1].as_ref();
        let Obj::ListSet(list_set) = factor else {
            return Ok((StmtUnknown::new()).into());
        };

        let mut step_results = Vec::new();
        for element in list_set.list.iter() {
            let element_in_target_set: AtomicFact = InFact::new(
                element.as_ref().clone(),
                target_set_obj.clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let result = self.verify_atomic_fact_known_then_builtin_rules_only(
                &element_in_target_set,
                verify_state,
            )?;
            if !result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
            step_results.push(result);
        }

        Ok(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                format!(
                    "cart projection list_set elements are all in {}",
                    target_set_obj
                ),
                step_results,
            ))
            .into(),
        )
    }

    fn verify_in_fact_by_known_standard_subset_membership(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
    ) -> Result<StmtResult, RuntimeError> {
        let standard_subset_set_objs =
            match Self::standard_subset_set_objs_for_target_set(target_set_obj) {
                Some(standard_subset_set_objs) => standard_subset_set_objs,
                None => return Ok((StmtUnknown::new()).into()),
            };
        for standard_subset_set_obj in standard_subset_set_objs.iter() {
            let in_fact_into_standard_subset = InFact::new(
                in_fact.element.clone(),
                standard_subset_set_obj.clone(),
                in_fact.line_file.clone(),
            )
            .into();
            let verify_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
                &in_fact_into_standard_subset,
            )?;
            if verify_result.is_true() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        in_fact.clone().into(),
                        format!(
                            "{} in {} implies in {} (standard subset relation)",
                            in_fact.element, standard_subset_set_obj, target_set_obj
                        ),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }
        Ok((StmtUnknown::new()).into())
    }

    fn verify_not_in_z_for_resolved_numeric_div(
        &self,
        not_in_fact: &NotInFact,
    ) -> Option<StmtResult> {
        let (numerator, denominator) = self.resolved_numeric_div_operands(&not_in_fact.element)?;
        if !number_is_in_z(&numerator) || !number_is_in_z_nz(&denominator) {
            return None;
        }

        let remainder_obj: Obj = Mod::new(numerator.into(), denominator.into()).into();
        let remainder = self.resolve_obj_to_number_resolved(&remainder_obj)?;
        if matches!(
            compare_normalized_number_str_to_zero(&remainder.normalized_value),
            NumberCompareResult::Equal
        ) {
            return None;
        }

        Some(not_in_fact_verified_by_builtin_rules_result(
            not_in_fact,
            "numeric division not in Z: resolved numerator % denominator != 0",
        ))
    }

    fn resolved_numeric_div_operands(&self, obj: &Obj) -> Option<(Number, Number)> {
        if let Some(operands) = self.numeric_div_operands_after_resolve(obj) {
            return Some(operands);
        }

        let obj_key = obj.to_string();
        for env in self.iter_environments_from_top() {
            let Some((_, equal_objs)) = env.known_equality.get(&obj_key) else {
                continue;
            };
            for equal_obj in equal_objs.iter() {
                if let Some(operands) = self.numeric_div_operands_after_resolve(equal_obj) {
                    return Some(operands);
                }
            }
        }
        None
    }

    fn numeric_div_operands_after_resolve(&self, obj: &Obj) -> Option<(Number, Number)> {
        let resolved = self.resolve_obj(obj);
        let Obj::Div(div) = resolved else {
            return None;
        };
        let numerator = self.resolve_obj_to_number_resolved(div.left.as_ref())?;
        let denominator = self.resolve_obj_to_number_resolved(div.right.as_ref())?;
        Some((numerator, denominator))
    }

    fn verify_in_fact_by_left_is_tuple_right_is_cart(
        &mut self,
        in_fact: &InFact,
        tuple: &Tuple,
        cart: &Cart,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if tuple.args.len() < 2 {
            return Ok((StmtUnknown::new()).into());
        }
        if tuple.args.len() != cart.args.len() {
            return Ok((StmtUnknown::new()).into());
        }

        for component_index in 0..tuple.args.len() {
            let tuple_component_obj = (*tuple.args[component_index]).clone();
            let cart_component_obj = (*cart.args[component_index]).clone();
            let component_in_fact = InFact::new(
                tuple_component_obj,
                cart_component_obj,
                in_fact.line_file.clone(),
            )
            .into();
            let component_verify_result = self.verify_atomic_fact_known_then_builtin_rules_only(
                &component_in_fact,
                verify_state,
            )?;
            if !component_verify_result.is_true() {
                return Ok((StmtUnknown::new()).into());
            }
        }

        Ok(
            (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                in_fact.clone().into(),
                "tuple in cart: each component is in the corresponding cart factor".to_string(),
                Vec::new(),
            ))
            .into(),
        )
    }
}
