use super::*;

impl Runtime {
    pub fn verify_not_in_fact_with_builtin_rules(
        &mut self,
        not_in_fact: &NotInFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
                    builtin_state,
                ),
            (_, Obj::Intersect(intersect)) => self
                .verify_not_in_fact_not_in_intersect_by_non_member_of_either_side(
                    not_in_fact,
                    intersect,
                    builtin_state,
                ),
            (_, right) => {
                // Set-difference elimination: membership in A \ B entails
                // non-membership in B.
                let mut evidence = None;
                for environment in self.iter_environments_from_top() {
                    for known_facts_map in environment.known_atomic_facts_with_2_args.values() {
                        for known_fact in known_facts_map.values() {
                            let AtomicFact::InFact(member) = known_fact else {
                                continue;
                            };
                            let Obj::SetMinus(set_minus) = &member.set else {
                                continue;
                            };
                            if verify_equality_by_they_are_the_same(
                                &member.element,
                                &not_in_fact.element,
                            ) && verify_equality_by_they_are_the_same(&set_minus.right, right)
                            {
                                evidence = Some(known_fact.clone());
                                break;
                            }
                        }
                    }
                }
                if evidence.is_some() {
                    Ok(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            not_in_fact.clone().into(),
                            "set-minus membership excludes the right operand".to_string(),
                            Vec::new(),
                        )
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
        }
    }

    pub fn verify_in_fact_with_builtin_rules(
        &mut self,
        in_fact: &InFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Obj::FnSet(fn_set) = &in_fact.set {
            if let Some(result) = self.verify_in_fact_element_in_fn_set_by_pointwise_values(
                &in_fact.element,
                fn_set,
                in_fact,
                &UseContextVerifyState::new(0, true),
            )? {
                return Ok(result);
            }
        }
        if let Obj::GeneralCart(general_cart) = &in_fact.set {
            let result = self.verify_in_fact_in_general_cart_by_defining_facts(
                in_fact,
                general_cart,
                &UseContextVerifyState::new(0, true),
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }
        if let Some(result) =
            self.try_verify_set_builder_membership_definition_transport(in_fact)?
        {
            return Ok(result);
        }
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
        let direct_superset_result = self.verify_in_fact_by_known_direct_superset(in_fact)?;
        if direct_superset_result.is_true() {
            return Ok(direct_superset_result);
        }
        if let Some(result) = self.verify_reduce_membership_from_operation_carrier(in_fact) {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_refined_integer_carrier_from_known_sign(in_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.maybe_verify_in_fact_finite_set_extremum(in_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self.maybe_verify_in_fact_builtin_operator_signature(in_fact) {
            return Ok(result);
        }
        if matches!(
            (&in_fact.element, &in_fact.set),
            (Obj::ImaginaryUnit(_), Obj::StandardSet(StandardSet::C))
        ) {
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "native imaginary unit is in C",
            ));
        }
        // Euler's number and pi are primitive positive real constants.
        // Example: `e $in R+`, `pi $in R`, and therefore both are also in `C`.
        if matches!(&in_fact.element, Obj::EulerNumber(_) | Obj::Pi(_))
            && matches!(
                &in_fact.set,
                Obj::StandardSet(StandardSet::RPos)
                    | Obj::StandardSet(StandardSet::R)
                    | Obj::StandardSet(StandardSet::C)
            )
        {
            let reason = match &in_fact.set {
                Obj::StandardSet(StandardSet::RPos) => {
                    "native mathematical constant is a positive real"
                }
                Obj::StandardSet(StandardSet::R) => "native mathematical constant is a real",
                Obj::StandardSet(StandardSet::C) => {
                    "native mathematical constant is real, hence is in C"
                }
                _ => unreachable!(),
            };
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact, reason,
            ));
        }
        // Real and imaginary coordinates and complex modulus map a complex argument into R.
        // Example: `z $in C` implies `re(z) $in R`.
        if matches!(
            &in_fact.element,
            Obj::RealPart(_) | Obj::ImaginaryPart(_) | Obj::ComplexAbs(_)
        ) && matches!(
            &in_fact.set,
            Obj::StandardSet(StandardSet::R) | Obj::StandardSet(StandardSet::C)
        ) {
            let reason = if matches!(&in_fact.set, Obj::StandardSet(StandardSet::R)) {
                "native complex coordinate or modulus has real result"
            } else {
                "native complex coordinate or modulus has real result, hence is in C"
            };
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact, reason,
            ));
        }
        // Native real trigonometric objects map a well-defined real argument into R.
        // Example: `x R` implies `sin(x) $in R`; `tan(x)` additionally needs `cos(x) != 0`.
        if matches!(
            &in_fact.element,
            Obj::Sin(_) | Obj::Cos(_) | Obj::Tan(_) | Obj::Cot(_)
        ) && matches!(
            &in_fact.set,
            Obj::StandardSet(StandardSet::R) | Obj::StandardSet(StandardSet::C)
        ) {
            let reason = if matches!(&in_fact.set, Obj::StandardSet(StandardSet::R)) {
                "native real trigonometric object has real result"
            } else {
                "native real trigonometric object has real result, hence is in C"
            };
            return Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact, reason,
            ));
        }
        match (&in_fact.element, &in_fact.set) {
            (_, Obj::Union(union)) => {
                return self.verify_in_fact_in_union_by_member_of_either_side(
                    in_fact,
                    union,
                    builtin_state,
                );
            }
            (_, Obj::Intersect(intersect)) => {
                return self.verify_in_fact_in_intersect_by_member_of_both_sides(
                    in_fact,
                    intersect,
                    builtin_state,
                );
            }
            (_, Obj::SetMinus(set_minus)) => {
                return self.verify_in_fact_in_set_minus_by_member_and_non_member(
                    in_fact,
                    set_minus,
                    builtin_state,
                );
            }
            (_, Obj::BigUnion(big_union)) => {
                return self.verify_in_fact_in_big_union_by_member_witness(
                    in_fact,
                    big_union,
                    builtin_state,
                );
            }
            (_, Obj::Replacement(replacement)) => {
                return self.verify_in_fact_in_replacement_by_relation_witness(
                    in_fact,
                    replacement,
                    builtin_state,
                );
            }
            (Obj::Tuple(tuple), Obj::Cart(cart)) => {
                return self.verify_in_fact_by_left_is_tuple_right_is_cart(
                    in_fact,
                    tuple,
                    cart,
                    builtin_state,
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
                    builtin_state,
                    "sum",
                ),
            (Obj::Product(product), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_sum_or_product_in_n_pos_by_iterand_ret_set(
                    in_fact,
                    product.func.as_ref(),
                    builtin_state,
                    "product",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::NPos,
                    builtin_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::NPos,
                    builtin_state,
                ),
            (Obj::Add(add), Obj::StandardSet(StandardSet::N)) => {
                self.verify_in_fact_add_in_n_from_summands_in_n(in_fact, add, builtin_state)
            }
            (Obj::Sub(sub), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_sub_in_n_from_integer_terms_and_bound(in_fact, sub, builtin_state),
            (Obj::Mul(mul), Obj::StandardSet(StandardSet::N)) => {
                self.verify_in_fact_mul_in_n_from_factors_in_n(in_fact, mul, builtin_state)
            }
            (Obj::Pow(pow), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_pow_in_standard_set_from_base_and_natural_exponent(
                    in_fact,
                    pow,
                    builtin_state,
                    StandardSet::N,
                    "N: a^k from a in N and k in N",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::N,
                    builtin_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::N,
                    builtin_state,
                ),
            (Obj::Sum(sum), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_sum_or_product_by_iterand_ret_set(
                    in_fact,
                    sum.func.as_ref(),
                    StandardSet::N,
                    builtin_state,
                    "sum",
                ),
            (Obj::Product(product), Obj::StandardSet(StandardSet::N)) => self
                .verify_in_fact_sum_or_product_by_iterand_ret_set(
                    in_fact,
                    product.func.as_ref(),
                    StandardSet::N,
                    builtin_state,
                    "product",
                ),
            (Obj::FiniteSetSize(finite_set_size), Obj::StandardSet(StandardSet::N))
            | (Obj::FiniteSetSize(finite_set_size), Obj::StandardSet(StandardSet::Z))
            | (Obj::FiniteSetSize(finite_set_size), Obj::StandardSet(StandardSet::Q))
            | (Obj::FiniteSetSize(finite_set_size), Obj::StandardSet(StandardSet::R))
            | (Obj::FiniteSetSize(finite_set_size), Obj::StandardSet(StandardSet::C)) => self
                .verify_finite_set_size_in_standard_number_set(
                    in_fact,
                    finite_set_size,
                    builtin_state,
                ),
            (Obj::FnObj(fn_obj), Obj::FnRange(fn_range)) => {
                self.verify_in_fact_fn_application_in_fn_range(in_fact, fn_obj, fn_range)
            }
            (Obj::Add(add), Obj::StandardSet(StandardSet::NPos)) => {
                self.verify_in_fact_add_in_n_pos_from_n_pos_and_n(in_fact, add, builtin_state)
            }
            (Obj::Abs(abs), Obj::StandardSet(StandardSet::NPos)) => {
                let mut evidence = None;
                for source_carrier in [StandardSet::NPos, StandardSet::ZNeg, StandardSet::ZStar] {
                    let source_membership: AtomicFact = InFact::new(
                        abs.arg.as_ref().clone(),
                        source_carrier.into(),
                        in_fact.line_file.clone(),
                    )
                    .into();
                    let result =
                        self.verify_builtin_rule_premise(&source_membership, builtin_state)?;
                    if result.is_true() {
                        evidence = Some(result);
                        break;
                    }
                }
                if let Some(evidence) = evidence {
                    Ok(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            in_fact.clone().into(),
                            "absolute value of a known nonzero integer is a positive natural"
                                .to_string(),
                            vec![evidence],
                        )
                        .into(),
                    )
                } else {
                    Ok((StmtUnknown::new()).into())
                }
            }
            (Obj::Sub(sub), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_sub_in_n_pos_from_n_pos_and_greater_than_one(
                    in_fact,
                    sub,
                    builtin_state,
                ),
            (Obj::Mul(mul), Obj::StandardSet(StandardSet::NPos)) => {
                self.verify_in_fact_mul_in_n_pos_from_factors_in_n_pos(in_fact, mul, builtin_state)
            }
            (Obj::Pow(pow), Obj::StandardSet(StandardSet::NPos)) => self
                .verify_in_fact_pow_in_standard_set_from_base_and_natural_exponent(
                    in_fact,
                    pow,
                    builtin_state,
                    StandardSet::NPos,
                    "N+: a^k from a in N+ and k in N",
                ),
            (
                Obj::Gcd(_),
                Obj::StandardSet(
                    StandardSet::NPos
                    | StandardSet::N
                    | StandardSet::Z
                    | StandardSet::Q
                    | StandardSet::R
                    | StandardSet::C
                    | StandardSet::QPos
                    | StandardSet::RPos,
                ),
            ) => Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "gcd of a non-all-zero integer pair is a positive integer".to_string(),
                    Vec::new(),
                )
                .into(),
            ),
            (
                Obj::Lcm(_),
                Obj::StandardSet(
                    StandardSet::N
                    | StandardSet::Z
                    | StandardSet::Q
                    | StandardSet::R
                    | StandardSet::C,
                ),
            ) => Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "lcm of two integers is a nonnegative integer".to_string(),
                    Vec::new(),
                )
                .into(),
            ),
            (
                Obj::Floor(_) | Obj::Ceil(_),
                Obj::StandardSet(StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C),
            ) => Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "floor and ceil return integers".to_string(),
                    Vec::new(),
                )
                .into(),
            ),
            (Obj::Min(_) | Obj::Max(_), Obj::StandardSet(StandardSet::R | StandardSet::C)) => Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "minimum and maximum of real arguments are real".to_string(),
                    Vec::new(),
                )
                .into(),
            ),
            (
                Obj::Exp(_),
                Obj::StandardSet(StandardSet::RPos | StandardSet::R | StandardSet::C),
            ) => Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "real exponential values are positive reals".to_string(),
                    Vec::new(),
                )
                .into(),
            ),
            (Obj::Ln(_), Obj::StandardSet(StandardSet::R | StandardSet::C)) => Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "natural logarithm of a positive real is real".to_string(),
                    Vec::new(),
                )
                .into(),
            ),
            (
                Obj::Sign(_),
                Obj::StandardSet(StandardSet::Z | StandardSet::Q | StandardSet::R | StandardSet::C),
            ) => Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "the real sign function returns an integer".to_string(),
                    Vec::new(),
                )
                .into(),
            ),
            (
                Obj::Factorial(_),
                Obj::StandardSet(
                    StandardSet::NPos
                    | StandardSet::N
                    | StandardSet::Z
                    | StandardSet::Q
                    | StandardSet::R
                    | StandardSet::C
                    | StandardSet::QPos
                    | StandardSet::RPos,
                ),
            ) => Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    in_fact.clone().into(),
                    "factorial of a natural number is a positive integer".to_string(),
                    Vec::new(),
                )
                .into(),
            ),
            (_, Obj::StandardSet(StandardSet::N)) => {
                self.verify_in_fact_n_by_nonnegative_integer(in_fact, builtin_state)
            }
            (Obj::Pow(pow), Obj::StandardSet(StandardSet::RPos)) => self
                .verify_in_fact_pow_in_r_pos_from_positive_base_real_exponent(
                    in_fact,
                    pow,
                    builtin_state,
                ),
            (_, Obj::StandardSet(StandardSet::NPos)) => {
                self.verify_in_fact_n_pos_by_zero_less_and_in_z_or_n(in_fact, builtin_state)
            }
            (_, Obj::StandardSet(StandardSet::QPos)) => self
                .verify_in_fact_standard_positive_by_zero_less_and_base_set(
                    in_fact,
                    builtin_state,
                    StandardSet::Q,
                    "Q+: 0 < x and x in Q",
                ),
            (_, Obj::StandardSet(StandardSet::RPos)) => self
                .verify_in_fact_standard_positive_by_zero_less_and_base_set(
                    in_fact,
                    builtin_state,
                    StandardSet::R,
                    "R+: 0 < x and x in R",
                ),
            (_, Obj::ClosedRange(closed_range)) => self
                .verify_in_fact_closed_range_by_order_bounds(in_fact, closed_range, builtin_state),
            (_, Obj::Range(range)) => {
                self.verify_in_fact_open_range_by_order_bounds(in_fact, range, builtin_state)
            }
            (_, Obj::IntervalObj(interval)) => {
                self.verify_in_fact_interval_by_real_order_bounds(in_fact, interval, builtin_state)
            }
            (_, Obj::OneSideInfinityIntervalObj(interval)) => self
                .verify_in_fact_one_side_infinity_interval_by_real_order_bound(
                    in_fact,
                    interval,
                    builtin_state,
                ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Mod(_) | Obj::Pow(_) | Obj::Abs(_),
                Obj::StandardSet(StandardSet::Z),
            ) => self.verify_in_fact_arithmetic_expression_in_z(in_fact, builtin_state),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Pow(_) | Obj::Abs(_),
                Obj::StandardSet(StandardSet::Q),
            ) => self.verify_in_fact_arithmetic_expression_in_q(in_fact, builtin_state),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet(StandardSet::RNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                builtin_state,
                StandardSet::RNeg,
            ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet(StandardSet::QNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                builtin_state,
                StandardSet::QNeg,
            ),
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet(StandardSet::ZNeg),
            ) => self.verify_in_fact_arithmetic_expression_in_standard_negative_set(
                in_fact,
                builtin_state,
                StandardSet::ZNeg,
            ),
            (
                Obj::Add(_)
                | Obj::Sub(_)
                | Obj::Mul(_)
                | Obj::Div(_)
                | Obj::Mod(_)
                | Obj::Pow(_)
                | Obj::Abs(_)
                | Obj::Sin(_)
                | Obj::Cos(_)
                | Obj::Tan(_)
                | Obj::Cot(_)
                | Obj::Sqrt(_)
                | Obj::Log(_),
                Obj::StandardSet(StandardSet::R),
            ) => self.verify_in_fact_arithmetic_expression_in_r(in_fact, builtin_state),
            (
                Obj::Add(_)
                | Obj::Sub(_)
                | Obj::Mul(_)
                | Obj::Div(_)
                | Obj::Mod(_)
                | Obj::Pow(_)
                | Obj::Abs(_)
                | Obj::Sqrt(_)
                | Obj::Log(_),
                Obj::StandardSet(StandardSet::C),
            ) => self.verify_in_fact_arithmetic_expression_in_c(in_fact, builtin_state),
            (Obj::Sum(_), Obj::StandardSet(StandardSet::R)) => self
                .verify_in_fact_sum_or_product_by_iterand_ret_set(
                    in_fact,
                    match &in_fact.element {
                        Obj::Sum(sum) => sum.func.as_ref(),
                        _ => unreachable!(),
                    },
                    StandardSet::R,
                    builtin_state,
                    "sum",
                ),
            (Obj::Product(_), Obj::StandardSet(StandardSet::R)) => self
                .verify_in_fact_sum_or_product_by_iterand_ret_set(
                    in_fact,
                    match &in_fact.element {
                        Obj::Product(product) => product.func.as_ref(),
                        _ => unreachable!(),
                    },
                    StandardSet::R,
                    builtin_state,
                    "product",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::R)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::R,
                    builtin_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::R)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::R,
                    builtin_state,
                ),
            (Obj::Sum(sum), Obj::StandardSet(StandardSet::Z)) => self
                .verify_in_fact_sum_or_product_by_iterand_ret_set(
                    in_fact,
                    sum.func.as_ref(),
                    StandardSet::Z,
                    builtin_state,
                    "sum",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::Z)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::Z,
                    builtin_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::Z)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::Z,
                    builtin_state,
                ),
            (Obj::Product(product), Obj::StandardSet(StandardSet::Z)) => self
                .verify_in_fact_sum_or_product_by_iterand_ret_set(
                    in_fact,
                    product.func.as_ref(),
                    StandardSet::Z,
                    builtin_state,
                    "product",
                ),
            (Obj::Sum(sum), Obj::StandardSet(StandardSet::Q)) => self
                .verify_in_fact_sum_or_product_by_iterand_ret_set(
                    in_fact,
                    sum.func.as_ref(),
                    StandardSet::Q,
                    builtin_state,
                    "sum",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::Q)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::Q,
                    builtin_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::Q)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::Q,
                    builtin_state,
                ),
            (Obj::Product(product), Obj::StandardSet(StandardSet::Q)) => self
                .verify_in_fact_sum_or_product_by_iterand_ret_set(
                    in_fact,
                    product.func.as_ref(),
                    StandardSet::Q,
                    builtin_state,
                    "product",
                ),
            (Obj::Sum(sum), Obj::StandardSet(StandardSet::C)) => self
                .verify_in_fact_sum_or_product_by_iterand_ret_set(
                    in_fact,
                    sum.func.as_ref(),
                    StandardSet::C,
                    builtin_state,
                    "sum",
                ),
            (Obj::Product(product), Obj::StandardSet(StandardSet::C)) => self
                .verify_in_fact_sum_or_product_by_iterand_ret_set(
                    in_fact,
                    product.func.as_ref(),
                    StandardSet::C,
                    builtin_state,
                    "product",
                ),
            (Obj::SumOfFiniteSet(sum), Obj::StandardSet(StandardSet::C)) => self
                .verify_in_fact_finite_set_sum_by_iterand_ret_set(
                    in_fact,
                    sum,
                    StandardSet::C,
                    builtin_state,
                ),
            (Obj::ProductOfFiniteSet(product), Obj::StandardSet(StandardSet::C)) => self
                .verify_in_fact_finite_set_product_by_iterand_ret_set(
                    in_fact,
                    product,
                    StandardSet::C,
                    builtin_state,
                ),
            (Obj::ListSet(list_set), Obj::PowerSet(power_set)) => self
                .verify_in_fact_list_set_in_power_set_defines_membership(
                    in_fact,
                    list_set,
                    power_set,
                    builtin_state,
                ),
            (Obj::SetBuilder(set_builder), Obj::PowerSet(power_set)) => self
                .verify_in_fact_set_builder_in_power_set_via_param_subset(
                    in_fact,
                    set_builder,
                    power_set,
                    builtin_state,
                ),
            (Obj::FnRange(fn_range), Obj::PowerSet(power_set)) => self
                .verify_in_fact_fn_range_in_power_set(in_fact, fn_range, power_set, builtin_state),
            (_, Obj::PowerSet(power_set)) => {
                self.verify_in_fact_in_power_set_via_subset(in_fact, power_set, builtin_state)
            }
            (_, Obj::ListSet(list_set)) => self.verify_in_fact_by_equal_to_one_element_in_list_set(
                in_fact,
                list_set,
                builtin_state,
            ),
            (Obj::FiniteSeqListObj(list), Obj::FiniteSeqSet(fs)) => {
                let lf = in_fact.line_file.clone();
                let len_obj: Obj = Number::new(list.objs.len().to_string()).into();
                let length_result = self.verify_objs_are_equal_by_known_equality(
                    &len_obj,
                    fs.n.as_ref(),
                    lf.clone(),
                );
                if !length_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }
                let mut subgoals = vec![length_result];
                for o in list.objs.iter() {
                    let f: AtomicFact =
                        InFact::new((**o).clone(), (*fs.set).clone(), lf.clone()).into();
                    let result = self.verify_builtin_rule_premise(&f, builtin_state)?;
                    if !result.is_true() {
                        return Ok((StmtUnknown::new()).into());
                    }
                    subgoals.push(result);
                }
                Ok(
                    number_in_set_verified_by_builtin_rules_result_with_subgoals(
                        in_fact,
                        "finite_seq list: length equals n and each entry in co-domain",
                        subgoals,
                    ),
                )
            }
            (Obj::MatrixListObj(list), Obj::MatrixSet(ms)) => {
                let lf = in_fact.line_file.clone();
                let n_rows_obj: Obj = Number::new(list.rows.len().to_string()).into();
                let row_count_result = self.verify_objs_are_equal_by_known_equality(
                    &n_rows_obj,
                    ms.row_len.as_ref(),
                    lf.clone(),
                );
                if !row_count_result.is_true() {
                    return Ok((StmtUnknown::new()).into());
                }
                let mut subgoals = vec![row_count_result];
                for row in list.rows.iter() {
                    let n_col_obj: Obj = Number::new(row.len().to_string()).into();
                    let column_count_result = self.verify_objs_are_equal_by_known_equality(
                        &n_col_obj,
                        ms.col_len.as_ref(),
                        lf.clone(),
                    );
                    if !column_count_result.is_true() {
                        return Ok((StmtUnknown::new()).into());
                    }
                    subgoals.push(column_count_result);
                    for o in row.iter() {
                        let f: AtomicFact =
                            InFact::new((**o).clone(), (*ms.set).clone(), lf.clone()).into();
                        let result = self.verify_builtin_rule_premise(&f, builtin_state)?;
                        if !result.is_true() {
                            return Ok((StmtUnknown::new()).into());
                        }
                        subgoals.push(result);
                    }
                }
                Ok(
                    number_in_set_verified_by_builtin_rules_result_with_subgoals(
                        in_fact,
                        "matrix literal: shape matches matrix(...) and each entry in co-domain",
                        subgoals,
                    ),
                )
            }
            (_, Obj::FiniteSeqSet(fs)) => {
                let fn_set = self.finite_seq_set_to_fn_set(fs, in_fact.line_file.clone());
                let expanded = InFact::new(
                    in_fact.element.clone(),
                    fn_set.into(),
                    in_fact.line_file.clone(),
                );
                self.verify_builtin_rule_premise(&expanded.into(), builtin_state)
            }
            (_, Obj::SeqSet(ss)) => {
                let fn_set = self.seq_set_to_fn_set(ss, in_fact.line_file.clone());
                let expanded = InFact::new(
                    in_fact.element.clone(),
                    fn_set.into(),
                    in_fact.line_file.clone(),
                );
                self.verify_builtin_rule_premise(&expanded.into(), builtin_state)
            }
            (_, Obj::MatrixSet(ms)) => {
                let fn_set = self.matrix_set_to_fn_set(ms, in_fact.line_file.clone());
                let expanded = InFact::new(
                    in_fact.element.clone(),
                    fn_set.into(),
                    in_fact.line_file.clone(),
                );
                self.verify_builtin_rule_premise(&expanded.into(), builtin_state)
            }
            (_, target_set_obj) => {
                let literal_tuple_projection_result = self
                    .verify_in_fact_literal_tuple_projection_in_set(
                        in_fact,
                        target_set_obj,
                        builtin_state,
                    )?;
                if literal_tuple_projection_result.is_true() {
                    return Ok(literal_tuple_projection_result);
                }
                let finite_seq_literal_application_result = self
                    .verify_in_fact_finite_seq_literal_application_in_set(
                        in_fact,
                        target_set_obj,
                        builtin_state,
                    )?;
                if finite_seq_literal_application_result.is_true() {
                    return Ok(finite_seq_literal_application_result);
                }
                let cart_projection_result = self
                    .verify_in_fact_obj_at_index_in_standard_set_by_cart_factor_list_set(
                        in_fact,
                        target_set_obj,
                        builtin_state,
                    )?;
                if cart_projection_result.is_true() {
                    return Ok(cart_projection_result);
                }
                if let Obj::FnObj(fn_obj) = &in_fact.element {
                    let fn_try = self.verify_in_fact_fn_application_in_typed_return_set(
                        fn_obj,
                        in_fact,
                        builtin_state,
                    )?;
                    if fn_try.is_true() {
                        return Ok(fn_try);
                    }
                }
                let list_set_carrier_result =
                    self.verify_in_fact_by_known_list_set_carrier(in_fact, builtin_state)?;
                if list_set_carrier_result.is_true() {
                    return Ok(list_set_carrier_result);
                }
                self.verify_in_fact_by_known_standard_subset_membership(in_fact, target_set_obj)
            }
        }
    }
}
