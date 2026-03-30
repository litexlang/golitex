use crate::prelude::*;

fn number_in_set_verified_by_builtin_rules_result(
    in_fact: &InFact,
    reason: &str,
) -> NonErrStmtExecResult {
    NonErrStmtExecResult::FactualStmtSuccess(FactualStmtSuccess::new_with_verified_by_builtin_rules(
        Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
        InferResult::new(),
        reason.to_string(),
        Vec::new(),
    ))
}

fn arithmetic_obj_in_r_verified_by_builtin_rules_result(in_fact: &InFact) -> NonErrStmtExecResult {
    NonErrStmtExecResult::FactualStmtSuccess(FactualStmtSuccess::new_with_verified_by_builtin_rules(
        Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
        InferResult::new(),
        "arithmetic expression is in R".to_string(),
        Vec::new(),
    ))
}

fn builtin_in_fact_result_for_evaluated_number_in_standard_set(
    in_fact: &InFact,
    evaluated_number: &Number,
    standard_set: &StandardSet,
) -> NonErrStmtExecResult {
    match standard_set {
        StandardSet::R => {
            number_in_set_verified_by_builtin_rules_result(in_fact, "number in R")
        }
        StandardSet::RPos => {
            if number_is_in_r_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_pos")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::RNeg => {
            if number_is_in_r_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_neg")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::RNz => {
            if number_is_in_r_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R_nz")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::Q => {
            number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q")
        }
        StandardSet::QPos => {
            if number_is_in_q_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_pos")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QNeg => {
            if number_is_in_q_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_neg")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::QNz => {
            if number_is_in_q_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q_nz")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::Z => {
            if number_is_in_z(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNeg => {
            if number_is_in_z_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z_neg")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::ZNz => {
            if number_is_in_z_nz(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z_nz")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::N => {
            if number_is_in_n(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
        StandardSet::NPos => {
            if number_is_in_n_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N_pos")
            } else {
                NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())
            }
        }
    }
}

impl Runtime {
    pub fn verify_in_fact_with_builtin_rules(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
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
                    return Ok(evaluation_membership_result);
                }
            }
        }
        match (&in_fact.element, &in_fact.set) {
            (Obj::Tuple(tuple), Obj::Cart(cart)) => {
                return self.verify_in_fact_by_left_is_tuple_right_is_cart(
                    in_fact,
                    tuple,
                    cart,
                    verify_state,
                );
            }
            (Obj::Number(num), Obj::StandardSet(standard_set)) => Ok(
                builtin_in_fact_result_for_evaluated_number_in_standard_set(
                    in_fact,
                    num,
                    standard_set,
                ),
            ),
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
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet(StandardSet::R),
            ) => Ok(arithmetic_obj_in_r_verified_by_builtin_rules_result(
                in_fact,
            )),
            (_, Obj::ListSet(list_set)) => self.verify_in_fact_by_equal_to_one_element_in_list_set(
                in_fact,
                list_set,
                verify_state,
            ),
            (_, target_set_obj) => {
                self.verify_in_fact_by_known_standard_subset_membership(in_fact, target_set_obj)
            }
        }
    }

    fn verify_in_fact_arithmetic_expression_in_standard_negative_set(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
        target_negative_standard_set: StandardSet,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(evaluated_number) = in_fact.element.evaluate_to_normalized_decimal_number() {
            return Ok(builtin_in_fact_result_for_evaluated_number_in_standard_set(
                in_fact,
                &evaluated_number,
                &target_negative_standard_set,
            ));
        }
        let mul = match &in_fact.element {
            Obj::Mul(mul) => mul,
            _ => return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        };
        let product_in_r_fact = AtomicFact::InFact(InFact::new(
            in_fact.element.clone(),
            Obj::StandardSet(StandardSet::R),
            in_fact.line_file,
        ));
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &product_in_r_fact,
            verify_state,
        )? {
            return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
        }
        if !self.mul_product_negative_when_factors_have_strict_opposite_sign_by_non_equational_verify(
            &mul.left,
            &mul.right,
            in_fact.line_file,
            verify_state,
        )? {
            return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
        }
        match target_negative_standard_set {
            StandardSet::RNeg => Ok(NonErrStmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules(
                    Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                    InferResult::new(),
                    "mul_opposite_signs_product_in_R_neg".to_string(),
                    Vec::new(),
                ),
            )),
            StandardSet::QNeg => {
                let product_in_q_fact = AtomicFact::InFact(InFact::new(
                    in_fact.element.clone(),
                    Obj::StandardSet(StandardSet::Q),
                    in_fact.line_file,
                ));
                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &product_in_q_fact,
                    verify_state,
                )? {
                    Ok(NonErrStmtExecResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules(
                            Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                            InferResult::new(),
                            "mul_opposite_signs_product_in_Q_neg".to_string(),
                            Vec::new(),
                        ),
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            StandardSet::ZNeg => {
                let product_in_z_fact = AtomicFact::InFact(InFact::new(
                    in_fact.element.clone(),
                    Obj::StandardSet(StandardSet::Z),
                    in_fact.line_file,
                ));
                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &product_in_z_fact,
                    verify_state,
                )? {
                    Ok(NonErrStmtExecResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules(
                            Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                            InferResult::new(),
                            "mul_opposite_signs_product_in_Z_neg".to_string(),
                            Vec::new(),
                        ),
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    fn verify_in_fact_by_equal_to_one_element_in_list_set(
        &mut self,
        in_fact: &InFact,
        list_set: &crate::obj::ListSet,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        for current_element_in_list_set in list_set.list.iter() {
            let equal_fact = AtomicFact::EqualFact(EqualFact::new(
                in_fact.element.clone(),
                *current_element_in_list_set.clone(),
                in_fact.line_file,
            ));
            let equal_fact_verify_result = self.verify_atomic_fact(&equal_fact, verify_state)?;
            if equal_fact_verify_result.is_true() {
                return Ok(NonErrStmtExecResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules(
                        Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                        InferResult::new(),
                        format!(
                            "{} equals one element in list_set {}",
                            in_fact.element, in_fact.set
                        ),
                        Vec::new(),
                    ),
                ));
            }
        }
        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn standard_subset_set_objs_for_target_set(target_set_obj: &Obj) -> Option<Vec<Obj>> {
        match target_set_obj {
            Obj::StandardSet(StandardSet::NPos) => Some(vec![]),
            Obj::StandardSet(StandardSet::N) => Some(vec![Obj::StandardSet(StandardSet::NPos)]),
            Obj::StandardSet(StandardSet::ZNeg) => Some(vec![]),
            Obj::StandardSet(StandardSet::ZNz) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::ZNeg),
            ]),
            Obj::StandardSet(StandardSet::Z) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::N),
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::ZNz),
            ]),
            Obj::StandardSet(StandardSet::QPos) => Some(vec![Obj::StandardSet(StandardSet::NPos)]),
            Obj::StandardSet(StandardSet::QNeg) => Some(vec![Obj::StandardSet(StandardSet::ZNeg)]),
            Obj::StandardSet(StandardSet::QNz) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::ZNz),
                Obj::StandardSet(StandardSet::QPos),
                Obj::StandardSet(StandardSet::QNeg),
            ]),
            Obj::StandardSet(StandardSet::Q) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::N),
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::ZNz),
                Obj::StandardSet(StandardSet::Z),
                Obj::StandardSet(StandardSet::QPos),
                Obj::StandardSet(StandardSet::QNeg),
                Obj::StandardSet(StandardSet::QNz),
            ]),
            Obj::StandardSet(StandardSet::RPos) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::QPos),
            ]),
            Obj::StandardSet(StandardSet::RNeg) => Some(vec![
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::QNeg),
            ]),
            Obj::StandardSet(StandardSet::RNz) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::ZNz),
                Obj::StandardSet(StandardSet::QPos),
                Obj::StandardSet(StandardSet::QNeg),
                Obj::StandardSet(StandardSet::QNz),
                Obj::StandardSet(StandardSet::RPos),
                Obj::StandardSet(StandardSet::RNeg),
            ]),
            Obj::StandardSet(StandardSet::R) => Some(vec![
                Obj::StandardSet(StandardSet::NPos),
                Obj::StandardSet(StandardSet::N),
                Obj::StandardSet(StandardSet::ZNeg),
                Obj::StandardSet(StandardSet::ZNz),
                Obj::StandardSet(StandardSet::Z),
                Obj::StandardSet(StandardSet::QPos),
                Obj::StandardSet(StandardSet::QNeg),
                Obj::StandardSet(StandardSet::QNz),
                Obj::StandardSet(StandardSet::Q),
                Obj::StandardSet(StandardSet::RPos),
                Obj::StandardSet(StandardSet::RNeg),
                Obj::StandardSet(StandardSet::RNz),
            ]),
            _ => None,
        }
    }

    fn verify_in_fact_by_known_standard_subset_membership(
        &mut self,
        in_fact: &InFact,
        target_set_obj: &Obj,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let standard_subset_set_objs =
            match Self::standard_subset_set_objs_for_target_set(target_set_obj) {
                Some(standard_subset_set_objs) => standard_subset_set_objs,
                None => return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
            };
        for standard_subset_set_obj in standard_subset_set_objs.iter() {
            let in_fact_into_standard_subset = AtomicFact::InFact(InFact::new(
                in_fact.element.clone(),
                standard_subset_set_obj.clone(),
                in_fact.line_file,
            ));
            let verify_result = self
                .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                    &in_fact_into_standard_subset,
                )?;
            if verify_result.is_true() {
                return Ok(NonErrStmtExecResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules(
                        Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                        InferResult::new(),
                        format!(
                            "{} in {} implies in {} (standard subset relation)",
                            in_fact.element, standard_subset_set_obj, target_set_obj
                        ),
                        Vec::new(),
                    ),
                ));
            }
        }
        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_in_fact_by_left_is_tuple_right_is_cart(
        &mut self,
        in_fact: &InFact,
        tuple: &Tuple,
        cart: &Cart,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if tuple.args.len() != cart.args.len() {
            return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
        }

        for component_index in 0..tuple.args.len() {
            let tuple_component_obj = (*tuple.args[component_index]).clone();
            let cart_component_obj = (*cart.args[component_index]).clone();
            let component_in_fact = AtomicFact::InFact(InFact::new(
                tuple_component_obj,
                cart_component_obj,
                in_fact.line_file,
            ));
            let component_verify_result =
                self.verify_atomic_fact(&component_in_fact, verify_state)?;
            if !component_verify_result.is_true() {
                return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
            }
        }

        Ok(NonErrStmtExecResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules(
                Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                InferResult::new(),
                "tuple in cart: each component is in the corresponding cart factor".to_string(),
                Vec::new(),
            ),
        ))
    }
}
