use crate::prelude::*;

fn number_in_set_verified_by_builtin_rules_result(
    in_fact: &InFact,
    reason: &str,
) -> NonErrStmtExecResult {
    NonErrStmtExecResult::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(
        Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
        reason.to_string(),
        InferResult::new(),
    ))
}

fn arithmetic_obj_in_r_verified_by_builtin_rules_result(in_fact: &InFact) -> NonErrStmtExecResult {
    NonErrStmtExecResult::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(
        Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
        "arithmetic expression is in R".to_string(),
        InferResult::new(),
    ))
}

impl Runtime {
    pub fn verify_in_fact_with_builtin_rules(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match (&in_fact.element, &in_fact.set) {
            (Obj::Tuple(tuple), Obj::Cart(cart)) => {
                return self.verify_in_fact_by_left_is_tuple_right_is_cart(
                    in_fact,
                    tuple,
                    cart,
                    verify_state,
                );
            }
            (Obj::Number(_), Obj::StandardSet { standard_set: StandardSet::R }) => Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "number in R",
            )),
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::RPos }) => {
                if number_is_in_r_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in R_pos",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::RNeg }) => {
                if number_is_in_r_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in R_neg",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::RNz }) => {
                if number_is_in_r_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in R_nz",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(_), Obj::StandardSet { standard_set: StandardSet::Q }) => Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "number in Q",
            )),
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::QPos }) => {
                if number_is_in_q_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Q_pos",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::QNeg }) => {
                if number_is_in_q_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Q_neg",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::QNz }) => {
                if number_is_in_q_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Q_nz",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::Z }) => {
                if number_is_in_z(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Z",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::ZNeg }) => {
                if number_is_in_z_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Z_neg",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::ZNz }) => {
                if number_is_in_z_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Z_nz",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::N }) => {
                if number_is_in_n(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in N",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::StandardSet { standard_set: StandardSet::NPos }) => {
                if number_is_in_n_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in N_pos",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::StandardSet { standard_set: StandardSet::R },
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
                return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                    FactVerifiedByBuiltinRules::new(
                        Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                        format!(
                            "{} equals one element in list_set {}",
                            in_fact.element, in_fact.set
                        ),
                        InferResult::new(),
                    ),
                ));
            }
        }
        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn standard_subset_set_objs_for_target_set(target_set_obj: &Obj) -> Option<Vec<Obj>> {
        match target_set_obj {
            Obj::StandardSet { standard_set: StandardSet::NPos } => Some(vec![]),
            Obj::StandardSet { standard_set: StandardSet::N } => Some(vec![Obj::StandardSet { standard_set: StandardSet::NPos }]),
            Obj::StandardSet { standard_set: StandardSet::ZNeg } => Some(vec![]),
            Obj::StandardSet { standard_set: StandardSet::ZNz } => Some(vec![
                Obj::StandardSet { standard_set: StandardSet::NPos },
                Obj::StandardSet { standard_set: StandardSet::ZNeg },
            ]),
            Obj::StandardSet { standard_set: StandardSet::Z } => Some(vec![
                Obj::StandardSet { standard_set: StandardSet::NPos },
                Obj::StandardSet { standard_set: StandardSet::N },
                Obj::StandardSet { standard_set: StandardSet::ZNeg },
                Obj::StandardSet { standard_set: StandardSet::ZNz },
            ]),
            Obj::StandardSet { standard_set: StandardSet::QPos } => Some(vec![Obj::StandardSet { standard_set: StandardSet::NPos }]),
            Obj::StandardSet { standard_set: StandardSet::QNeg } => Some(vec![Obj::StandardSet { standard_set: StandardSet::ZNeg }]),
            Obj::StandardSet { standard_set: StandardSet::QNz } => Some(vec![
                Obj::StandardSet { standard_set: StandardSet::NPos },
                Obj::StandardSet { standard_set: StandardSet::ZNeg },
                Obj::StandardSet { standard_set: StandardSet::ZNz },
                Obj::StandardSet { standard_set: StandardSet::QPos },
                Obj::StandardSet { standard_set: StandardSet::QNeg },
            ]),
            Obj::StandardSet { standard_set: StandardSet::Q } => Some(vec![
                Obj::StandardSet { standard_set: StandardSet::NPos },
                Obj::StandardSet { standard_set: StandardSet::N },
                Obj::StandardSet { standard_set: StandardSet::ZNeg },
                Obj::StandardSet { standard_set: StandardSet::ZNz },
                Obj::StandardSet { standard_set: StandardSet::Z },
                Obj::StandardSet { standard_set: StandardSet::QPos },
                Obj::StandardSet { standard_set: StandardSet::QNeg },
                Obj::StandardSet { standard_set: StandardSet::QNz },
            ]),
            Obj::StandardSet { standard_set: StandardSet::RPos } => Some(vec![
                Obj::StandardSet { standard_set: StandardSet::NPos },
                Obj::StandardSet { standard_set: StandardSet::QPos },
            ]),
            Obj::StandardSet { standard_set: StandardSet::RNeg } => Some(vec![
                Obj::StandardSet { standard_set: StandardSet::ZNeg },
                Obj::StandardSet { standard_set: StandardSet::QNeg },
            ]),
            Obj::StandardSet { standard_set: StandardSet::RNz } => Some(vec![
                Obj::StandardSet { standard_set: StandardSet::NPos },
                Obj::StandardSet { standard_set: StandardSet::ZNeg },
                Obj::StandardSet { standard_set: StandardSet::ZNz },
                Obj::StandardSet { standard_set: StandardSet::QPos },
                Obj::StandardSet { standard_set: StandardSet::QNeg },
                Obj::StandardSet { standard_set: StandardSet::QNz },
                Obj::StandardSet { standard_set: StandardSet::RPos },
                Obj::StandardSet { standard_set: StandardSet::RNeg },
            ]),
            Obj::StandardSet { standard_set: StandardSet::R } => Some(vec![
                Obj::StandardSet { standard_set: StandardSet::NPos },
                Obj::StandardSet { standard_set: StandardSet::N },
                Obj::StandardSet { standard_set: StandardSet::ZNeg },
                Obj::StandardSet { standard_set: StandardSet::ZNz },
                Obj::StandardSet { standard_set: StandardSet::Z },
                Obj::StandardSet { standard_set: StandardSet::QPos },
                Obj::StandardSet { standard_set: StandardSet::QNeg },
                Obj::StandardSet { standard_set: StandardSet::QNz },
                Obj::StandardSet { standard_set: StandardSet::Q },
                Obj::StandardSet { standard_set: StandardSet::RPos },
                Obj::StandardSet { standard_set: StandardSet::RNeg },
                Obj::StandardSet { standard_set: StandardSet::RNz },
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
                return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                    FactVerifiedByBuiltinRules::new(
                        Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                        format!(
                            "{} in {} implies in {} (standard subset relation)",
                            in_fact.element, standard_subset_set_obj, target_set_obj
                        ),
                        InferResult::new(),
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

        Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
            FactVerifiedByBuiltinRules::new(
                Fact::AtomicFact(AtomicFact::InFact(in_fact.clone())),
                "tuple in cart: each component is in the corresponding cart factor".to_string(),
                InferResult::new(),
            ),
        ))
    }
}
