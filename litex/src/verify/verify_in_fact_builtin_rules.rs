use crate::prelude::*;
use crate::verify::verify_number_in_standard_set::{
    number_is_in_n, number_is_in_n_pos, number_is_in_q_neg, number_is_in_q_nz, number_is_in_q_pos,
    number_is_in_r_neg, number_is_in_r_nz, number_is_in_r_pos, number_is_in_z, number_is_in_z_neg,
    number_is_in_z_nz,
};

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
            (Obj::Number(_), Obj::RObj(_)) => Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "number in R",
            )),
            (Obj::Number(num), Obj::RPos(_)) => {
                if number_is_in_r_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in R_pos",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::RNeg(_)) => {
                if number_is_in_r_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in R_neg",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::RNz(_)) => {
                if number_is_in_r_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in R_nz",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(_), Obj::QObj(_)) => Ok(number_in_set_verified_by_builtin_rules_result(
                in_fact,
                "number in Q",
            )),
            (Obj::Number(num), Obj::QPos(_)) => {
                if number_is_in_q_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Q_pos",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::QNeg(_)) => {
                if number_is_in_q_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Q_neg",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::QNz(_)) => {
                if number_is_in_q_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Q_nz",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::ZObj(_)) => {
                if number_is_in_z(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Z",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::ZNeg(_)) => {
                if number_is_in_z_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Z_neg",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::ZNz(_)) => {
                if number_is_in_z_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in Z_nz",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::NObj(_)) => {
                if number_is_in_n(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        in_fact,
                        "number in N",
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::NPosObj(_)) => {
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
                Obj::RObj(_),
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
            Obj::NPosObj(_) => Some(vec![]),
            Obj::NObj(_) => Some(vec![Obj::NPosObj(crate::obj::NPosObj::new())]),
            Obj::ZNeg(_) => Some(vec![]),
            Obj::ZNz(_) => Some(vec![
                Obj::NPosObj(crate::obj::NPosObj::new()),
                Obj::ZNeg(crate::obj::ZNeg::new()),
            ]),
            Obj::ZObj(_) => Some(vec![
                Obj::NPosObj(crate::obj::NPosObj::new()),
                Obj::NObj(crate::obj::NObj::new()),
                Obj::ZNeg(crate::obj::ZNeg::new()),
                Obj::ZNz(crate::obj::ZNz::new()),
            ]),
            Obj::QPos(_) => Some(vec![Obj::NPosObj(crate::obj::NPosObj::new())]),
            Obj::QNeg(_) => Some(vec![Obj::ZNeg(crate::obj::ZNeg::new())]),
            Obj::QNz(_) => Some(vec![
                Obj::NPosObj(crate::obj::NPosObj::new()),
                Obj::ZNeg(crate::obj::ZNeg::new()),
                Obj::ZNz(crate::obj::ZNz::new()),
                Obj::QPos(crate::obj::QPos::new()),
                Obj::QNeg(crate::obj::QNeg::new()),
            ]),
            Obj::QObj(_) => Some(vec![
                Obj::NPosObj(crate::obj::NPosObj::new()),
                Obj::NObj(crate::obj::NObj::new()),
                Obj::ZNeg(crate::obj::ZNeg::new()),
                Obj::ZNz(crate::obj::ZNz::new()),
                Obj::ZObj(crate::obj::ZObj::new()),
                Obj::QPos(crate::obj::QPos::new()),
                Obj::QNeg(crate::obj::QNeg::new()),
                Obj::QNz(crate::obj::QNz::new()),
            ]),
            Obj::RPos(_) => Some(vec![
                Obj::NPosObj(crate::obj::NPosObj::new()),
                Obj::QPos(crate::obj::QPos::new()),
            ]),
            Obj::RNeg(_) => Some(vec![
                Obj::ZNeg(crate::obj::ZNeg::new()),
                Obj::QNeg(crate::obj::QNeg::new()),
            ]),
            Obj::RNz(_) => Some(vec![
                Obj::NPosObj(crate::obj::NPosObj::new()),
                Obj::ZNeg(crate::obj::ZNeg::new()),
                Obj::ZNz(crate::obj::ZNz::new()),
                Obj::QPos(crate::obj::QPos::new()),
                Obj::QNeg(crate::obj::QNeg::new()),
                Obj::QNz(crate::obj::QNz::new()),
                Obj::RPos(crate::obj::RPos::new()),
                Obj::RNeg(crate::obj::RNeg::new()),
            ]),
            Obj::RObj(_) => Some(vec![
                Obj::NPosObj(crate::obj::NPosObj::new()),
                Obj::NObj(crate::obj::NObj::new()),
                Obj::ZNeg(crate::obj::ZNeg::new()),
                Obj::ZNz(crate::obj::ZNz::new()),
                Obj::ZObj(crate::obj::ZObj::new()),
                Obj::QPos(crate::obj::QPos::new()),
                Obj::QNeg(crate::obj::QNeg::new()),
                Obj::QNz(crate::obj::QNz::new()),
                Obj::QObj(crate::obj::QObj::new()),
                Obj::RPos(crate::obj::RPos::new()),
                Obj::RNeg(crate::obj::RNeg::new()),
                Obj::RNz(crate::obj::RNz::new()),
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
