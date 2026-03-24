use crate::common::keywords::{
    FACT_PREFIX, IN, N, N_POS, Q, Q_NEG, Q_NZ, Q_POS, R, R_NEG, R_NZ, R_POS, Z, Z_NEG, Z_NZ,
};
use crate::error::VerifyError;
use crate::execute::Runtime;
use crate::fact::AtomicFact;
use crate::fact::InFact;
use crate::fact::EqualFact;
use crate::infer::InferResult;
use crate::obj::Obj;
use crate::result::FactVerifiedByBuiltinRules;
use crate::result::NonErrStmtExecResult;
use crate::result::StmtUnknown;
use crate::verify::verify_number_in_standard_set::{
    number_is_in_n, number_is_in_n_pos, number_is_in_q_neg, number_is_in_q_nz, number_is_in_q_pos,
    number_is_in_r_neg, number_is_in_r_nz, number_is_in_r_pos, number_is_in_z, number_is_in_z_neg,
    number_is_in_z_nz,
};
use crate::verify::VerifyState;

fn number_in_set_verified_by_builtin_rules_result(
    num_value: &str,
    set_name: &str,
    reason: &str,
    line_file: (usize, usize),
) -> NonErrStmtExecResult {
    NonErrStmtExecResult::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(
        format!("{} in {}", num_value, set_name),
        reason.to_string(),
        InferResult::new(),
        line_file,
    ))
}

fn arithmetic_obj_in_r_verified_by_builtin_rules_result(
    obj: &Obj,
    line_file: (usize, usize),
) -> NonErrStmtExecResult {
    NonErrStmtExecResult::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(
        format!("{} {}{} {}", obj, FACT_PREFIX, IN, R),
        "arithmetic expression is in R".to_string(),
        InferResult::new(),
        line_file,
    ))
}

impl<'a> Runtime<'a> {
    pub fn verify_in_fact_with_builtin_rules(
        &mut self,
        in_fact: &InFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match (&in_fact.element, &in_fact.set) {
            (Obj::Number(num), Obj::RObj(_)) => Ok(number_in_set_verified_by_builtin_rules_result(
                &num.normalized_value,
                R,
                "number in R",
                in_fact.line_file,
            )),
            (Obj::Number(num), Obj::RPos(_)) => {
                if number_is_in_r_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        R_POS,
                        "number in R_pos",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::RNeg(_)) => {
                if number_is_in_r_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        R_NEG,
                        "number in R_neg",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::RNz(_)) => {
                if number_is_in_r_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        R_NZ,
                        "number in R_nz",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::QObj(_)) => Ok(number_in_set_verified_by_builtin_rules_result(
                &num.normalized_value,
                Q,
                "number in Q",
                in_fact.line_file,
            )),
            (Obj::Number(num), Obj::QPos(_)) => {
                if number_is_in_q_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        Q_POS,
                        "number in Q_pos",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::QNeg(_)) => {
                if number_is_in_q_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        Q_NEG,
                        "number in Q_neg",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::QNz(_)) => {
                if number_is_in_q_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        Q_NZ,
                        "number in Q_nz",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::ZObj(_)) => {
                if number_is_in_z(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        Z,
                        "number in Z",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::ZNeg(_)) => {
                if number_is_in_z_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        Z_NEG,
                        "number in Z_neg",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::ZNz(_)) => {
                if number_is_in_z_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        Z_NZ,
                        "number in Z_nz",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::NObj(_)) => {
                if number_is_in_n(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        N,
                        "number in N",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::NPosObj(_)) => {
                if number_is_in_n_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(
                        &num.normalized_value,
                        N_POS,
                        "number in N_pos",
                        in_fact.line_file,
                    ))
                } else {
                    Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (
                Obj::Add(_) | Obj::Sub(_) | Obj::Mul(_) | Obj::Div(_) | Obj::Mod(_) | Obj::Pow(_),
                Obj::RObj(_),
            ) => Ok(arithmetic_obj_in_r_verified_by_builtin_rules_result(
                &in_fact.element,
                in_fact.line_file,
            )),
            (_, Obj::ListSet(list_set)) => {
                self.verify_in_fact_by_equal_to_one_element_in_list_set(in_fact, list_set, verify_state)
            }
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
                        format!("{} {}{} {}", in_fact.element, FACT_PREFIX, IN, in_fact.set),
                        format!(
                            "{} equals one element in list_set {}",
                            in_fact.element, in_fact.set
                        ),
                        InferResult::new(),
                        in_fact.line_file,
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
        let standard_subset_set_objs = match Self::standard_subset_set_objs_for_target_set(target_set_obj)
        {
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
                        format!("{} {}{} {}", in_fact.element, FACT_PREFIX, IN, target_set_obj),
                        format!(
                            "{} in {} implies in {} (standard subset relation)",
                            in_fact.element, standard_subset_set_obj, target_set_obj
                        ),
                        InferResult::new(),
                        in_fact.line_file,
                    ),
                ));
            }
        }
        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }
}
