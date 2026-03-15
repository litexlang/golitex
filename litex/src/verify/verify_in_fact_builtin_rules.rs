use crate::fact::InFact;
use crate::error::VerifyError;
use crate::execute::Executor;
use crate::common::keywords::{N, N_POS, Q, Q_NEG, Q_NZ, Q_POS, R, R_NEG, R_NZ, R_POS, Z, Z_NEG, Z_NZ, Z_POS};
use crate::obj::Obj;
use crate::result::NonErrStmtResult;
use crate::result::FactVerifiedByBuiltinRules;
use crate::result::StmtUnknown;
use crate::verify::VerifyState;
use crate::verify::verify_number_in_standard_set::{
    number_is_in_n, number_is_in_n_pos, number_is_in_q_neg, number_is_in_q_nz, number_is_in_q_pos,
    number_is_in_r_neg, number_is_in_r_nz, number_is_in_r_pos,
    number_is_in_z, number_is_in_z_neg, number_is_in_z_nz, number_is_in_z_pos,
};

fn number_in_set_verified_by_builtin_rules_result(num_value: &str, set_name: &str, reason: &str, line_file_index: Option<(usize, usize)>) -> NonErrStmtResult {
    NonErrStmtResult::FactVerifiedByBuiltinRules(
        FactVerifiedByBuiltinRules::new(format!("{} in {}", num_value, set_name), reason.to_string(), line_file_index),
    )
}

impl<'a> Executor<'a> {
    pub fn verify_in_fact_with_builtin_rules(&mut self, in_fact: &InFact, _verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        match (&in_fact.element, &in_fact.set) {
            (Obj::Number(num), Obj::RObj(_)) => Ok(number_in_set_verified_by_builtin_rules_result(&num.value, R, "number in R", in_fact.line_file_index)),
            (Obj::Number(num), Obj::RPos(_)) => {
                if number_is_in_r_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, R_POS, "number in R_pos", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::RNeg(_)) => {
                if number_is_in_r_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, R_NEG, "number in R_neg", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::RNz(_)) => {
                if number_is_in_r_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, R_NZ, "number in R_nz", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::QObj(_)) => Ok(number_in_set_verified_by_builtin_rules_result(&num.value, Q, "number in Q", in_fact.line_file_index)),
            (Obj::Number(num), Obj::QPos(_)) => {
                if number_is_in_q_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, Q_POS, "number in Q_pos", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::QNeg(_)) => {
                if number_is_in_q_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, Q_NEG, "number in Q_neg", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::QNz(_)) => {
                if number_is_in_q_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, Q_NZ, "number in Q_nz", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::ZObj(_)) => {
                if number_is_in_z(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, Z, "number in Z", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::ZPos(_)) => {
                if number_is_in_z_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, Z_POS, "number in Z_pos", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::ZNeg(_)) => {
                if number_is_in_z_neg(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, Z_NEG, "number in Z_neg", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::ZNz(_)) => {
                if number_is_in_z_nz(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, Z_NZ, "number in Z_nz", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::NObj(_)) => {
                if number_is_in_n(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, N, "number in N", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            (Obj::Number(num), Obj::NPosObj(_)) => {
                if number_is_in_n_pos(num) {
                    Ok(number_in_set_verified_by_builtin_rules_result(&num.value, N_POS, "number in N_pos", in_fact.line_file_index))
                } else {
                    Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
                }
            }
            _ => Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new())),
        }
    }
}