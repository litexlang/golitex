use super::*;

pub(super) fn number_in_set_verified_by_builtin_rules_result(
    in_fact: &InFact,
    reason: &str,
) -> StmtResult {
    StmtResult::from(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

pub(super) fn not_in_fact_verified_by_builtin_rules_result(
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

pub(super) fn arithmetic_obj_in_r_verified_by_builtin_rules_result(in_fact: &InFact) -> StmtResult {
    StmtResult::from(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            "arithmetic expression is in R".to_string(),
            Vec::new(),
        ),
    )
}

pub(super) fn builtin_in_fact_result_for_evaluated_number_in_standard_set(
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

pub(super) fn builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
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
