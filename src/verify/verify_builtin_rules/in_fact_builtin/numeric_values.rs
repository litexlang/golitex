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

pub(super) fn number_in_set_verified_by_builtin_rules_result_with_subgoals(
    in_fact: &InFact,
    reason: &str,
    subgoals: Vec<StmtResult>,
) -> StmtResult {
    StmtResult::from(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            reason.to_string(),
            subgoals,
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

pub(crate) fn builtin_in_fact_result_for_evaluated_number_in_standard_set(
    in_fact: &InFact,
    evaluated_number: &Number,
    standard_set: &StandardSet,
) -> StmtResult {
    match standard_set {
        StandardSet::C => number_in_set_verified_by_builtin_rules_result(in_fact, "number in C"),
        StandardSet::CStar => {
            if number_is_in_c_star(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in C*")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::R => number_in_set_verified_by_builtin_rules_result(in_fact, "number in R"),
        StandardSet::RPos => {
            if number_is_in_r_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R+")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::RNeg => {
            if number_is_in_r_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R-")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::RStar => {
            if number_is_in_r_star(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R*")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::Q => number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q"),
        StandardSet::QPos => {
            if number_is_in_q_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q+")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::QNeg => {
            if number_is_in_q_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q-")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::QStar => {
            if number_is_in_q_star(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q*")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::Z => {
            if number_is_in_z(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::ZNeg => {
            if number_is_in_z_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z-")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::ZStar => {
            if number_is_in_z_star(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z*")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::N => {
            if number_is_in_n(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::NPos => {
            if number_is_in_n_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N+")
            } else {
                StmtUnknown::new().into()
            }
        }
    }
}

pub(crate) fn builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
    not_in_fact: &NotInFact,
    evaluated_number: &Number,
    standard_set: &StandardSet,
) -> StmtResult {
    match standard_set {
        StandardSet::C | StandardSet::R | StandardSet::Q => StmtUnknown::new().into(),
        StandardSet::CStar => {
            if !number_is_in_c_star(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in C*")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::RPos => {
            if !number_is_in_r_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R+")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::RNeg => {
            if !number_is_in_r_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R-")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::RStar => {
            if !number_is_in_r_star(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R*")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::QPos => {
            if !number_is_in_q_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q+")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::QNeg => {
            if !number_is_in_q_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q-")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::QStar => {
            if !number_is_in_q_star(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q*")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::Z => {
            if !number_is_in_z(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::ZNeg => {
            if !number_is_in_z_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z-")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::ZStar => {
            if !number_is_in_z_star(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z*")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::N => {
            if !number_is_in_n(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in N")
            } else {
                StmtUnknown::new().into()
            }
        }
        StandardSet::NPos => {
            if !number_is_in_n_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in N+")
            } else {
                StmtUnknown::new().into()
            }
        }
    }
}
