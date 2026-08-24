use super::*;

pub(super) fn number_in_set_verified_by_builtin_rules_result(
    in_fact: &InFact,
    reason: &str,
) -> StmtResult {
    StmtResult::from(
        SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
            in_fact.clone().into(),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

pub(super) fn number_in_set_verified_by_evaluation_result(
    in_fact: &InFact,
    reason: &str,
    target_set: &StandardSet,
    evaluation: &SuccessEvaluateObjResult,
) -> StmtResult {
    SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
        in_fact.clone().into(),
        reason.to_string(),
        BuiltinRuleEvidence::ClosedNumericMembership(
            ClosedNumericMembershipBuiltinRuleEvidence::new(
                in_fact.clone().into(),
                target_set.clone(),
                evaluation.clone(),
            ),
        ),
        Vec::new(),
    )
    .into()
}

pub(super) fn number_in_set_verified_by_builtin_rules_result_with_subgoals(
    in_fact: &InFact,
    reason: &str,
    subgoals: Vec<StmtResult>,
) -> StmtResult {
    StmtResult::from(
        SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
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
        SuccessFactStmtResult::new_with_verified_by_builtin_rules_recording_stmt(
            not_in_fact.clone().into(),
            reason.to_string(),
            Vec::new(),
        ),
    )
}

pub(super) fn number_not_in_set_verified_by_evaluation_result(
    not_in_fact: &NotInFact,
    reason: &str,
    target_set: &StandardSet,
    evaluation: &SuccessEvaluateObjResult,
) -> StmtResult {
    SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
        not_in_fact.clone().into(),
        reason.to_string(),
        BuiltinRuleEvidence::ClosedNumericNonmembership(
            ClosedNumericNonmembershipBuiltinRuleEvidence::new(
                not_in_fact.clone().into(),
                target_set.clone(),
                evaluation.clone(),
            ),
        ),
        Vec::new(),
    )
    .into()
}

pub fn builtin_in_fact_result_for_evaluation_in_standard_set(
    in_fact: &InFact,
    evaluation: &SuccessEvaluateObjResult,
    standard_set: &StandardSet,
) -> StmtResult {
    let evaluated_number = &evaluation.value;
    match standard_set {
        StandardSet::C => number_in_set_verified_by_evaluation_result(
            in_fact,
            "number in C",
            standard_set,
            evaluation,
        ),
        StandardSet::CStar if number_is_in_c_star(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in C*",
                standard_set,
                evaluation,
            )
        }
        StandardSet::R => number_in_set_verified_by_evaluation_result(
            in_fact,
            "number in R",
            standard_set,
            evaluation,
        ),
        StandardSet::RPos if number_is_in_r_pos(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in R+",
                standard_set,
                evaluation,
            )
        }
        StandardSet::RNeg if number_is_in_r_neg(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in R-",
                standard_set,
                evaluation,
            )
        }
        StandardSet::RStar if number_is_in_r_star(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in R*",
                standard_set,
                evaluation,
            )
        }
        StandardSet::Q => number_in_set_verified_by_evaluation_result(
            in_fact,
            "number in Q",
            standard_set,
            evaluation,
        ),
        StandardSet::QPos if number_is_in_q_pos(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in Q+",
                standard_set,
                evaluation,
            )
        }
        StandardSet::QNeg if number_is_in_q_neg(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in Q-",
                standard_set,
                evaluation,
            )
        }
        StandardSet::QStar if number_is_in_q_star(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in Q*",
                standard_set,
                evaluation,
            )
        }
        StandardSet::Z if number_is_in_z(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in Z",
                standard_set,
                evaluation,
            )
        }
        StandardSet::ZNeg if number_is_in_z_neg(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in Z-",
                standard_set,
                evaluation,
            )
        }
        StandardSet::ZStar if number_is_in_z_star(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in Z*",
                standard_set,
                evaluation,
            )
        }
        StandardSet::N if number_is_in_n(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in N",
                standard_set,
                evaluation,
            )
        }
        StandardSet::NPos if number_is_in_n_pos(evaluated_number) => {
            number_in_set_verified_by_evaluation_result(
                in_fact,
                "number in N+",
                standard_set,
                evaluation,
            )
        }
        _ => UnknownGenericStmtResult::new().into(),
    }
}

pub fn builtin_not_in_fact_result_for_evaluation_in_standard_set(
    not_in_fact: &NotInFact,
    evaluation: &SuccessEvaluateObjResult,
    standard_set: &StandardSet,
) -> StmtResult {
    let evaluated_number = &evaluation.value;
    let reason = match standard_set {
        StandardSet::C | StandardSet::R | StandardSet::Q => None,
        StandardSet::CStar if !number_is_in_c_star(evaluated_number) => Some("number not in C*"),
        StandardSet::RPos if !number_is_in_r_pos(evaluated_number) => Some("number not in R+"),
        StandardSet::RNeg if !number_is_in_r_neg(evaluated_number) => Some("number not in R-"),
        StandardSet::RStar if !number_is_in_r_star(evaluated_number) => Some("number not in R*"),
        StandardSet::QPos if !number_is_in_q_pos(evaluated_number) => Some("number not in Q+"),
        StandardSet::QNeg if !number_is_in_q_neg(evaluated_number) => Some("number not in Q-"),
        StandardSet::QStar if !number_is_in_q_star(evaluated_number) => Some("number not in Q*"),
        StandardSet::Z if !number_is_in_z(evaluated_number) => Some("number not in Z"),
        StandardSet::ZNeg if !number_is_in_z_neg(evaluated_number) => Some("number not in Z-"),
        StandardSet::ZStar if !number_is_in_z_star(evaluated_number) => Some("number not in Z*"),
        StandardSet::N if !number_is_in_n(evaluated_number) => Some("number not in N"),
        StandardSet::NPos if !number_is_in_n_pos(evaluated_number) => Some("number not in N+"),
        _ => None,
    };
    match reason {
        Some(reason) => number_not_in_set_verified_by_evaluation_result(
            not_in_fact,
            reason,
            standard_set,
            evaluation,
        ),
        None => UnknownGenericStmtResult::new().into(),
    }
}

pub fn builtin_in_fact_result_for_evaluated_number_in_standard_set(
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
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::R => number_in_set_verified_by_builtin_rules_result(in_fact, "number in R"),
        StandardSet::RPos => {
            if number_is_in_r_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R+")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::RNeg => {
            if number_is_in_r_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R-")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::RStar => {
            if number_is_in_r_star(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in R*")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::Q => number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q"),
        StandardSet::QPos => {
            if number_is_in_q_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q+")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::QNeg => {
            if number_is_in_q_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q-")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::QStar => {
            if number_is_in_q_star(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Q*")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::Z => {
            if number_is_in_z(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::ZNeg => {
            if number_is_in_z_neg(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z-")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::ZStar => {
            if number_is_in_z_star(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in Z*")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::N => {
            if number_is_in_n(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::NPos => {
            if number_is_in_n_pos(evaluated_number) {
                number_in_set_verified_by_builtin_rules_result(in_fact, "number in N+")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
    }
}

pub fn builtin_not_in_fact_result_for_evaluated_number_in_standard_set(
    not_in_fact: &NotInFact,
    evaluated_number: &Number,
    standard_set: &StandardSet,
) -> StmtResult {
    match standard_set {
        StandardSet::C | StandardSet::R | StandardSet::Q => UnknownGenericStmtResult::new().into(),
        StandardSet::CStar => {
            if !number_is_in_c_star(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in C*")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::RPos => {
            if !number_is_in_r_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R+")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::RNeg => {
            if !number_is_in_r_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R-")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::RStar => {
            if !number_is_in_r_star(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in R*")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::QPos => {
            if !number_is_in_q_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q+")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::QNeg => {
            if !number_is_in_q_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q-")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::QStar => {
            if !number_is_in_q_star(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Q*")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::Z => {
            if !number_is_in_z(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::ZNeg => {
            if !number_is_in_z_neg(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z-")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::ZStar => {
            if !number_is_in_z_star(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in Z*")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::N => {
            if !number_is_in_n(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in N")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
        StandardSet::NPos => {
            if !number_is_in_n_pos(evaluated_number) {
                not_in_fact_verified_by_builtin_rules_result(not_in_fact, "number not in N+")
            } else {
                UnknownGenericStmtResult::new().into()
            }
        }
    }
}
