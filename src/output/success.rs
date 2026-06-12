use crate::common::json_value::{line_file_line_json_value, render_json_value, JsonValue};
use crate::prelude::{
    ByCasesVerificationResult, ByContraVerificationResult, ByVerificationResult,
    ClaimFactVerificationResult, ClaimForallVerificationResult, ClaimVerificationResult,
    CommandStmt, FactualStmtSuccess, NonFactualStmtSuccess, Runtime, Stmt, StmtResult,
    VerifiedByResult,
};

use super::evidence::{
    factual_success_forall_proof_fields, factual_success_verified_by_value,
    forall_assumption_items, forall_param_items, forall_proved_fact_value,
    stmt_result_to_composite_step_verified_by,
};
use super::fields::{
    user_visible_stmt_or_msg_text, JSON_KEY_CONCLUSIONS, JSON_KEY_INSIDE_RESULTS, JSON_KEY_RESULT,
    JSON_KEY_STMT, JSON_KEY_STMT_TYPE, JSON_KEY_STORE_FACTS, JSON_KEY_SUCCESS,
    JSON_KEY_VERIFICATION,
};
use super::normalize::{finalize_display_text_with_optional_strip, json_value_for_output};
use super::source::stmt_text_for_json;
use super::store_facts::{store_fact_json_values, store_fact_json_values_for_fact};

pub fn display_stmt_exec_result_json(
    runtime: &Runtime,
    r: &StmtResult,
    strip_free_param_tags: bool,
) -> String {
    let value = json_value_for_output(runtime, stmt_exec_result_json_value(runtime, r));
    let raw = render_json_value(&value, 0);
    finalize_display_text_with_optional_strip(raw, strip_free_param_tags)
}

fn stmt_exec_result_json_value(runtime: &Runtime, r: &StmtResult) -> JsonValue {
    if let Some(x) = r.factual_success() {
        factual_stmt_success_to_json(runtime, x)
    } else if let Some(x) = r.non_factual_success() {
        non_factual_stmt_success_to_json(runtime, x)
    } else {
        unreachable!()
    }
}

fn non_factual_stmt_success_to_json(runtime: &Runtime, x: &NonFactualStmtSuccess) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_text = stmt_text_for_json(runtime, &x.stmt);
    let store_fact_items = store_fact_json_values(&x.infers);

    let mut fields = vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            JSON_KEY_STMT_TYPE.to_string(),
            JsonValue::JsonString(x.stmt.output_type_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&stmt_line_file),
        ),
        (JSON_KEY_STMT.to_string(), JsonValue::JsonString(stmt_text)),
    ];

    if let Some(verification) = non_factual_verification_value(runtime, x) {
        fields.push((JSON_KEY_VERIFICATION.to_string(), verification));
    }

    fields.push((
        JSON_KEY_STORE_FACTS.to_string(),
        JsonValue::Array(store_fact_items),
    ));

    fields.push((
        JSON_KEY_INSIDE_RESULTS.to_string(),
        inside_results_value(runtime, &x.stmt, &x.inside_results),
    ));

    JsonValue::Object(fields)
}

fn non_factual_verification_value(
    runtime: &Runtime,
    x: &NonFactualStmtSuccess,
) -> Option<JsonValue> {
    if let Some(claim_verification) = x.claim_verification.as_ref() {
        return match claim_verification {
            ClaimVerificationResult::Forall(verification) => Some(claim_forall_verification_value(
                runtime,
                verification,
                &x.inside_results,
            )),
            ClaimVerificationResult::Fact(verification) => Some(claim_fact_verification_value(
                runtime,
                verification,
                &x.inside_results,
            )),
        };
    }
    match x.by_verification.as_ref()? {
        ByVerificationResult::Cases(verification) => Some(by_cases_verification_value(
            runtime,
            verification,
            &x.inside_results,
        )),
        ByVerificationResult::Contra(verification) => Some(by_contra_verification_value(
            runtime,
            verification,
            &x.inside_results,
        )),
    }
}

fn claim_forall_verification_value(
    runtime: &Runtime,
    verification: &ClaimForallVerificationResult,
    inside_results: &[StmtResult],
) -> JsonValue {
    let proof_steps = proof_step_values(runtime, inside_results, verification.proof_step_count);
    let conclusion_results = inside_results.iter().skip(verification.proof_step_count);
    let conclusions = verification
        .forall_fact
        .then_facts
        .iter()
        .zip(conclusion_results)
        .map(|(stmt, result)| {
            forall_proved_fact_value(runtime, &verification.forall_fact, stmt, result)
        })
        .collect::<Vec<_>>();

    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("claim forall proof".to_string()),
        ),
        (
            "parameters".to_string(),
            JsonValue::Array(forall_param_items(
                &verification.forall_fact.params_def_with_type,
            )),
        ),
        (
            "assumptions".to_string(),
            JsonValue::Array(forall_assumption_items(&verification.assumption_infers)),
        ),
        ("proof_steps".to_string(), JsonValue::Array(proof_steps)),
        (
            JSON_KEY_CONCLUSIONS.to_string(),
            JsonValue::Array(conclusions),
        ),
    ])
}

fn claim_fact_verification_value(
    runtime: &Runtime,
    verification: &ClaimFactVerificationResult,
    inside_results: &[StmtResult],
) -> JsonValue {
    let proof_steps = proof_step_values(runtime, inside_results, verification.proof_step_count);
    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString("claim proof".to_string()),
        ),
        (
            "prove_goal".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(
                &verification.fact.to_string(),
            )),
        ),
        ("proof_steps".to_string(), JsonValue::Array(proof_steps)),
    ];

    if let Some(result) = inside_results.get(verification.proof_step_count) {
        fields.push((
            "conclusion".to_string(),
            JsonValue::Object(vec![
                (
                    JSON_KEY_STMT.to_string(),
                    JsonValue::JsonString(user_visible_stmt_or_msg_text(
                        &verification.fact.to_string(),
                    )),
                ),
                (
                    JSON_KEY_VERIFICATION.to_string(),
                    stmt_result_to_composite_step_verified_by(runtime, result),
                ),
            ]),
        ));
    }

    JsonValue::Object(fields)
}

fn proof_step_values(
    runtime: &Runtime,
    inside_results: &[StmtResult],
    proof_step_count: usize,
) -> Vec<JsonValue> {
    inside_results
        .iter()
        .take(proof_step_count)
        .map(|r| stmt_exec_result_json_value(runtime, r))
        .collect::<Vec<_>>()
}

fn by_cases_verification_value(
    runtime: &Runtime,
    verification: &ByCasesVerificationResult,
    inside_results: &[StmtResult],
) -> JsonValue {
    let case_coverage = inside_results
        .first()
        .map(|result| stmt_exec_result_json_value(runtime, result))
        .unwrap_or_else(|| JsonValue::Object(vec![]));
    let prove_goals = verification
        .then_facts
        .iter()
        .map(|fact| JsonValue::JsonString(user_visible_stmt_or_msg_text(&fact.to_string())))
        .collect::<Vec<_>>();

    let mut cursor = 1;
    let mut case_items = Vec::new();
    for case_index in 0..verification.cases.len() {
        let count = verification
            .case_result_counts
            .get(case_index)
            .copied()
            .unwrap_or(0);
        let end = std::cmp::min(cursor + count, inside_results.len());
        let case_results = &inside_results[cursor..end];
        cursor = end;
        case_items.push(by_case_value(
            runtime,
            verification,
            case_index,
            case_results,
        ));
    }

    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("by cases proof".to_string()),
        ),
        ("prove_goals".to_string(), JsonValue::Array(prove_goals)),
        ("case_coverage".to_string(), case_coverage),
        ("cases".to_string(), JsonValue::Array(case_items)),
    ])
}

fn by_case_value(
    runtime: &Runtime,
    verification: &ByCasesVerificationResult,
    case_index: usize,
    case_results: &[StmtResult],
) -> JsonValue {
    let proof_step_count = verification
        .proof_step_counts
        .get(case_index)
        .copied()
        .unwrap_or(0);
    let proof_steps = proof_step_values(runtime, case_results, proof_step_count);
    let mut fields = vec![
        ("case_index".to_string(), JsonValue::Number(case_index + 1)),
        (
            "case".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(
                &verification.cases[case_index].to_string(),
            )),
        ),
        (
            "assumption".to_string(),
            local_assumption_fact_value(
                &verification.cases[case_index].to_string(),
                "case assumption",
            ),
        ),
        ("proof_steps".to_string(), JsonValue::Array(proof_steps)),
    ];

    if let Some(impossible_fact) = verification
        .impossible_facts
        .get(case_index)
        .and_then(|fact| fact.as_ref())
    {
        let impossible_result = case_results.get(proof_step_count);
        fields.push((
            "impossible".to_string(),
            impossible_verification_value(runtime, impossible_fact, impossible_result),
        ));
    } else {
        let conclusions = case_results
            .iter()
            .skip(proof_step_count)
            .map(|result| stmt_exec_result_json_value(runtime, result))
            .collect::<Vec<_>>();
        fields.push((
            JSON_KEY_CONCLUSIONS.to_string(),
            JsonValue::Array(conclusions),
        ));
    }

    JsonValue::Object(fields)
}

fn by_contra_verification_value(
    runtime: &Runtime,
    verification: &ByContraVerificationResult,
    inside_results: &[StmtResult],
) -> JsonValue {
    let proof_steps = proof_step_values(runtime, inside_results, verification.proof_step_count);
    let final_checks = inside_results
        .iter()
        .skip(verification.proof_step_count)
        .collect::<Vec<_>>();
    let impossible = JsonValue::Object(vec![
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(
                &verification.impossible_fact.to_string(),
            )),
        ),
        (
            "checks".to_string(),
            JsonValue::Array(impossible_check_values(
                runtime,
                &verification.impossible_fact,
                final_checks.as_slice(),
            )),
        ),
    ]);

    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("by contra proof".to_string()),
        ),
        (
            "prove_goal".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(
                &verification.to_prove.to_string(),
            )),
        ),
        (
            "reverse_assumption".to_string(),
            local_assumption_fact_value(
                &verification.reverse_assumption.to_string(),
                "by contra assumption",
            ),
        ),
        ("proof_steps".to_string(), JsonValue::Array(proof_steps)),
        ("impossible".to_string(), impossible),
    ])
}

fn impossible_verification_value(
    runtime: &Runtime,
    impossible_fact: &crate::prelude::AtomicFact,
    result: Option<&StmtResult>,
) -> JsonValue {
    let checks = result
        .and_then(|r| r.non_factual_success())
        .map(|n| n.inside_results.iter().collect::<Vec<&StmtResult>>())
        .unwrap_or_default();

    JsonValue::Object(vec![
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&impossible_fact.to_string())),
        ),
        (
            "checks".to_string(),
            JsonValue::Array(impossible_check_values(
                runtime,
                impossible_fact,
                checks.as_slice(),
            )),
        ),
    ])
}

fn impossible_check_values(
    runtime: &Runtime,
    impossible_fact: &crate::prelude::AtomicFact,
    results: &[&StmtResult],
) -> Vec<JsonValue> {
    let facts = vec![
        impossible_fact.clone().into(),
        impossible_fact.make_reversed().into(),
    ];
    let roles = ["impossible fact", "reversed impossible fact"];
    facts
        .into_iter()
        .zip(roles)
        .zip(results.iter())
        .map(|((fact, role), result)| fact_check_value(runtime, role, &fact, result))
        .collect::<Vec<_>>()
}

fn fact_check_value(
    runtime: &Runtime,
    role: &str,
    fact: &crate::prelude::Fact,
    result: &StmtResult,
) -> JsonValue {
    JsonValue::Object(vec![
        ("role".to_string(), JsonValue::JsonString(role.to_string())),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&fact.to_string())),
        ),
        (
            JSON_KEY_VERIFICATION.to_string(),
            stmt_result_to_composite_step_verified_by(runtime, result),
        ),
    ])
}

fn local_assumption_fact_value(fact: &str, reason: &str) -> JsonValue {
    JsonValue::Object(vec![
        (
            "fact".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(fact)),
        ),
        (
            "reason".to_string(),
            JsonValue::JsonString(reason.to_string()),
        ),
    ])
}

fn inside_results_value(
    runtime: &Runtime,
    stmt: &Stmt,
    inside_results: &[StmtResult],
) -> JsonValue {
    let should_show_inside_results =
        runtime.detail_output || matches!(stmt, Stmt::Command(CommandStmt::RunFileStmt(_)));
    if !should_show_inside_results {
        return JsonValue::Array(vec![]);
    }

    JsonValue::Array(
        inside_results
            .iter()
            .map(|r| stmt_exec_result_json_value(runtime, r))
            .collect::<Vec<_>>(),
    )
}

fn factual_stmt_success_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    if x.is_verified_by_builtin_rules_only() {
        factual_builtin_rules_to_json(runtime, x)
    } else {
        factual_citation_to_json(runtime, x)
    }
}

fn factual_builtin_rules_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let fact_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let store_fact_items = store_fact_json_values_for_fact(&x.infers, &x.stmt);

    let mut fields = vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            JSON_KEY_STMT_TYPE.to_string(),
            JsonValue::JsonString(x.stmt.output_type_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&fact_line_file),
        ),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(stmt_user_visible.clone()),
        ),
    ];

    fields.extend(factual_success_forall_proof_fields(runtime, x));
    if !factual_success_is_forall_proof(x) {
        fields.push((
            JSON_KEY_VERIFICATION.to_string(),
            factual_success_verified_by_value(runtime, x),
        ));
    }
    fields.push((
        JSON_KEY_STORE_FACTS.to_string(),
        JsonValue::Array(store_fact_items),
    ));
    fields.push(("inside_results".to_string(), JsonValue::Array(vec![])));

    JsonValue::Object(fields)
}

fn factual_citation_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let store_fact_items = store_fact_json_values_for_fact(&x.infers, &x.stmt);

    let mut fields = vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            JSON_KEY_STMT_TYPE.to_string(),
            JsonValue::JsonString(x.stmt.output_type_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&stmt_line_file),
        ),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(stmt_user_visible.clone()),
        ),
    ];

    fields.extend(factual_success_forall_proof_fields(runtime, x));
    if !factual_success_is_forall_proof(x) {
        fields.push((
            JSON_KEY_VERIFICATION.to_string(),
            factual_success_verified_by_value(runtime, x),
        ));
    }
    fields.push((
        JSON_KEY_STORE_FACTS.to_string(),
        JsonValue::Array(store_fact_items),
    ));
    fields.push(("inside_results".to_string(), JsonValue::Array(vec![])));

    JsonValue::Object(fields)
}

fn factual_success_is_forall_proof(x: &FactualStmtSuccess) -> bool {
    matches!(x.verified_by, VerifiedByResult::ForallProof(_))
}
