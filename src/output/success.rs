use crate::common::json_value::{line_file_line_json_value, render_json_value, JsonValue};
use crate::prelude::{
    AcceptedByKind, AcceptedByResult, CaseSplitAcceptedBy, CaseSplitCoverage, Fact,
    FactualStmtSuccess, NonFactualStmtSuccess, ObjectIntroductionItem, Runtime, Stmt, StmtResult,
    UnsafeStmt,
};

use super::effects::{effects_json_values, effects_json_values_for_fact};
use super::evidence::{
    factual_success_forall_proof_fields, factual_success_verified_by_value,
    stmt_result_to_composite_step_verified_by,
};
use super::fields::{
    user_visible_stmt_or_msg_text, JSON_KEY_ACCEPTED_BY, JSON_KEY_EFFECTS, JSON_KEY_INSIDE_RESULTS,
    JSON_KEY_RESULT, JSON_KEY_STEPS, JSON_KEY_SUCCESS, JSON_KEY_VERIFIED_BY,
};
use super::normalize::{finalize_display_text_with_optional_strip, json_value_for_output};
use super::source::stmt_text_for_json;

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
    let effect_items = effects_json_values(&x.infers);

    let mut fields = vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            "type".to_string(),
            JsonValue::JsonString(x.stmt.stmt_type_name().to_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&stmt_line_file),
        ),
        ("stmt".to_string(), JsonValue::JsonString(stmt_text)),
        (JSON_KEY_EFFECTS.to_string(), JsonValue::Array(effect_items)),
    ];

    if statement_trust_is_unsafe(&x.stmt) {
        fields.push((
            "trust".to_string(),
            JsonValue::JsonString("unsafe".to_string()),
        ));
    }

    fields.push((
        JSON_KEY_ACCEPTED_BY.to_string(),
        accepted_by_value(runtime, x),
    ));

    fields.push((
        JSON_KEY_INSIDE_RESULTS.to_string(),
        inside_results_value(runtime, &x.inside_results),
    ));

    JsonValue::Object(fields)
}

fn inside_results_value(runtime: &Runtime, inside_results: &[StmtResult]) -> JsonValue {
    if !runtime.detail_output {
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
    let verified_by = factual_success_verified_by_value(runtime, x);
    let effect_items = effects_json_values_for_fact(&x.infers, &x.stmt);

    let mut fields = vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            "type".to_string(),
            JsonValue::JsonString(x.stmt.fact_type_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&fact_line_file),
        ),
        (
            "stmt".to_string(),
            JsonValue::JsonString(stmt_user_visible.clone()),
        ),
    ];

    fields.extend(factual_success_forall_proof_fields(runtime, x));
    fields.extend(vec![
        (JSON_KEY_VERIFIED_BY.to_string(), verified_by),
        (JSON_KEY_EFFECTS.to_string(), JsonValue::Array(effect_items)),
        ("inside_results".to_string(), JsonValue::Array(vec![])),
    ]);

    JsonValue::Object(fields)
}

fn factual_citation_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let verified_by = factual_success_verified_by_value(runtime, x);
    let effect_items = effects_json_values_for_fact(&x.infers, &x.stmt);

    let mut fields = vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            "type".to_string(),
            JsonValue::JsonString(x.stmt.fact_type_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&stmt_line_file),
        ),
        (
            "stmt".to_string(),
            JsonValue::JsonString(stmt_user_visible.clone()),
        ),
    ];

    fields.extend(factual_success_forall_proof_fields(runtime, x));
    fields.extend(vec![
        (JSON_KEY_VERIFIED_BY.to_string(), verified_by),
        (JSON_KEY_EFFECTS.to_string(), JsonValue::Array(effect_items)),
        ("inside_results".to_string(), JsonValue::Array(vec![])),
    ]);

    JsonValue::Object(fields)
}

fn statement_trust_is_unsafe(stmt: &Stmt) -> bool {
    matches!(stmt, Stmt::UnsafeStmt(_))
}

fn accepted_by_value(runtime: &Runtime, success: &NonFactualStmtSuccess) -> JsonValue {
    let mut fields = vec![(
        "type".to_string(),
        JsonValue::JsonString(accepted_by_type(&success.accepted_by).to_string()),
    )];

    if let Some(summary) = accepted_by_summary(success) {
        fields.push((
            "summary".to_string(),
            JsonValue::JsonString(summary.to_string()),
        ));
    }

    match success.accepted_by.kind.as_ref() {
        AcceptedByKind::ProofBlock {
            proved,
            steps_count,
        } => {
            if let Some(proved) = proved {
                fields.push((
                    "proved".to_string(),
                    JsonValue::JsonString(user_visible_stmt_or_msg_text(&proved.to_string())),
                ));
            }
            fields.push(("steps_count".to_string(), JsonValue::Number(*steps_count)));
            fields.push((
                JSON_KEY_STEPS.to_string(),
                JsonValue::Array(accepted_by_step_items(runtime, &success.inside_results)),
            ));
        }
        AcceptedByKind::CaseSplit {
            goals,
            coverage,
            cases,
        } => {
            let goal_items = goals
                .iter()
                .map(|goal| JsonValue::JsonString(user_visible_stmt_or_msg_text(&goal.to_string())))
                .collect::<Vec<_>>();
            let case_items = cases
                .iter()
                .map(|case| accepted_by_case_json_value(runtime, case, goals))
                .collect::<Vec<_>>();
            fields.push(("case_count".to_string(), JsonValue::Number(cases.len())));
            if let Some(coverage) = coverage {
                fields.push((
                    "covers_by".to_string(),
                    accepted_by_case_split_coverage_json_value(runtime, coverage),
                ));
            }
            fields.push(("goals".to_string(), JsonValue::Array(goal_items)));
            fields.push(("cases".to_string(), JsonValue::Array(case_items)));
            fields.push((JSON_KEY_STEPS.to_string(), JsonValue::Array(vec![])));
        }
        AcceptedByKind::ObjectIntroduction | AcceptedByKind::ExistElimination => {
            fields.push((
                "checks".to_string(),
                JsonValue::Array(accepted_by_check_items(runtime, &success.inside_results)),
            ));
            push_introduces_field_if_present(&mut fields, &success.accepted_by.introduces);
        }
        _ => {
            fields.push((
                JSON_KEY_STEPS.to_string(),
                JsonValue::Array(accepted_by_step_items(runtime, &success.inside_results)),
            ));
            push_introduces_field_if_present(&mut fields, &success.accepted_by.introduces);
        }
    }

    JsonValue::Object(fields)
}

fn accepted_by_step_items(runtime: &Runtime, inside_results: &[StmtResult]) -> Vec<JsonValue> {
    inside_results
        .iter()
        .map(|r| stmt_result_to_composite_step_verified_by(runtime, r))
        .collect::<Vec<_>>()
}

fn accepted_by_check_items(runtime: &Runtime, inside_results: &[StmtResult]) -> Vec<JsonValue> {
    inside_results
        .iter()
        .map(|r| accepted_by_check_item(runtime, r))
        .collect::<Vec<_>>()
}

fn accepted_by_check_item(runtime: &Runtime, r: &StmtResult) -> JsonValue {
    if let Some(f) = r.factual_success() {
        JsonValue::Object(vec![
            (
                "stmt".to_string(),
                JsonValue::JsonString(user_visible_stmt_or_msg_text(&f.stmt.to_string())),
            ),
            (
                JSON_KEY_VERIFIED_BY.to_string(),
                factual_success_verified_by_value(runtime, f),
            ),
        ])
    } else if let Some(n) = r.non_factual_success() {
        JsonValue::Object(vec![
            (
                "stmt".to_string(),
                JsonValue::JsonString(stmt_text_for_json(runtime, &n.stmt)),
            ),
            (
                JSON_KEY_ACCEPTED_BY.to_string(),
                accepted_by_value(runtime, n),
            ),
        ])
    } else {
        JsonValue::Object(vec![(
            "type".to_string(),
            JsonValue::JsonString("unknown".to_string()),
        )])
    }
}

fn push_introduces_field_if_present(
    fields: &mut Vec<(String, JsonValue)>,
    introduces: &[ObjectIntroductionItem],
) {
    if introduces.is_empty() {
        return;
    }
    fields.push((
        "introduces".to_string(),
        JsonValue::Array(object_introduction_items_json_value(introduces)),
    ));
}

fn object_introduction_items_json_value(introduces: &[ObjectIntroductionItem]) -> Vec<JsonValue> {
    introduces
        .iter()
        .map(|item| {
            let facts = item
                .facts
                .iter()
                .map(|fact| JsonValue::JsonString(user_visible_stmt_or_msg_text(&fact.to_string())))
                .collect::<Vec<_>>();
            JsonValue::Object(vec![
                ("name".to_string(), JsonValue::JsonString(item.name.clone())),
                ("facts".to_string(), JsonValue::Array(facts)),
            ])
        })
        .collect::<Vec<_>>()
}

fn accepted_by_case_split_coverage_json_value(
    runtime: &Runtime,
    coverage: &CaseSplitCoverage,
) -> JsonValue {
    JsonValue::Object(vec![
        (
            "fact".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&coverage.fact.to_string())),
        ),
        (
            JSON_KEY_VERIFIED_BY.to_string(),
            stmt_result_to_composite_step_verified_by(runtime, coverage.result.as_ref()),
        ),
    ])
}

fn accepted_by_case_json_value(
    runtime: &Runtime,
    case: &CaseSplitAcceptedBy,
    goals: &[Fact],
) -> JsonValue {
    let conclusion_items = goals
        .iter()
        .map(|goal| JsonValue::JsonString(user_visible_stmt_or_msg_text(&goal.to_string())))
        .collect::<Vec<_>>();
    let mut fields = vec![
        (
            "case".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&case.case_fact.to_string())),
        ),
        (
            "conclusions".to_string(),
            JsonValue::Array(conclusion_items),
        ),
        (
            "steps_count".to_string(),
            JsonValue::Number(case.inside_results.len()),
        ),
    ];

    if let Some(impossible_fact) = &case.impossible_fact {
        fields.push((
            "impossible".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&impossible_fact.to_string())),
        ));
        fields.push((
            "impossible_by".to_string(),
            JsonValue::Array(vec![
                JsonValue::JsonString(user_visible_stmt_or_msg_text(&impossible_fact.to_string())),
                JsonValue::JsonString(user_visible_stmt_or_msg_text(
                    &impossible_fact.make_reversed().to_string(),
                )),
            ]),
        ));
    }

    if runtime.detail_output {
        fields.push((
            JSON_KEY_INSIDE_RESULTS.to_string(),
            inside_results_value(runtime, &case.inside_results),
        ));
    }

    JsonValue::Object(fields)
}

fn accepted_by_type(accepted_by: &AcceptedByResult) -> &'static str {
    match accepted_by.kind.as_ref() {
        AcceptedByKind::Assumption => "assumption",
        AcceptedByKind::Definition => "definition",
        AcceptedByKind::ObjectIntroduction => "object introduction",
        AcceptedByKind::ExistElimination => "exist elimination",
        AcceptedByKind::ProofBlock { .. } => "proof block",
        AcceptedByKind::CaseSplit { .. } => "case split",
        AcceptedByKind::TheoremCall => "theorem call",
        AcceptedByKind::Witness => "witness",
        AcceptedByKind::NoOp => "no op",
        AcceptedByKind::Evaluation => "evaluation",
        AcceptedByKind::Command => "command",
        AcceptedByKind::VerifiedFact => "verified fact",
    }
}

fn accepted_by_summary(success: &NonFactualStmtSuccess) -> Option<&'static str> {
    match &success.stmt {
        Stmt::UnsafeStmt(UnsafeStmt::KnowStmt(_)) => {
            return Some("facts accepted without proof");
        }
        Stmt::UnsafeStmt(UnsafeStmt::DefLetStmt(_)) => {
            return Some("binding accepted without proof obligation");
        }
        _ => {}
    }

    match success.accepted_by.kind.as_ref() {
        AcceptedByKind::Assumption => Some("facts accepted as explicit assumptions"),
        AcceptedByKind::Definition => Some("definition or interface registered"),
        AcceptedByKind::ObjectIntroduction => Some("object and supporting facts introduced"),
        AcceptedByKind::ExistElimination => {
            Some("exist fact verified and witness facts registered")
        }
        AcceptedByKind::ProofBlock { .. } => Some("proof steps executed and target facts verified"),
        AcceptedByKind::CaseSplit { .. } => {
            Some("cases cover all situations and target facts were released")
        }
        AcceptedByKind::TheoremCall => Some("named theorem instantiated"),
        AcceptedByKind::Witness => Some("witness obligations verified"),
        AcceptedByKind::NoOp => Some("statement intentionally does nothing"),
        AcceptedByKind::Evaluation => Some("expression evaluated"),
        AcceptedByKind::Command => Some("command completed"),
        AcceptedByKind::VerifiedFact => None,
    }
}
