use crate::common::json_value::{line_file_line_json_value, render_json_value, JsonValue};
use crate::prelude::{
    ByAssignmentVerificationResult, ByCasesVerificationResult, ByChoiceVerificationResult,
    ByContraVerificationResult, ByDefinitionVerificationResult,
    ByEnumerateFiniteSetVerificationResult, ByEnumerateRangeVerificationResult,
    ByExtensionVerificationResult, ByForVerificationResult, ByInducVerificationResult,
    ByPropRegistrationVerificationResult, ByTheoremVerificationResult, ByVerificationResult,
    ClaimFactVerificationResult, ClaimForallVerificationResult, ClaimVerificationResult,
    CommandStmt, DefObjStmt, Fact, FactualStmtSuccess, InferResult, NonFactualStmtSuccess,
    OutputStyle, ParamDefWithType, Runtime, StatementExecutionTrace, StatementPhaseStatus, Stmt,
    StmtResult, TheoremVerificationResult, VerifiedByResult,
};

use super::evidence::{
    factual_success_forall_proof_fields, factual_success_verified_by_value,
    forall_assumption_items, forall_param_items, forall_proved_fact_value,
    stmt_result_to_composite_step_verified_by,
};
use super::fields::{
    user_visible_stmt_or_msg_text, JSON_KEY_CONCLUSIONS, JSON_KEY_INSIDE_RESULTS, JSON_KEY_RESULT,
    JSON_KEY_STMT, JSON_KEY_STMT_TYPE, JSON_KEY_SUCCESS, JSON_KEY_UNKNOWN_RESULT,
    JSON_KEY_VERIFICATION,
};
use super::normalize::{
    finalize_display_text_with_optional_strip, json_value_for_output_with_style,
};
use super::phases::execution_phases_value;
use super::source::stmt_text_for_json;
use super::store_facts::{store_fact_json_values, store_fact_output_json_values};
use super::{fact_unknown_json_value, stmt_unknown_json_value};

pub fn display_stmt_exec_result_json(
    runtime: &Runtime,
    r: &StmtResult,
    strip_free_param_tags: bool,
) -> String {
    display_stmt_exec_result_json_with_style(
        runtime,
        r,
        runtime.effective_output_style(),
        strip_free_param_tags,
    )
}

pub(crate) fn display_stmt_exec_result_json_with_style(
    runtime: &Runtime,
    r: &StmtResult,
    output_style: OutputStyle,
    strip_free_param_tags: bool,
) -> String {
    let value = json_value_for_output_with_style(
        runtime,
        stmt_exec_result_json_value(runtime, r, output_style),
        output_style,
    );
    let raw = render_json_value(&value, 0);
    finalize_display_text_with_optional_strip(raw, strip_free_param_tags)
}

fn stmt_exec_result_json_value(
    runtime: &Runtime,
    r: &StmtResult,
    output_style: OutputStyle,
) -> JsonValue {
    if let Some(x) = r.factual_success() {
        factual_stmt_success_to_json(runtime, x, output_style)
    } else if let Some(x) = r.non_factual_success() {
        non_factual_stmt_success_to_json(runtime, x, output_style)
    } else {
        unknown_stmt_result_json_value(runtime, r, output_style)
    }
}

fn unknown_stmt_result_json_value(
    runtime: &Runtime,
    r: &StmtResult,
    output_style: OutputStyle,
) -> JsonValue {
    let mut fields = vec![(
        JSON_KEY_RESULT.to_string(),
        JsonValue::JsonString("unknown".to_string()),
    )];
    if let Some(unknown) = r.as_fact_unknown() {
        fields.push((
            "line".to_string(),
            line_file_line_json_value(&unknown.goal().line_file()),
        ));
        fields.push((
            JSON_KEY_UNKNOWN_RESULT.to_string(),
            fact_unknown_json_value(runtime, unknown, output_style),
        ));
        if output_style.is_detailed() {
            let trace = StatementExecutionTrace::unknown();
            fields.push((
                "phases".to_string(),
                execution_phases_value(
                    &trace,
                    well_definedness_checks_for_fact(unknown.goal()),
                    vec![(
                        JSON_KEY_UNKNOWN_RESULT.to_string(),
                        fact_unknown_json_value(runtime, unknown, output_style),
                    )],
                    vec![],
                ),
            ));
        }
    } else if let Some(unknown) = r.as_unknown() {
        fields.push((
            JSON_KEY_UNKNOWN_RESULT.to_string(),
            stmt_unknown_json_value(runtime, unknown, output_style),
        ));
        if output_style.is_detailed() {
            let trace = StatementExecutionTrace::unknown();
            fields.push((
                "phases".to_string(),
                execution_phases_value(
                    &trace,
                    vec![],
                    vec![(
                        JSON_KEY_UNKNOWN_RESULT.to_string(),
                        stmt_unknown_json_value(runtime, unknown, output_style),
                    )],
                    vec![],
                ),
            ));
        }
    } else {
        fields.push((
            JSON_KEY_UNKNOWN_RESULT.to_string(),
            JsonValue::Object(vec![(
                "type".to_string(),
                JsonValue::JsonString("unknown".to_string()),
            )]),
        ));
    }
    JsonValue::Object(fields)
}

fn non_factual_stmt_success_to_json(
    runtime: &Runtime,
    x: &NonFactualStmtSuccess,
    output_style: OutputStyle,
) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_text = stmt_text_for_json(runtime, &x.stmt);

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
    add_statement_trust_fields(x.execution_trace.as_ref(), &mut fields);

    if let Some(verification) = non_factual_verification_value(runtime, x, output_style) {
        fields.push((JSON_KEY_VERIFICATION.to_string(), verification));
    }

    if !x.reported_store_facts.is_empty() {
        fields.push((
            "store_facts".to_string(),
            JsonValue::Array(store_fact_output_json_values(&x.reported_store_facts)),
        ));
    }

    fields.push((
        JSON_KEY_INSIDE_RESULTS.to_string(),
        inside_results_value(runtime, &x.stmt, &x.inside_results, output_style),
    ));

    if output_style.is_detailed() {
        if let Some(trace) = x.execution_trace.as_ref() {
            fields.push((
                "phases".to_string(),
                execution_phases_value(
                    trace,
                    well_definedness_checks_for_stmt(&x.stmt),
                    non_factual_process_fields(runtime, x, output_style),
                    environment_effect_values(&x.stmt, &x.infers, trace),
                ),
            ));
        }
    }

    JsonValue::Object(fields)
}

fn non_factual_process_fields(
    runtime: &Runtime,
    x: &NonFactualStmtSuccess,
    output_style: OutputStyle,
) -> Vec<(String, JsonValue)> {
    let mut fields = Vec::new();
    if let Some(verification) = non_factual_verification_value(runtime, x, output_style) {
        fields.push((JSON_KEY_VERIFICATION.to_string(), verification));
    }
    if !x.inside_results.is_empty() {
        fields.push((
            "checks".to_string(),
            JsonValue::Array(
                x.inside_results
                    .iter()
                    .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
                    .collect::<Vec<_>>(),
            ),
        ));
    }
    fields
}

fn non_factual_verification_value(
    runtime: &Runtime,
    x: &NonFactualStmtSuccess,
    output_style: OutputStyle,
) -> Option<JsonValue> {
    if let Some(theorem_verification) = x.theorem_verification.as_ref() {
        return Some(theorem_verification_value(
            runtime,
            theorem_verification,
            &x.inside_results,
            output_style,
        ));
    }
    if let Some(claim_verification) = x.claim_verification.as_ref() {
        return match claim_verification {
            ClaimVerificationResult::Forall(verification) => Some(claim_forall_verification_value(
                runtime,
                verification,
                &x.inside_results,
                output_style,
            )),
            ClaimVerificationResult::Fact(verification) => Some(claim_fact_verification_value(
                runtime,
                verification,
                &x.inside_results,
                output_style,
            )),
        };
    }
    match x.by_verification.as_ref()? {
        ByVerificationResult::Cases(verification) => Some(by_cases_verification_value(
            runtime,
            verification,
            &x.inside_results,
            output_style,
        )),
        ByVerificationResult::Contra(verification) => Some(by_contra_verification_value(
            runtime,
            verification,
            &x.inside_results,
            output_style,
        )),
        ByVerificationResult::EnumerateFiniteSet(verification) => {
            Some(by_enumerate_finite_set_verification_value(
                runtime,
                verification,
                &x.inside_results,
                output_style,
            ))
        }
        ByVerificationResult::EnumerateRange(verification) => {
            Some(by_enumerate_range_verification_value(
                runtime,
                verification,
                &x.inside_results,
                output_style,
            ))
        }
        ByVerificationResult::Induc(verification) => Some(by_induc_verification_value(
            runtime,
            verification,
            &x.inside_results,
            output_style,
        )),
        ByVerificationResult::For(verification) => Some(by_for_verification_value(
            runtime,
            verification,
            &x.inside_results,
            output_style,
        )),
        ByVerificationResult::Extension(verification) => Some(by_extension_verification_value(
            runtime,
            verification,
            &x.inside_results,
            output_style,
        )),
        ByVerificationResult::PropRegistration(verification) => {
            Some(by_prop_registration_verification_value(
                runtime,
                verification,
                &x.inside_results,
                output_style,
            ))
        }
        ByVerificationResult::AxiomOfChoice(verification) => Some(by_choice_verification_value(
            runtime,
            verification,
            &x.inside_results,
            "trusted_conclusion",
            output_style,
        )),
        ByVerificationResult::ZornLemma(verification) => Some(by_choice_verification_value(
            runtime,
            verification,
            &x.inside_results,
            "trusted_conclusion",
            output_style,
        )),
        ByVerificationResult::RegularityAxiom(verification) => Some(by_choice_verification_value(
            runtime,
            verification,
            &x.inside_results,
            "trusted_conclusion",
            output_style,
        )),
        ByVerificationResult::Definition(verification) => Some(by_definition_verification_value(
            runtime,
            verification,
            &x.inside_results,
            output_style,
        )),
        ByVerificationResult::Theorem(verification) => Some(by_theorem_verification_value(
            runtime,
            verification,
            &x.inside_results,
            output_style,
        )),
    }
}

fn theorem_verification_value(
    runtime: &Runtime,
    verification: &TheoremVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let proof_steps = proof_step_values(
        runtime,
        inside_results,
        verification.proof_step_count,
        output_style,
    );
    let conclusion_results = inside_results.iter().skip(verification.proof_step_count);
    let conclusions = verification
        .forall_fact
        .then_facts
        .iter()
        .zip(conclusion_results)
        .map(|(stmt, result)| {
            forall_proved_fact_value(
                runtime,
                &verification.forall_fact,
                stmt,
                result,
                output_style,
            )
        })
        .collect::<Vec<_>>();

    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("theorem proof".to_string()),
        ),
        (
            "theorem".to_string(),
            JsonValue::JsonString(verification.name.clone()),
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

fn claim_forall_verification_value(
    runtime: &Runtime,
    verification: &ClaimForallVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let proof_steps = proof_step_values(
        runtime,
        inside_results,
        verification.proof_step_count,
        output_style,
    );
    let conclusion_results = inside_results.iter().skip(verification.proof_step_count);
    let conclusions = verification
        .forall_fact
        .then_facts
        .iter()
        .zip(conclusion_results)
        .map(|(stmt, result)| {
            forall_proved_fact_value(
                runtime,
                &verification.forall_fact,
                stmt,
                result,
                output_style,
            )
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
    output_style: OutputStyle,
) -> JsonValue {
    let proof_steps = proof_step_values(
        runtime,
        inside_results,
        verification.proof_step_count,
        output_style,
    );
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
                    stmt_result_to_composite_step_verified_by(runtime, result, output_style),
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
    output_style: OutputStyle,
) -> Vec<JsonValue> {
    inside_results
        .iter()
        .take(proof_step_count)
        .map(|r| stmt_exec_result_json_value(runtime, r, output_style))
        .collect::<Vec<_>>()
}

fn by_cases_verification_value(
    runtime: &Runtime,
    verification: &ByCasesVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let case_coverage = inside_results
        .first()
        .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
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
            output_style,
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
    output_style: OutputStyle,
) -> JsonValue {
    let proof_step_count = verification
        .proof_step_counts
        .get(case_index)
        .copied()
        .unwrap_or(0);
    let proof_steps = proof_step_values(runtime, case_results, proof_step_count, output_style);
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
            impossible_verification_value(
                runtime,
                impossible_fact,
                impossible_result,
                output_style,
            ),
        ));
    } else {
        let conclusions = case_results
            .iter()
            .skip(proof_step_count)
            .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
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
    output_style: OutputStyle,
) -> JsonValue {
    let proof_steps = proof_step_values(
        runtime,
        inside_results,
        verification.proof_step_count,
        output_style,
    );
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
                output_style,
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

fn by_enumerate_finite_set_verification_value(
    runtime: &Runtime,
    verification: &ByEnumerateFiniteSetVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("by enumerate finite_set proof".to_string()),
        ),
        (
            "parameters".to_string(),
            JsonValue::Array(string_items(&verification.parameters)),
        ),
        (
            "parameter_sets".to_string(),
            JsonValue::Array(string_items(&verification.parameter_sets)),
        ),
        (
            "prove_goal".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&verification.prove_goal)),
        ),
        (
            "assignments".to_string(),
            JsonValue::Array(iteration_assignment_values(
                runtime,
                &verification.assignments,
                inside_results,
                output_style,
            )),
        ),
        (
            "generated_forall".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(
                &verification.generated_forall,
            )),
        ),
    ])
}

fn by_for_verification_value(
    runtime: &Runtime,
    verification: &ByForVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("by for proof".to_string()),
        ),
        (
            "iteration_mode".to_string(),
            JsonValue::JsonString(verification.iteration_mode.clone()),
        ),
        (
            "parameters".to_string(),
            JsonValue::Array(string_items(&verification.parameters)),
        ),
        (
            "domains".to_string(),
            JsonValue::Array(string_items(&verification.domains)),
        ),
        (
            "prove_goal".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&verification.prove_goal)),
        ),
        (
            "assignments".to_string(),
            JsonValue::Array(iteration_assignment_values(
                runtime,
                &verification.assignments,
                inside_results,
                output_style,
            )),
        ),
        (
            "generated_forall".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(
                &verification.generated_forall,
            )),
        ),
    ])
}

fn iteration_assignment_values(
    runtime: &Runtime,
    assignments: &[ByAssignmentVerificationResult],
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> Vec<JsonValue> {
    let mut cursor = 0;
    let mut values = Vec::new();
    for assignment in assignments.iter() {
        let end = std::cmp::min(cursor + assignment.result_count, inside_results.len());
        let results = &inside_results[cursor..end];
        cursor = end;
        values.push(iteration_assignment_value(
            runtime,
            assignment,
            results,
            output_style,
        ));
    }
    values
}

fn iteration_assignment_value(
    runtime: &Runtime,
    assignment: &ByAssignmentVerificationResult,
    results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let domain_end = std::cmp::min(assignment.domain_check_count, results.len());
    let proof_end = std::cmp::min(domain_end + assignment.proof_step_count, results.len());
    let conclusion_end = std::cmp::min(proof_end + assignment.conclusion_count, results.len());

    let mut fields = vec![
        (
            "assignment".to_string(),
            string_pair_object(&assignment.assignment),
        ),
        (
            "assumptions".to_string(),
            JsonValue::Array(assumption_pair_values(&assignment.assumptions)),
        ),
        (
            "domain_checks".to_string(),
            JsonValue::Array(
                results[..domain_end]
                    .iter()
                    .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
                    .collect::<Vec<_>>(),
            ),
        ),
        (
            "proof_steps".to_string(),
            JsonValue::Array(
                results[domain_end..proof_end]
                    .iter()
                    .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
                    .collect::<Vec<_>>(),
            ),
        ),
        (
            JSON_KEY_CONCLUSIONS.to_string(),
            JsonValue::Array(
                results[proof_end..conclusion_end]
                    .iter()
                    .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
                    .collect::<Vec<_>>(),
            ),
        ),
    ];
    if let Some(skipped_domain) = assignment.skipped_domain.as_ref() {
        fields.push((
            "skipped_domain".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(skipped_domain)),
        ));
    }
    JsonValue::Object(fields)
}

fn by_enumerate_range_verification_value(
    runtime: &Runtime,
    verification: &ByEnumerateRangeVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let mut check_results = Vec::new();
    if let Some(result) = inside_results.first() {
        check_results.push(statement_check_value(
            runtime,
            "membership",
            &verification.membership_fact,
            result,
            output_style,
        ));
    }
    for (endpoint_fact, result) in verification
        .endpoint_facts
        .iter()
        .zip(inside_results.iter().skip(1))
    {
        check_results.push(statement_check_value(
            runtime,
            "endpoint in Z",
            endpoint_fact,
            result,
            output_style,
        ));
    }

    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString(verification.proof_type.clone()),
        ),
        (
            "element".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&verification.element)),
        ),
        (
            "range".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&verification.range)),
        ),
        ("checks".to_string(), JsonValue::Array(check_results)),
        (
            "generated_cases".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&verification.generated_cases)),
        ),
    ])
}

fn by_induc_verification_value(
    runtime: &Runtime,
    verification: &ByInducVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let proof_type = if verification.finite_set {
        "by finite-set induction proof"
    } else if verification.strong {
        "by strong_induc proof"
    } else {
        "by induc proof"
    };
    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString(proof_type.to_string()),
        ),
        (
            "parameter".to_string(),
            JsonValue::JsonString(verification.parameter.clone()),
        ),
        (
            "start".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&verification.start)),
        ),
        (
            "prove_goals".to_string(),
            JsonValue::Array(string_items(&verification.prove_goals)),
        ),
    ];

    if verification.structured {
        let base_end = std::cmp::min(verification.base_result_count, inside_results.len());
        let base_results = &inside_results[..base_end];
        let step_end = std::cmp::min(
            base_end + verification.step_result_count,
            inside_results.len(),
        );
        let step_results = &inside_results[base_end..step_end];
        fields.push((
            "base_case".to_string(),
            induction_case_value(
                runtime,
                &verification.base_assumptions,
                verification.base_proof_step_count,
                base_results,
                output_style,
            ),
        ));
        fields.push((
            "step_case".to_string(),
            induction_case_value(
                runtime,
                &verification.step_assumptions,
                verification.step_proof_step_count,
                step_results,
                output_style,
            ),
        ));
    } else {
        fields.push((
            "proof_steps".to_string(),
            JsonValue::Array(proof_step_values(
                runtime,
                inside_results,
                verification.proof_step_count,
                output_style,
            )),
        ));
    }

    fields.push((
        "generated_forall".to_string(),
        JsonValue::JsonString(user_visible_stmt_or_msg_text(
            &verification.generated_forall,
        )),
    ));
    JsonValue::Object(fields)
}

fn induction_case_value(
    runtime: &Runtime,
    assumptions: &[(String, String)],
    proof_step_count: usize,
    results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let proof_end = std::cmp::min(proof_step_count, results.len());
    JsonValue::Object(vec![
        (
            "assumptions".to_string(),
            JsonValue::Array(assumption_pair_values(assumptions)),
        ),
        (
            "proof_steps".to_string(),
            JsonValue::Array(
                results[..proof_end]
                    .iter()
                    .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
                    .collect::<Vec<_>>(),
            ),
        ),
        (
            JSON_KEY_CONCLUSIONS.to_string(),
            JsonValue::Array(
                results[proof_end..]
                    .iter()
                    .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
                    .collect::<Vec<_>>(),
            ),
        ),
    ])
}

fn by_extension_verification_value(
    runtime: &Runtime,
    verification: &ByExtensionVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let proof_steps = proof_step_values(
        runtime,
        inside_results,
        verification.proof_step_count,
        output_style,
    );
    let subset_results = inside_results.iter().skip(verification.proof_step_count);
    let subset_checks = vec![
        ("left_to_right", verification.left_to_right_subset.as_str()),
        ("right_to_left", verification.right_to_left_subset.as_str()),
    ]
    .into_iter()
    .zip(subset_results)
    .map(|((direction, statement), result)| {
        JsonValue::Object(vec![
            (
                "direction".to_string(),
                JsonValue::JsonString(direction.to_string()),
            ),
            (
                JSON_KEY_STMT.to_string(),
                JsonValue::JsonString(user_visible_stmt_or_msg_text(statement)),
            ),
            (
                JSON_KEY_VERIFICATION.to_string(),
                stmt_result_to_composite_step_verified_by(runtime, result, output_style),
            ),
        ])
    })
    .collect::<Vec<_>>();

    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("by extension proof".to_string()),
        ),
        (
            "prove_goal".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&verification.prove_goal)),
        ),
        ("proof_steps".to_string(), JsonValue::Array(proof_steps)),
        ("subset_checks".to_string(), JsonValue::Array(subset_checks)),
        (
            "conclusion".to_string(),
            JsonValue::Object(vec![
                (
                    JSON_KEY_STMT.to_string(),
                    JsonValue::JsonString(user_visible_stmt_or_msg_text(&verification.prove_goal)),
                ),
                (
                    "reason".to_string(),
                    JsonValue::JsonString("set extensionality".to_string()),
                ),
            ]),
        ),
    ])
}

fn by_prop_registration_verification_value(
    runtime: &Runtime,
    verification: &ByPropRegistrationVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let proof_steps = proof_step_values(
        runtime,
        inside_results,
        verification.proof_step_count,
        output_style,
    );
    let conclusions = verification
        .forall_fact
        .then_facts
        .iter()
        .zip(inside_results.iter().skip(verification.proof_step_count))
        .map(|(stmt, result)| {
            forall_proved_fact_value(
                runtime,
                &verification.forall_fact,
                stmt,
                result,
                output_style,
            )
        })
        .collect::<Vec<_>>();

    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("by prop registration proof".to_string()),
        ),
        (
            "registration".to_string(),
            JsonValue::JsonString(verification.registration_type.clone()),
        ),
        (
            "prop".to_string(),
            JsonValue::JsonString(verification.prop_name.clone()),
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

fn by_choice_verification_value(
    runtime: &Runtime,
    verification: &ByChoiceVerificationResult,
    inside_results: &[StmtResult],
    conclusion_key: &str,
    output_style: OutputStyle,
) -> JsonValue {
    let proof_steps = proof_step_values(
        runtime,
        inside_results,
        verification.proof_step_count,
        output_style,
    );
    let mut result_cursor = verification.proof_step_count;
    let mut obligations = Vec::new();
    for (label, statement, has_check_result) in verification.obligations.iter() {
        if *has_check_result {
            if let Some(result) = inside_results.get(result_cursor) {
                result_cursor += 1;
                obligations.push(JsonValue::Object(vec![
                    ("label".to_string(), JsonValue::JsonString(label.clone())),
                    (
                        JSON_KEY_STMT.to_string(),
                        JsonValue::JsonString(user_visible_stmt_or_msg_text(statement)),
                    ),
                    (
                        JSON_KEY_VERIFICATION.to_string(),
                        stmt_result_to_composite_step_verified_by(runtime, result, output_style),
                    ),
                ]));
            }
        } else {
            obligations.push(JsonValue::Object(vec![
                ("label".to_string(), JsonValue::JsonString(label.clone())),
                (
                    JSON_KEY_STMT.to_string(),
                    JsonValue::JsonString(user_visible_stmt_or_msg_text(statement)),
                ),
                (
                    JSON_KEY_VERIFICATION.to_string(),
                    JsonValue::Object(vec![(
                        "type".to_string(),
                        JsonValue::JsonString("proved in proof steps".to_string()),
                    )]),
                ),
            ]));
        }
    }

    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString(verification.proof_type.clone()),
        ),
        (
            "target".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&verification.target)),
        ),
        ("proof_steps".to_string(), JsonValue::Array(proof_steps)),
        ("obligations".to_string(), JsonValue::Array(obligations)),
        (
            conclusion_key.to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(
                &verification.trusted_conclusion,
            )),
        ),
    ])
}

fn by_theorem_verification_value(
    runtime: &Runtime,
    verification: &ByTheoremVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let is_litex_theorem = verification.theorem_source == "litex";
    let parameter_type_check = if is_litex_theorem {
        inside_results
            .first()
            .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
            .unwrap_or_else(|| JsonValue::Object(vec![]))
    } else {
        JsonValue::Object(vec![])
    };
    let domain_checks = if is_litex_theorem {
        verification
            .domain_facts
            .iter()
            .zip(inside_results.iter().skip(1))
            .map(|(statement, result)| {
                statement_check_value(runtime, "domain", statement, result, output_style)
            })
            .collect::<Vec<_>>()
    } else {
        vec![]
    };
    let requirement_checks = verification
        .requirement_roles
        .iter()
        .zip(verification.domain_facts.iter())
        .zip(inside_results.iter())
        .map(|((role, statement), result)| {
            statement_check_value(runtime, role, statement, result, output_style)
        })
        .collect::<Vec<_>>();
    let target_check = if verification.selected_fact.is_some() {
        inside_results
            .last()
            .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
            .unwrap_or(JsonValue::Null)
    } else {
        JsonValue::Null
    };

    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("by thm proof".to_string()),
        ),
        (
            "mode".to_string(),
            JsonValue::JsonString(verification.mode.clone()),
        ),
        (
            "theorem".to_string(),
            JsonValue::JsonString(verification.theorem.clone()),
        ),
        (
            "theorem_source".to_string(),
            JsonValue::JsonString(verification.theorem_source.clone()),
        ),
        (
            "arguments".to_string(),
            JsonValue::Array(string_items(&verification.arguments)),
        ),
        ("parameter_type_check".to_string(), parameter_type_check),
        ("domain_checks".to_string(), JsonValue::Array(domain_checks)),
        (
            "requirement_checks".to_string(),
            JsonValue::Array(requirement_checks),
        ),
        (
            "stored_then_facts".to_string(),
            JsonValue::Array(string_items(&verification.stored_then_facts)),
        ),
        (
            "temporary_then_facts".to_string(),
            JsonValue::Array(string_items(&verification.temporary_then_facts)),
        ),
        (
            "selected_fact".to_string(),
            verification
                .selected_fact
                .as_ref()
                .map(|fact| JsonValue::JsonString(user_visible_stmt_or_msg_text(fact)))
                .unwrap_or(JsonValue::Null),
        ),
        ("target_check".to_string(), target_check),
        (
            "parent_stored_facts".to_string(),
            JsonValue::Array(string_items(&verification.parent_stored_facts)),
        ),
        (
            "provenance".to_string(),
            verification
                .provenance
                .as_ref()
                .map(|value| JsonValue::JsonString(value.clone()))
                .unwrap_or(JsonValue::Null),
        ),
    ])
}

fn by_definition_verification_value(
    runtime: &Runtime,
    verification: &ByDefinitionVerificationResult,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let has_parameter_type_check =
        inside_results.len() == verification.definition_clauses.len() + 1;
    let parameter_type_check = if has_parameter_type_check {
        inside_results
            .first()
            .map(|result| stmt_exec_result_json_value(runtime, result, output_style))
            .unwrap_or_else(|| JsonValue::Object(vec![]))
    } else {
        JsonValue::Object(vec![])
    };
    let clause_results = if has_parameter_type_check {
        &inside_results[1..]
    } else {
        inside_results
    };
    let definition_clause_checks = verification
        .definition_clauses
        .iter()
        .zip(clause_results.iter())
        .enumerate()
        .map(|(index, (statement, result))| {
            statement_check_value(
                runtime,
                if has_parameter_type_check {
                    format!("definition clause {}", index + 1)
                } else {
                    format!("builtin definition check {}", index + 1)
                }
                .as_str(),
                statement,
                result,
                output_style,
            )
        })
        .collect::<Vec<_>>();

    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("by definition proof".to_string()),
        ),
        (
            "prop".to_string(),
            JsonValue::JsonString(verification.prop.clone()),
        ),
        (
            "arguments".to_string(),
            JsonValue::Array(string_items(&verification.arguments)),
        ),
        ("parameter_type_check".to_string(), parameter_type_check),
        (
            "definition_clause_checks".to_string(),
            JsonValue::Array(definition_clause_checks),
        ),
        (
            "stored_fact".to_string(),
            JsonValue::JsonString(verification.stored_fact.clone()),
        ),
    ])
}

fn impossible_verification_value(
    runtime: &Runtime,
    impossible_fact: &crate::prelude::AtomicFact,
    result: Option<&StmtResult>,
    output_style: OutputStyle,
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
                output_style,
            )),
        ),
    ])
}

fn impossible_check_values(
    runtime: &Runtime,
    impossible_fact: &crate::prelude::AtomicFact,
    results: &[&StmtResult],
    output_style: OutputStyle,
) -> Vec<JsonValue> {
    let mut facts_and_roles = vec![(impossible_fact.clone().into(), "impossible fact")];
    if let Ok(negated) = impossible_fact.logical_negation() {
        facts_and_roles.push((negated.into(), "negated impossible fact"));
    }
    facts_and_roles
        .into_iter()
        .zip(results.iter())
        .map(|((fact, role), result)| fact_check_value(runtime, role, &fact, result, output_style))
        .collect::<Vec<_>>()
}

fn fact_check_value(
    runtime: &Runtime,
    role: &str,
    fact: &crate::prelude::Fact,
    result: &StmtResult,
    output_style: OutputStyle,
) -> JsonValue {
    JsonValue::Object(vec![
        ("role".to_string(), JsonValue::JsonString(role.to_string())),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&fact.to_string())),
        ),
        (
            JSON_KEY_VERIFICATION.to_string(),
            stmt_result_to_composite_step_verified_by(runtime, result, output_style),
        ),
    ])
}

fn statement_check_value(
    runtime: &Runtime,
    role: &str,
    statement: &str,
    result: &StmtResult,
    output_style: OutputStyle,
) -> JsonValue {
    JsonValue::Object(vec![
        ("role".to_string(), JsonValue::JsonString(role.to_string())),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(statement)),
        ),
        (
            JSON_KEY_VERIFICATION.to_string(),
            stmt_result_to_composite_step_verified_by(runtime, result, output_style),
        ),
    ])
}

fn string_items(items: &[String]) -> Vec<JsonValue> {
    items
        .iter()
        .map(|item| JsonValue::JsonString(user_visible_stmt_or_msg_text(item)))
        .collect::<Vec<_>>()
}

fn string_pair_object(items: &[(String, String)]) -> JsonValue {
    JsonValue::Object(
        items
            .iter()
            .map(|(key, value)| {
                (
                    key.clone(),
                    JsonValue::JsonString(user_visible_stmt_or_msg_text(value)),
                )
            })
            .collect::<Vec<_>>(),
    )
}

fn assumption_pair_values(items: &[(String, String)]) -> Vec<JsonValue> {
    items
        .iter()
        .map(|(fact, reason)| local_assumption_fact_value(fact, reason))
        .collect::<Vec<_>>()
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
    _stmt: &Stmt,
    inside_results: &[StmtResult],
    output_style: OutputStyle,
) -> JsonValue {
    let should_show_inside_results = output_style != OutputStyle::Compact;
    if !should_show_inside_results {
        return JsonValue::Array(vec![]);
    }

    JsonValue::Array(
        inside_results
            .iter()
            .map(|r| stmt_exec_result_json_value(runtime, r, output_style))
            .collect::<Vec<_>>(),
    )
}

fn factual_stmt_success_to_json(
    runtime: &Runtime,
    x: &FactualStmtSuccess,
    output_style: OutputStyle,
) -> JsonValue {
    if x.is_verified_by_builtin_rules_only() {
        factual_builtin_rules_to_json(runtime, x, output_style)
    } else {
        factual_citation_to_json(runtime, x, output_style)
    }
}

fn factual_builtin_rules_to_json(
    runtime: &Runtime,
    x: &FactualStmtSuccess,
    output_style: OutputStyle,
) -> JsonValue {
    let fact_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());

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
    add_statement_trust_fields(x.execution_trace.as_ref(), &mut fields);

    fields.extend(factual_success_forall_proof_fields(
        runtime,
        x,
        output_style,
    ));
    if !factual_success_is_forall_proof(x) {
        fields.push((
            JSON_KEY_VERIFICATION.to_string(),
            factual_success_verified_by_value(runtime, x, output_style),
        ));
    }
    fields.push(("inside_results".to_string(), JsonValue::Array(vec![])));

    add_factual_execution_phases(runtime, x, &mut fields, output_style);

    JsonValue::Object(fields)
}

fn factual_citation_to_json(
    runtime: &Runtime,
    x: &FactualStmtSuccess,
    output_style: OutputStyle,
) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());

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
    add_statement_trust_fields(x.execution_trace.as_ref(), &mut fields);

    fields.extend(factual_success_forall_proof_fields(
        runtime,
        x,
        output_style,
    ));
    if !factual_success_is_forall_proof(x) {
        fields.push((
            JSON_KEY_VERIFICATION.to_string(),
            factual_success_verified_by_value(runtime, x, output_style),
        ));
    }
    fields.push(("inside_results".to_string(), JsonValue::Array(vec![])));

    add_factual_execution_phases(runtime, x, &mut fields, output_style);

    JsonValue::Object(fields)
}

fn add_statement_trust_fields(
    trace: Option<&StatementExecutionTrace>,
    fields: &mut Vec<(String, JsonValue)>,
) {
    let Some(trace) = trace else {
        return;
    };
    if let Some(status) = trace.verification_status.as_ref() {
        fields.push((
            "verification_status".to_string(),
            JsonValue::JsonString(status.clone()),
        ));
    }
}

fn add_factual_execution_phases(
    runtime: &Runtime,
    x: &FactualStmtSuccess,
    fields: &mut Vec<(String, JsonValue)>,
    output_style: OutputStyle,
) {
    if !output_style.is_detailed() {
        return;
    }
    let Some(trace) = x.execution_trace.as_ref() else {
        return;
    };
    let mut process_fields = if factual_success_is_forall_proof(x) {
        factual_success_forall_proof_fields(runtime, x, output_style)
    } else {
        vec![(
            JSON_KEY_VERIFICATION.to_string(),
            factual_success_verified_by_value(runtime, x, output_style),
        )]
    };
    if process_fields.is_empty() {
        process_fields.push((
            JSON_KEY_VERIFICATION.to_string(),
            factual_success_verified_by_value(runtime, x, output_style),
        ));
    }
    fields.push((
        "phases".to_string(),
        execution_phases_value(
            trace,
            well_definedness_checks_for_fact(&x.stmt),
            process_fields,
            environment_effect_values(&x.stmt.clone().into(), &x.infers, trace),
        ),
    ));
}

fn well_definedness_checks_for_stmt(stmt: &Stmt) -> Vec<JsonValue> {
    match stmt {
        Stmt::Fact(fact) => well_definedness_checks_for_fact(fact),
        Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(have_stmt)) => {
            let mut checks = parameter_binding_checks(&have_stmt.param_def);
            checks.push(JsonValue::Object(vec![
                (
                    "kind".to_string(),
                    JsonValue::JsonString("arity".to_string()),
                ),
                (
                    "expected".to_string(),
                    JsonValue::Number(have_stmt.param_def.number_of_params()),
                ),
                (
                    "actual".to_string(),
                    JsonValue::Number(have_stmt.objs_equal_to.len()),
                ),
            ]));
            checks
        }
        _ => vec![statement_well_defined_check(&stmt.to_string())],
    }
}

fn well_definedness_checks_for_fact(fact: &Fact) -> Vec<JsonValue> {
    let Fact::ForallFact(forall_fact) = fact else {
        return vec![statement_well_defined_check(&fact.to_string())];
    };
    let mut checks = parameter_binding_checks(&forall_fact.params_def_with_type);
    for premise in forall_fact.dom_facts.iter() {
        checks.push(well_defined_fact_check(&premise.to_string()));
    }
    for conclusion in forall_fact.then_facts.iter() {
        checks.push(well_defined_fact_check(&conclusion.to_string()));
    }
    checks
}

fn parameter_binding_checks(param_def: &ParamDefWithType) -> Vec<JsonValue> {
    param_def
        .collect_param_names_with_types()
        .into_iter()
        .map(|(name, param_type)| {
            JsonValue::Object(vec![
                (
                    "kind".to_string(),
                    JsonValue::JsonString("parameter_binding".to_string()),
                ),
                ("name".to_string(), JsonValue::JsonString(name)),
                (
                    "type".to_string(),
                    JsonValue::JsonString(param_type.to_string()),
                ),
            ])
        })
        .collect::<Vec<_>>()
}

fn statement_well_defined_check(statement: &str) -> JsonValue {
    JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString("statement_well_defined".to_string()),
        ),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(statement)),
        ),
    ])
}

fn well_defined_fact_check(statement: &str) -> JsonValue {
    JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString("well_defined_fact".to_string()),
        ),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(statement)),
        ),
    ])
}

fn environment_effect_values(
    stmt: &Stmt,
    infers: &InferResult,
    trace: &StatementExecutionTrace,
) -> Vec<JsonValue> {
    let mut effects = statement_environment_effects(stmt, trace);
    for store_fact in store_fact_json_values(infers) {
        let JsonValue::Object(mut fields) = store_fact else {
            continue;
        };
        fields.insert(
            0,
            (
                "kind".to_string(),
                JsonValue::JsonString("store_fact".to_string()),
            ),
        );
        effects.push(JsonValue::Object(fields));
    }
    effects
}

fn statement_environment_effects(stmt: &Stmt, trace: &StatementExecutionTrace) -> Vec<JsonValue> {
    match stmt {
        Stmt::DefObjStmt(DefObjStmt::LetObjStmt(let_stmt)) => {
            vec![JsonValue::Object(vec![
                (
                    "kind".to_string(),
                    JsonValue::JsonString("declare_object".to_string()),
                ),
                (
                    "name".to_string(),
                    JsonValue::JsonString(let_stmt.name.clone()),
                ),
                (
                    "value".to_string(),
                    JsonValue::JsonString(user_visible_stmt_or_msg_text(
                        &let_stmt.value.to_string(),
                    )),
                ),
            ])]
        }
        Stmt::DefObjStmt(DefObjStmt::HaveObjEqualStmt(have_stmt)) => have_stmt
            .param_def
            .collect_param_names_with_types()
            .into_iter()
            .zip(have_stmt.objs_equal_to.iter())
            .map(|((name, param_type), value)| {
                JsonValue::Object(vec![
                    (
                        "kind".to_string(),
                        JsonValue::JsonString("declare_object".to_string()),
                    ),
                    ("name".to_string(), JsonValue::JsonString(name)),
                    (
                        "type".to_string(),
                        JsonValue::JsonString(param_type.to_string()),
                    ),
                    (
                        "value".to_string(),
                        JsonValue::JsonString(user_visible_stmt_or_msg_text(&value.to_string())),
                    ),
                ])
            })
            .collect::<Vec<_>>(),
        Stmt::DefObjStmt(_) => vec![statement_environment_effect("declare_object", stmt)],
        Stmt::DefPredicateStmt(_) => vec![statement_environment_effect("define_predicate", stmt)],
        Stmt::DefInterfaceStmt(_) => vec![statement_environment_effect("define_interface", stmt)],
        Stmt::DefAlgoStmt(_) => vec![statement_environment_effect("define_algorithm", stmt)],
        Stmt::DefThmStmt(_) => vec![statement_environment_effect("define_theorem", stmt)],
        Stmt::DefStrategyStmt(_) => vec![statement_environment_effect("define_strategy", stmt)],
        Stmt::Command(CommandStmt::ClearStmt(_)) => {
            vec![statement_environment_effect("clear_environment", stmt)]
        }
        Stmt::Command(CommandStmt::UseStrategyStmt(_)) => {
            vec![statement_environment_effect("activate_strategy", stmt)]
        }
        Stmt::Command(CommandStmt::StopStrategyStmt(_)) => {
            vec![statement_environment_effect("stop_strategy", stmt)]
        }
        _ if trace.verify_well_definedness.status == StatementPhaseStatus::Skipped => {
            let effect_kind = if trace.verification_status.as_deref() == Some("trusted_prefix") {
                "trusted_prefix_environment_load"
            } else {
                "trusted_environment_load"
            };
            vec![statement_environment_effect(effect_kind, stmt)]
        }
        _ => vec![],
    }
}

fn statement_environment_effect(kind: &str, stmt: &Stmt) -> JsonValue {
    JsonValue::Object(vec![
        ("kind".to_string(), JsonValue::JsonString(kind.to_string())),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&stmt.to_string())),
        ),
    ])
}

fn factual_success_is_forall_proof(x: &FactualStmtSuccess) -> bool {
    matches!(x.underlying_verified_by(), VerifiedByResult::ForallProof(_))
}
