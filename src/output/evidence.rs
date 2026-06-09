use crate::common::json_value::JsonValue;
use crate::prelude::*;

use super::fields::{user_visible_stmt_or_msg_text, JSON_KEY_STEPS};
use super::source::source_ref_json_value;

fn verified_by_builtin_rule_value(rule: &str, verify_what: Option<&Fact>) -> JsonValue {
    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString("builtin rule".to_string()),
        ),
        ("rule".to_string(), JsonValue::JsonString(rule.to_string())),
    ];
    if let Some(vw) = verify_what {
        fields.push((
            "verify_what".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&vw.to_string())),
        ));
    }
    fields.push((JSON_KEY_STEPS.to_string(), JsonValue::Array(vec![])));
    JsonValue::Object(fields)
}

/// `verified_by` field for one [`FactualStmtSuccess`] (builtin rule or citation).
pub(crate) fn factual_success_verified_by_value(
    runtime: &Runtime,
    x: &FactualStmtSuccess,
) -> JsonValue {
    let current_line_file = x.stmt.line_file();
    verified_by_result_json_value(runtime, &x.verified_by, &current_line_file, Some(&x.stmt))
}

fn verified_by_result_json_value(
    runtime: &Runtime,
    verified_by: &VerifiedByResult,
    current_line_file: &LineFile,
    verify_goal: Option<&Fact>,
) -> JsonValue {
    match verified_by {
        VerifiedByResult::BuiltinRule(r) => verified_by_builtin_rule_value(&r.msg, None),
        VerifiedByResult::Fact(r) => {
            let citation_type = citation_type_for_stmt(r.cite_what.as_ref());
            let cited_stmt_plain = user_visible_stmt_or_msg_text(&r.cite_what.to_string());
            let citation_line_file = r.cite_what.line_file();
            let display_text = r
                .detail
                .as_deref()
                .filter(|s| !s.is_empty())
                .map(user_visible_stmt_or_msg_text)
                .unwrap_or_else(|| cited_stmt_plain.clone());
            let cited_stmt_json = JsonValue::JsonString(cited_stmt_plain.clone());
            verified_by_citation_object(
                runtime,
                &citation_line_file,
                current_line_file,
                citation_type.as_str(),
                cited_stmt_json,
                cited_stmt_plain.as_str(),
                display_text.as_str(),
                None,
            )
        }
        VerifiedByResult::VerifiedBys(w) => {
            verified_by_steps_object(runtime, &w.cite_what, current_line_file, verify_goal)
        }
    }
}

fn verified_by_steps_object(
    runtime: &Runtime,
    items: &[VerifiedBysEnum],
    current_line_file: &LineFile,
    verify_goal: Option<&Fact>,
) -> JsonValue {
    let steps = items
        .iter()
        .map(|item| verified_bys_enum_json_value(runtime, item, current_line_file))
        .collect::<Vec<_>>();
    let mut fields = vec![(
        "type".to_string(),
        JsonValue::JsonString(verified_by_steps_type(verify_goal).to_string()),
    )];
    if let Some(summary) = verified_by_steps_summary(verify_goal) {
        fields.push((
            "summary".to_string(),
            JsonValue::JsonString(summary.to_string()),
        ));
    }
    fields.push((JSON_KEY_STEPS.to_string(), JsonValue::Array(steps)));
    JsonValue::Object(fields)
}

fn verified_by_steps_type(verify_goal: Option<&Fact>) -> &'static str {
    match verify_goal {
        Some(Fact::ForallFact(_)) => "forall local check",
        Some(Fact::ForallFactWithIff(_)) => "forall iff local check",
        Some(Fact::AndFact(_)) => "and fact",
        Some(Fact::ChainFact(_)) => "chain fact",
        Some(Fact::OrFact(_)) => "or fact",
        Some(Fact::ExistFact(_)) => "exist fact",
        Some(Fact::NotForall(_)) => "not forall fact",
        Some(Fact::AtomicFact(_)) | None => "verification steps",
    }
}

fn verified_by_steps_summary(verify_goal: Option<&Fact>) -> Option<&'static str> {
    match verify_goal {
        Some(Fact::ForallFact(_)) => Some("then facts verified in local forall context"),
        Some(Fact::ForallFactWithIff(_)) => {
            Some("both directions verified in local forall contexts")
        }
        Some(Fact::AndFact(_)) => Some("each conjunct verified in order"),
        Some(Fact::ChainFact(_)) => Some("each chain step verified in order"),
        Some(Fact::OrFact(_)) => Some("one or more disjunctive proof routes verified"),
        Some(Fact::ExistFact(_)) => Some("existential proof obligations verified"),
        Some(Fact::NotForall(_)) => Some("negated universal proof obligations verified"),
        Some(Fact::AtomicFact(_)) | None => None,
    }
}

fn verified_bys_enum_json_value(
    runtime: &Runtime,
    item: &VerifiedBysEnum,
    current_line_file: &LineFile,
) -> JsonValue {
    match item {
        VerifiedBysEnum::ByBuiltinRule(r) => {
            verified_by_builtin_rule_value(&r.msg, Some(&r.verify_what))
        }
        VerifiedBysEnum::ByFact(r) => {
            let citation_type = citation_type_for_stmt(r.cite_what.as_ref());
            let cited_stmt_plain = user_visible_stmt_or_msg_text(&r.cite_what.to_string());
            let citation_line_file = r.cite_what.line_file();
            let display_text = r
                .detail
                .as_deref()
                .filter(|s| !s.is_empty())
                .map(user_visible_stmt_or_msg_text)
                .unwrap_or_else(|| cited_stmt_plain.clone());
            verified_by_citation_object(
                runtime,
                &citation_line_file,
                current_line_file,
                citation_type.as_str(),
                JsonValue::JsonString(cited_stmt_plain.clone()),
                cited_stmt_plain.as_str(),
                display_text.as_str(),
                Some(&r.verify_what),
            )
        }
    }
}

pub(crate) fn stmt_result_to_composite_step_verified_by(
    runtime: &Runtime,
    r: &StmtResult,
) -> JsonValue {
    match r {
        StmtResult::FactualStmtSuccess(f) => factual_success_verified_by_value(runtime, f),
        StmtResult::NonFactualStmtSuccess(n) => JsonValue::Object(vec![
            (
                "type".to_string(),
                JsonValue::JsonString("accepted statement".to_string()),
            ),
            (
                "stmt_type".to_string(),
                JsonValue::JsonString(n.stmt.stmt_type_name().to_string()),
            ),
        ]),
        StmtResult::StmtUnknown(_) => JsonValue::Object(vec![(
            "type".to_string(),
            JsonValue::JsonString("unknown".to_string()),
        )]),
    }
}

fn citation_type_for_stmt(stmt: &Stmt) -> String {
    match stmt {
        Stmt::Fact(fact) => format!("cite {}", citation_fact_type_label(fact)),
        Stmt::DefInterfaceStmt(DefInterfaceStmt::DefPropStmt(_)) => "cite prop def".to_string(),
        Stmt::DefInterfaceStmt(DefInterfaceStmt::DefAbstractPropStmt(_)) => {
            "cite abstract prop def".to_string()
        }
        Stmt::UnsafeStmt(UnsafeStmt::DefLetStmt(_)) => "cite let def".to_string(),
        Stmt::DefInterfaceStmt(DefInterfaceStmt::DefAlgoStmt(_)) => "cite algo def".to_string(),
        Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(_)) => "cite struct def".to_string(),
        _ => format!("cite {} stmt", stmt_type_label_for_citation(stmt)),
    }
}

fn citation_fact_type_label(fact: &Fact) -> &'static str {
    match fact {
        Fact::AtomicFact(_) => "atomic fact",
        Fact::ExistFact(_) => "exist fact",
        Fact::OrFact(_) => "or fact",
        Fact::AndFact(_) => "and fact",
        Fact::ChainFact(_) => "chain fact",
        Fact::ForallFact(_) => "forall fact",
        Fact::ForallFactWithIff(_) => "forall iff fact",
        Fact::NotForall(_) => "not forall fact",
    }
}

fn stmt_type_label_for_citation(stmt: &Stmt) -> String {
    let stmt_type_name = stmt.stmt_type_name();
    let base_name = stmt_type_name
        .strip_suffix("Stmt")
        .unwrap_or(stmt_type_name.as_str());
    lower_camel_case_words(base_name)
}

fn lower_camel_case_words(input: &str) -> String {
    let mut out = String::new();
    let mut prev_is_lower_or_digit = false;
    for ch in input.chars() {
        if ch.is_ascii_uppercase() {
            if prev_is_lower_or_digit && !out.is_empty() {
                out.push(' ');
            }
            out.push(ch.to_ascii_lowercase());
            prev_is_lower_or_digit = false;
        } else {
            out.push(ch);
            prev_is_lower_or_digit = ch.is_ascii_lowercase() || ch.is_ascii_digit();
        }
    }
    out
}

fn verified_by_citation_object(
    runtime: &Runtime,
    citation_line_file: &LineFile,
    current_line_file: &LineFile,
    citation_type: &str,
    cited_stmt: JsonValue,
    cited_stmt_plain: &str,
    msg: &str,
    verify_what: Option<&Fact>,
) -> JsonValue {
    let cite_source = source_ref_json_value(runtime, citation_line_file, Some(current_line_file));
    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString(citation_type.to_string()),
        ),
        ("cite_source".to_string(), cite_source),
        ("cited_stmt".to_string(), cited_stmt),
    ];
    if msg != cited_stmt_plain {
        fields.push(("detail".to_string(), JsonValue::JsonString(msg.to_string())));
    }
    if let Some(vw) = verify_what {
        fields.push((
            "verify_what".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&vw.to_string())),
        ));
    }
    fields.push((JSON_KEY_STEPS.to_string(), JsonValue::Array(vec![])));
    JsonValue::Object(fields)
}
