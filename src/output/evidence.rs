use crate::common::json_value::JsonValue;
use crate::prelude::*;

use super::fields::{
    user_visible_stmt_or_msg_text, JSON_KEY_CONCLUSIONS_WITH_VERIFICATION, JSON_KEY_STEPS,
    JSON_KEY_STMT, JSON_KEY_VERIFICATION,
};
use super::source::{source_ref_json_value, stmt_text_for_json};

fn verified_by_builtin_rule_value(
    runtime: &Runtime,
    rule: &str,
    verify_what: Option<&Fact>,
    subgoals: &[StmtResult],
) -> JsonValue {
    let public_rule = builtin_rule_public_text(rule);
    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString("builtin rule".to_string()),
        ),
        ("rule".to_string(), JsonValue::JsonString(public_rule)),
    ];
    if let Some(vw) = verify_what {
        fields.push((
            "verify_what".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&vw.to_string())),
        ));
    }
    fields.push((
        "subgoals".to_string(),
        JsonValue::Array(subgoal_values(runtime, subgoals)),
    ));
    fields.push((JSON_KEY_STEPS.to_string(), JsonValue::Array(vec![])));
    JsonValue::Object(fields)
}

/// Public `verification` field for one [`FactualStmtSuccess`] (builtin rule or citation).
pub(crate) fn factual_success_verified_by_value(
    runtime: &Runtime,
    x: &FactualStmtSuccess,
) -> JsonValue {
    let current_line_file = x.stmt.line_file();
    verified_by_result_json_value(runtime, &x.verified_by, &current_line_file, Some(&x.stmt))
}

pub(crate) fn factual_success_forall_proof_fields(
    runtime: &Runtime,
    x: &FactualStmtSuccess,
) -> Vec<(String, JsonValue)> {
    match &x.verified_by {
        VerifiedByResult::ForallProof(proof) => forall_proof_top_level_fields(runtime, proof),
        _ => vec![],
    }
}

fn verified_by_result_json_value(
    runtime: &Runtime,
    verified_by: &VerifiedByResult,
    current_line_file: &LineFile,
    verify_goal: Option<&Fact>,
) -> JsonValue {
    match verified_by {
        VerifiedByResult::BuiltinRule(r) => {
            verified_by_builtin_rule_value(runtime, &r.msg, None, &r.subgoals)
        }
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
        VerifiedByResult::KnownForallInstantiation(r) => {
            known_forall_instantiation_json_value(runtime, current_line_file, r, None)
        }
        VerifiedByResult::VerifiedBys(w) => {
            verified_by_steps_object(runtime, &w.cite_what, current_line_file, verify_goal)
        }
        VerifiedByResult::ForallProof(proof) => {
            JsonValue::Object(forall_proof_top_level_fields(runtime, proof))
        }
    }
}

fn forall_proof_top_level_fields(
    runtime: &Runtime,
    proof: &ForallProofResult,
) -> Vec<(String, JsonValue)> {
    let conclusions_with_verification = proof
        .proves
        .iter()
        .map(|proved| forall_proved_fact_value(runtime, proof, proved))
        .collect::<Vec<_>>();

    let mut fields = Vec::new();
    if runtime.detail_output {
        fields.push((
            "parameters".to_string(),
            JsonValue::Array(forall_param_items(&proof.forall_fact.params_def_with_type)),
        ));
        fields.push((
            "assumptions".to_string(),
            JsonValue::Array(forall_assumption_items(proof)),
        ));
    }
    fields.push((
        JSON_KEY_CONCLUSIONS_WITH_VERIFICATION.to_string(),
        JsonValue::Array(conclusions_with_verification),
    ));
    fields
}

fn forall_param_items(param_defs: &ParamDefWithType) -> Vec<JsonValue> {
    param_defs
        .collect_param_names()
        .into_iter()
        .map(|name| JsonValue::JsonString(user_visible_stmt_or_msg_text(&name)))
        .collect::<Vec<_>>()
}

fn forall_assumption_items(proof: &ForallProofResult) -> Vec<JsonValue> {
    let mut facts = forall_param_type_assumption_facts(&proof.forall_fact.params_def_with_type);
    facts.extend(proof.forall_fact.dom_facts.iter().cloned());
    facts
        .iter()
        .map(|fact| JsonValue::JsonString(user_visible_stmt_or_msg_text(&fact.to_string())))
        .collect::<Vec<_>>()
}

fn forall_local_assumption_value(source: &str) -> JsonValue {
    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("local assumption".to_string()),
        ),
        (
            "source".to_string(),
            JsonValue::JsonString(source.to_string()),
        ),
    ])
}

fn forall_proved_fact_value(
    runtime: &Runtime,
    proof: &ForallProofResult,
    proved: &ForallProvedFactResult,
) -> JsonValue {
    let stmt_text = user_visible_stmt_or_msg_text(&proved.stmt.to_string());
    let verification = match forall_local_assumption_source(proof, &proved.stmt) {
        Some(source) => forall_local_assumption_value(source),
        None => stmt_result_to_composite_step_verified_by(runtime, proved.result.as_ref()),
    };
    JsonValue::Object(vec![
        (JSON_KEY_STMT.to_string(), JsonValue::JsonString(stmt_text)),
        (JSON_KEY_VERIFICATION.to_string(), verification),
    ])
}

fn forall_local_assumption_source(
    proof: &ForallProofResult,
    stmt: &ExistOrAndChainAtomicFact,
) -> Option<&'static str> {
    let target = stmt.clone().to_fact().to_string();
    for fact in forall_param_type_assumption_facts(&proof.forall_fact.params_def_with_type) {
        if fact.to_string() == target {
            return Some("parameter declaration");
        }
    }
    for fact in proof.forall_fact.dom_facts.iter() {
        if fact.to_string() == target {
            return Some("forall premise");
        }
    }
    None
}

fn forall_param_type_assumption_facts(param_defs: &ParamDefWithType) -> Vec<Fact> {
    let mut facts = Vec::new();
    for (name, param_type) in param_defs.collect_param_names_with_types() {
        let param_obj = param_binding_element_obj_for_store(name, ParamObjType::Forall);
        let fact = match param_type {
            ParamType::Obj(obj) => InFact::new(param_obj, obj, default_line_file()).into(),
            ParamType::Set(_) => IsSetFact::new(param_obj, default_line_file()).into(),
            ParamType::NonemptySet(_) => {
                IsNonemptySetFact::new(param_obj, default_line_file()).into()
            }
            ParamType::FiniteSet(_) => IsFiniteSetFact::new(param_obj, default_line_file()).into(),
        };
        facts.push(fact);
    }
    facts
}

fn verified_by_steps_object(
    runtime: &Runtime,
    items: &[VerifiedBysEnum],
    current_line_file: &LineFile,
    verify_goal: Option<&Fact>,
) -> JsonValue {
    let steps = verified_by_step_items(runtime, items, current_line_file, verify_goal);
    let mut fields = Vec::new();
    if runtime.detail_output {
        fields.push((
            "type".to_string(),
            JsonValue::JsonString(verified_by_steps_type(verify_goal).to_string()),
        ));
    }
    if let Some(summary) = verified_by_steps_summary(verify_goal) {
        fields.push((
            "summary".to_string(),
            JsonValue::JsonString(summary.to_string()),
        ));
    }
    if runtime.detail_output {
        if let Some(main_rule) = verified_by_steps_main_rule(verify_goal) {
            fields.push((
                "main_rule".to_string(),
                JsonValue::JsonString(main_rule.to_string()),
            ));
        }
    }
    fields.push((JSON_KEY_STEPS.to_string(), JsonValue::Array(steps)));
    JsonValue::Object(fields)
}

fn verified_by_step_items(
    runtime: &Runtime,
    items: &[VerifiedBysEnum],
    current_line_file: &LineFile,
    verify_goal: Option<&Fact>,
) -> Vec<JsonValue> {
    let Some(role) = composite_step_role(verify_goal) else {
        return items
            .iter()
            .map(|item| verified_bys_enum_json_value(runtime, item, current_line_file, true))
            .collect::<Vec<_>>();
    };

    if let Some(folded) = folded_builtin_steps_value(runtime, items) {
        return vec![folded];
    }

    let count = items.len();
    items
        .iter()
        .enumerate()
        .map(|(idx, item)| {
            let evidence = verified_bys_enum_json_value(runtime, item, current_line_file, false);
            composite_step_value(runtime, role, idx + 1, count, item.verify_what(), evidence)
        })
        .collect::<Vec<_>>()
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

fn verified_by_steps_main_rule(verify_goal: Option<&Fact>) -> Option<&'static str> {
    match verify_goal {
        Some(Fact::AndFact(_)) => Some("and decomposition"),
        Some(Fact::ChainFact(_)) => Some("chain decomposition"),
        _ => None,
    }
}

fn composite_step_role(verify_goal: Option<&Fact>) -> Option<&'static str> {
    match verify_goal {
        Some(Fact::AndFact(_)) => Some("conjunct"),
        Some(Fact::ChainFact(_)) => Some("chain step"),
        _ => None,
    }
}

fn verified_bys_enum_json_value(
    runtime: &Runtime,
    item: &VerifiedBysEnum,
    current_line_file: &LineFile,
    include_verify_what: bool,
) -> JsonValue {
    match item {
        VerifiedBysEnum::ByBuiltinRule(r) => verified_by_builtin_rule_value(
            runtime,
            &r.msg,
            include_verify_what.then_some(&r.verify_what),
            &r.subgoals,
        ),
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
                include_verify_what.then_some(&r.verify_what),
            )
        }
        VerifiedBysEnum::ByKnownForall(r) => known_forall_instantiation_json_value(
            runtime,
            current_line_file,
            &r.result,
            include_verify_what.then_some(&r.verify_what),
        ),
    }
}

pub(crate) fn stmt_result_to_composite_step_verified_by(
    runtime: &Runtime,
    r: &StmtResult,
) -> JsonValue {
    if let Some(f) = r.factual_success() {
        factual_success_verified_by_value(runtime, f)
    } else if let Some(n) = r.non_factual_success() {
        JsonValue::Object(vec![
            (
                "type".to_string(),
                JsonValue::JsonString("accepted statement".to_string()),
            ),
            (
                "statement_type".to_string(),
                JsonValue::JsonString(n.stmt.stmt_type_name().to_string()),
            ),
        ])
    } else {
        JsonValue::Object(vec![(
            "type".to_string(),
            JsonValue::JsonString("unknown".to_string()),
        )])
    }
}

fn subgoal_values(runtime: &Runtime, subgoals: &[StmtResult]) -> Vec<JsonValue> {
    subgoals
        .iter()
        .map(|subgoal| subgoal_value(runtime, subgoal))
        .collect::<Vec<_>>()
}

fn subgoal_value(runtime: &Runtime, subgoal: &StmtResult) -> JsonValue {
    let mut fields = Vec::new();
    if let Some(f) = subgoal.factual_success() {
        fields.push((
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&f.stmt.to_string())),
        ));
        fields.push((
            JSON_KEY_VERIFICATION.to_string(),
            factual_success_verified_by_value(runtime, f),
        ));
    } else if let Some(n) = subgoal.non_factual_success() {
        fields.push((
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(stmt_text_for_json(runtime, &n.stmt)),
        ));
        fields.push((
            JSON_KEY_VERIFICATION.to_string(),
            stmt_result_to_composite_step_verified_by(runtime, subgoal),
        ));
    } else {
        fields.push((
            "type".to_string(),
            JsonValue::JsonString("unknown".to_string()),
        ));
    }
    JsonValue::Object(fields)
}

fn composite_step_value(
    runtime: &Runtime,
    role: &str,
    step_index: usize,
    step_count: usize,
    fact: &Fact,
    evidence: JsonValue,
) -> JsonValue {
    let fact_field = (
        "fact".to_string(),
        JsonValue::JsonString(user_visible_stmt_or_msg_text(&fact.to_string())),
    );
    if !runtime.detail_output {
        return JsonValue::Object(vec![
            (fact_field.0, fact_field.1),
            (JSON_KEY_VERIFICATION.to_string(), evidence),
        ]);
    }

    JsonValue::Object(vec![
        ("role".to_string(), JsonValue::JsonString(role.to_string())),
        ("step_index".to_string(), JsonValue::Number(step_index)),
        ("step_count".to_string(), JsonValue::Number(step_count)),
        (fact_field.0, fact_field.1),
        (JSON_KEY_VERIFICATION.to_string(), evidence),
    ])
}

fn folded_builtin_steps_value(runtime: &Runtime, items: &[VerifiedBysEnum]) -> Option<JsonValue> {
    if runtime.detail_output || items.len() < 2 {
        return None;
    }
    let first_rule = match items.first()? {
        VerifiedBysEnum::ByBuiltinRule(r) => r.msg.as_str(),
        _ => return None,
    };
    if items
        .iter()
        .any(|item| matches!(item, VerifiedBysEnum::ByBuiltinRule(r) if !r.subgoals.is_empty()))
    {
        return None;
    }
    if !items
        .iter()
        .all(|item| matches!(item, VerifiedBysEnum::ByBuiltinRule(r) if r.msg == first_rule))
    {
        return None;
    }

    let facts = items
        .iter()
        .map(|item| {
            JsonValue::JsonString(user_visible_stmt_or_msg_text(
                &item.verify_what().to_string(),
            ))
        })
        .collect::<Vec<_>>();
    Some(JsonValue::Object(vec![
        ("facts".to_string(), JsonValue::Array(facts)),
        (
            JSON_KEY_VERIFICATION.to_string(),
            verified_by_builtin_rule_value(runtime, first_rule, None, &[]),
        ),
    ]))
}

fn known_forall_instantiation_json_value(
    runtime: &Runtime,
    current_line_file: &LineFile,
    result: &KnownForallInstantiationResult,
    verify_what: Option<&Fact>,
) -> JsonValue {
    let citation_line_file = result.cite_what.line_file();
    let cite_source = source_ref_json_value(runtime, &citation_line_file, Some(current_line_file));
    let cited_stmt_plain = user_visible_stmt_or_msg_text(&result.cite_what.to_string());
    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString("cite forall fact".to_string()),
        ),
        ("cite_source".to_string(), cite_source),
        (
            "cited_statement".to_string(),
            JsonValue::JsonString(cited_stmt_plain),
        ),
        (
            "instantiation".to_string(),
            JsonValue::Object(known_forall_instantiation_fields(&result.instantiation)),
        ),
        (
            "requirements".to_string(),
            JsonValue::Array(known_forall_requirement_items(
                runtime,
                &result.requirements,
            )),
        ),
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

fn known_forall_instantiation_fields(
    instantiation: &[KnownForallInstantiationItem],
) -> Vec<(String, JsonValue)> {
    instantiation
        .iter()
        .map(|item| {
            (
                item.param.clone(),
                JsonValue::JsonString(user_visible_stmt_or_msg_text(&item.arg)),
            )
        })
        .collect::<Vec<_>>()
}

fn known_forall_requirement_items(
    runtime: &Runtime,
    requirements: &[KnownForallRequirementResult],
) -> Vec<JsonValue> {
    requirements
        .iter()
        .map(|requirement| {
            JsonValue::Object(vec![
                (
                    JSON_KEY_STMT.to_string(),
                    JsonValue::JsonString(user_visible_stmt_or_msg_text(
                        &requirement.stmt.to_string(),
                    )),
                ),
                (
                    JSON_KEY_VERIFICATION.to_string(),
                    stmt_result_to_composite_step_verified_by(runtime, requirement.result.as_ref()),
                ),
            ])
        })
        .collect::<Vec<_>>()
}

fn citation_type_for_stmt(stmt: &Stmt) -> String {
    match stmt {
        Stmt::Fact(fact) => format!("cite {}", citation_fact_type_label(fact)),
        Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(_)) => "cite prop def".to_string(),
        Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(_)) => {
            "cite abstract prop def".to_string()
        }
        Stmt::UnsafeStmt(UnsafeStmt::DefLetStmt(_)) => "cite let def".to_string(),
        Stmt::DefAlgoStmt(_) => "cite algo def".to_string(),
        Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(_)) => "cite struct def".to_string(),
        _ => format!("cite {} statement", stmt_type_label_for_citation(stmt)),
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
        ("cited_statement".to_string(), cited_stmt),
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

impl VerifiedBysEnum {
    fn verify_what(&self) -> &Fact {
        match self {
            VerifiedBysEnum::ByBuiltinRule(r) => &r.verify_what,
            VerifiedBysEnum::ByFact(r) => &r.verify_what,
            VerifiedBysEnum::ByKnownForall(r) => &r.verify_what,
        }
    }
}

fn builtin_rule_public_text(rule: &str) -> String {
    match rule {
        "they are the same" => "same expression on both sides".to_string(),
        "known-only equality: they are the same" => {
            "same expression on both sides from the known/builtin-only checker".to_string()
        }
        "known-only equality: same known equality class" => "same known equality class".to_string(),
        "known-only equality: resolved objects match" => {
            "same value after resolving known values".to_string()
        }
        "or: complementary atomic facts (make_reversed first equals second)" => {
            "complementary facts cover all cases".to_string()
        }
        "calculation and rational expression simplification" => {
            "exact calculation and rational expression simplification".to_string()
        }
        "mul_opposite_signs_product_in_R_neg" => {
            "product of opposite-sign factors is in R_neg".to_string()
        }
        "mul_opposite_signs_product_in_Q_neg" => {
            "product of opposite-sign factors is in Q_neg".to_string()
        }
        "mul_opposite_signs_product_in_Z_neg" => {
            "product of opposite-sign factors is in Z_neg".to_string()
        }
        _ => humanize_builtin_rule_label(rule),
    }
}

fn humanize_builtin_rule_label(rule: &str) -> String {
    if !looks_like_internal_rule_id(rule) {
        return rule.to_string();
    }

    let mut text = rule.replace('_', " ");
    for (plain, original) in [
        ("N pos", "N_pos"),
        ("Q pos", "Q_pos"),
        ("R pos", "R_pos"),
        ("Z neg", "Z_neg"),
        ("Q neg", "Q_neg"),
        ("R neg", "R_neg"),
        ("Z nz", "Z_nz"),
        ("Q nz", "Q_nz"),
        ("R nz", "R_nz"),
    ] {
        text = text.replace(plain, original);
    }
    text = text.replace("fn ", "function ");
    text = text.replace(" ret ", " return ");
    text
}

fn looks_like_internal_rule_id(rule: &str) -> bool {
    rule.contains('_')
        && rule.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !rule.chars().any(char::is_whitespace)
}
