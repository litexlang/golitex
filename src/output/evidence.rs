use crate::common::json_value::JsonValue;
use crate::prelude::*;

use super::fields::{
    user_visible_stmt_or_msg_text, JSON_KEY_CONCLUSIONS, JSON_KEY_STEPS, JSON_KEY_STMT,
    JSON_KEY_VERIFICATION,
};
use super::source::{source_ref_json_value, stmt_text_for_json};

fn verified_by_builtin_rule_value(
    runtime: &Runtime,
    rule: &str,
    verify_what: Option<&Fact>,
    subgoals: &[StmtResult],
) -> JsonValue {
    let rule_output_text = builtin_rule_output_text(rule);
    let public_rule = render_builtin_rule_output_text(runtime.output_language, &rule_output_text);
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
    let conclusions = proof
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
        JSON_KEY_CONCLUSIONS.to_string(),
        JsonValue::Array(conclusions),
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
            return Some(ParamDefWithType::store_reason());
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
                JsonValue::JsonString(n.stmt.output_type_string()),
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
    ];
    if runtime.detail_output {
        fields.push((
            "instantiation".to_string(),
            JsonValue::Object(known_forall_instantiation_fields(&result.instantiation)),
        ));
        fields.push((
            "requirements".to_string(),
            JsonValue::Array(known_forall_requirement_items(
                runtime,
                &result.requirements,
            )),
        ));
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
        Stmt::Fact(fact) => format!("cite {}", fact.output_type_string()),
        Stmt::DefPredicateStmt(DefPredicateStmt::DefPropStmt(_)) => "cite prop def".to_string(),
        Stmt::DefPredicateStmt(DefPredicateStmt::DefAbstractPropStmt(_)) => {
            "cite abstract prop def".to_string()
        }
        Stmt::UnsafeStmt(UnsafeStmt::DefLetStmt(_)) => "cite let def".to_string(),
        Stmt::DefAlgoStmt(_) => "cite algo def".to_string(),
        Stmt::DefInterfaceStmt(DefInterfaceStmt::DefStructStmt(_)) => "cite struct def".to_string(),
        _ => format!("cite {}", stmt.output_type_string()),
    }
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

enum BuiltinRuleOutputText {
    Calculation,
    SameExpressionBothSides,
    SameExpressionBothSidesFromKnownBuiltinOnlyChecker,
    SameKnownEqualityClass,
    SameValueAfterResolvingKnownValues,
    ExactCalculationAndRationalExpressionSimplification,
    ComplementaryFactsCoverAllCases,
    OppositeSignProductInRNeg,
    OppositeSignProductInQNeg,
    OppositeSignProductInZNeg,
    Fallback(String),
}

fn builtin_rule_output_text(rule: &str) -> BuiltinRuleOutputText {
    match rule {
        "calculation" => BuiltinRuleOutputText::Calculation,
        "they are the same" => BuiltinRuleOutputText::SameExpressionBothSides,
        "known-only equality: they are the same" => {
            BuiltinRuleOutputText::SameExpressionBothSidesFromKnownBuiltinOnlyChecker
        }
        "known-only equality: same known equality class" => {
            BuiltinRuleOutputText::SameKnownEqualityClass
        }
        "known-only equality: resolved objects match" => {
            BuiltinRuleOutputText::SameValueAfterResolvingKnownValues
        }
        "or: complementary atomic facts (make_reversed first equals second)" => {
            BuiltinRuleOutputText::ComplementaryFactsCoverAllCases
        }
        "calculation and rational expression simplification" => {
            BuiltinRuleOutputText::ExactCalculationAndRationalExpressionSimplification
        }
        "mul_opposite_signs_product_in_R_neg" => BuiltinRuleOutputText::OppositeSignProductInRNeg,
        "mul_opposite_signs_product_in_Q_neg" => BuiltinRuleOutputText::OppositeSignProductInQNeg,
        "mul_opposite_signs_product_in_Z_neg" => BuiltinRuleOutputText::OppositeSignProductInZNeg,
        _ => BuiltinRuleOutputText::Fallback(humanize_builtin_rule_label(rule)),
    }
}

fn render_builtin_rule_output_text(
    output_language: OutputLanguage,
    text: &BuiltinRuleOutputText,
) -> String {
    match text {
        BuiltinRuleOutputText::Calculation => match output_language {
            OutputLanguage::English => "calculation",
            OutputLanguage::SimplifiedChinese => "计算",
            OutputLanguage::TraditionalChinese => "計算",
            OutputLanguage::Japanese => "計算",
            OutputLanguage::Korean => "계산",
            OutputLanguage::Spanish => "cálculo",
            OutputLanguage::French => "calcul",
            OutputLanguage::German => "Rechnung",
            OutputLanguage::Portuguese => "cálculo",
            OutputLanguage::Russian => "вычисление",
            OutputLanguage::Arabic => "حساب",
            OutputLanguage::Hindi => "गणना",
            OutputLanguage::Vietnamese => "tính toán",
            OutputLanguage::Indonesian => "perhitungan",
        }
        .to_string(),
        BuiltinRuleOutputText::SameExpressionBothSides => match output_language {
            OutputLanguage::English => "same expression on both sides",
            OutputLanguage::SimplifiedChinese => "两边是同一个表达式",
            OutputLanguage::TraditionalChinese => "兩邊是同一個表達式",
            OutputLanguage::Japanese => "両辺が同じ式",
            OutputLanguage::Korean => "양변이 같은 식",
            OutputLanguage::Spanish => "la misma expresión en ambos lados",
            OutputLanguage::French => "même expression des deux côtés",
            OutputLanguage::German => "gleicher Ausdruck auf beiden Seiten",
            OutputLanguage::Portuguese => "mesma expressão nos dois lados",
            OutputLanguage::Russian => "одинаковое выражение с обеих сторон",
            OutputLanguage::Arabic => "نفس التعبير على الجانبين",
            OutputLanguage::Hindi => "दोनों ओर समान expression",
            OutputLanguage::Vietnamese => "cùng biểu thức ở hai vế",
            OutputLanguage::Indonesian => "ekspresi yang sama di kedua sisi",
        }
        .to_string(),
        BuiltinRuleOutputText::SameExpressionBothSidesFromKnownBuiltinOnlyChecker => {
            match output_language {
                OutputLanguage::English => {
                    "same expression on both sides from the known/builtin-only checker"
                }
                OutputLanguage::SimplifiedChinese => {
                    "由仅使用已知事实和内置规则的检查器确认两边是同一个表达式"
                }
                OutputLanguage::TraditionalChinese => {
                    "由僅使用已知事實和內建規則的檢查器確認兩邊是同一個表達式"
                }
                OutputLanguage::Japanese => {
                    "既知事実と組み込みルールのみのチェッカーにより両辺が同じ式"
                }
                OutputLanguage::Korean => "알려진 사실과 내장 규칙만 사용하는 검사기에서 양변이 같은 식",
                OutputLanguage::Spanish => {
                    "la misma expresión en ambos lados según el verificador solo con hechos conocidos y reglas integradas"
                }
                OutputLanguage::French => {
                    "même expression des deux côtés selon le vérificateur limité aux faits connus et règles intégrées"
                }
                OutputLanguage::German => {
                    "gleicher Ausdruck auf beiden Seiten nach dem Prüfer nur mit bekannten Fakten und eingebauten Regeln"
                }
                OutputLanguage::Portuguese => {
                    "mesma expressão nos dois lados pelo verificador apenas com fatos conhecidos e regras internas"
                }
                OutputLanguage::Russian => {
                    "одинаковое выражение с обеих сторон по проверке только известными фактами и встроенными правилами"
                }
                OutputLanguage::Arabic => {
                    "نفس التعبير على الجانبين حسب الفاحص المعتمد فقط على الحقائق المعروفة والقواعد المضمنة"
                }
                OutputLanguage::Hindi => {
                    "ज्ञात तथ्यों और आंतरिक नियमों तक सीमित checker से दोनों ओर समान expression"
                }
                OutputLanguage::Vietnamese => {
                    "cùng biểu thức ở hai vế theo bộ kiểm tra chỉ dùng sự kiện đã biết và quy tắc tích hợp"
                }
                OutputLanguage::Indonesian => {
                    "ekspresi yang sama di kedua sisi menurut pemeriksa yang hanya memakai fakta diketahui dan aturan bawaan"
                }
            }
            .to_string()
        }
        BuiltinRuleOutputText::SameKnownEqualityClass => match output_language {
            OutputLanguage::English => "same known equality class",
            OutputLanguage::SimplifiedChinese => "属于同一个已知等价类",
            OutputLanguage::TraditionalChinese => "屬於同一個已知等價類",
            OutputLanguage::Japanese => "同じ既知の等価類",
            OutputLanguage::Korean => "같은 알려진 동치류",
            OutputLanguage::Spanish => "la misma clase de igualdad conocida",
            OutputLanguage::French => "même classe d'égalité connue",
            OutputLanguage::German => "gleiche bekannte Gleichheitsklasse",
            OutputLanguage::Portuguese => "mesma classe de igualdade conhecida",
            OutputLanguage::Russian => "тот же известный класс равенства",
            OutputLanguage::Arabic => "نفس صنف المساواة المعروف",
            OutputLanguage::Hindi => "समान ज्ञात equality class",
            OutputLanguage::Vietnamese => "cùng lớp đẳng thức đã biết",
            OutputLanguage::Indonesian => "kelas kesamaan yang sama diketahui",
        }
        .to_string(),
        BuiltinRuleOutputText::SameValueAfterResolvingKnownValues => match output_language {
            OutputLanguage::English => "same value after resolving known values",
            OutputLanguage::SimplifiedChinese => "解析已知值后相同",
            OutputLanguage::TraditionalChinese => "解析已知值後相同",
            OutputLanguage::Japanese => "既知値を解決すると同じ値",
            OutputLanguage::Korean => "알려진 값을 해소한 뒤 같은 값",
            OutputLanguage::Spanish => "mismo valor tras resolver valores conocidos",
            OutputLanguage::French => "même valeur après résolution des valeurs connues",
            OutputLanguage::German => "gleicher Wert nach Auflösung bekannter Werte",
            OutputLanguage::Portuguese => "mesmo valor após resolver valores conhecidos",
            OutputLanguage::Russian => "то же значение после раскрытия известных значений",
            OutputLanguage::Arabic => "نفس القيمة بعد حل القيم المعروفة",
            OutputLanguage::Hindi => "ज्ञात मान हल करने के बाद समान मान",
            OutputLanguage::Vietnamese => "cùng giá trị sau khi giải các giá trị đã biết",
            OutputLanguage::Indonesian => "nilai yang sama setelah nilai diketahui diselesaikan",
        }
        .to_string(),
        BuiltinRuleOutputText::ExactCalculationAndRationalExpressionSimplification => {
            match output_language {
                OutputLanguage::English => {
                    "exact calculation and rational expression simplification"
                }
                OutputLanguage::SimplifiedChinese => "精确计算和有理表达式化简",
                OutputLanguage::TraditionalChinese => "精確計算和有理表達式化簡",
                OutputLanguage::Japanese => "厳密計算と有理式簡約",
                OutputLanguage::Korean => "정확한 계산과 유리식 단순화",
                OutputLanguage::Spanish => "cálculo exacto y simplificación racional",
                OutputLanguage::French => "calcul exact et simplification rationnelle",
                OutputLanguage::German => "exakte Rechnung und rationale Vereinfachung",
                OutputLanguage::Portuguese => "cálculo exato e simplificação racional",
                OutputLanguage::Russian => "точное вычисление и упрощение рационального выражения",
                OutputLanguage::Arabic => "حساب دقيق وتبسيط تعبير كسري",
                OutputLanguage::Hindi => "सटीक गणना और rational expression सरलीकरण",
                OutputLanguage::Vietnamese => "tính toán chính xác và rút gọn biểu thức hữu tỉ",
                OutputLanguage::Indonesian => "perhitungan eksak dan penyederhanaan ekspresi rasional",
            }
            .to_string()
        }
        BuiltinRuleOutputText::ComplementaryFactsCoverAllCases => match output_language {
            OutputLanguage::English => "complementary facts cover all cases",
            OutputLanguage::SimplifiedChinese => "互补事实覆盖所有情况",
            OutputLanguage::TraditionalChinese => "互補事實覆蓋所有情況",
            OutputLanguage::Japanese => "相補的な事実が全場合を覆う",
            OutputLanguage::Korean => "상보적인 사실이 모든 경우를 덮음",
            OutputLanguage::Spanish => "los hechos complementarios cubren todos los casos",
            OutputLanguage::French => "les faits complémentaires couvrent tous les cas",
            OutputLanguage::German => "komplementäre Fakten decken alle Fälle ab",
            OutputLanguage::Portuguese => "fatos complementares cobrem todos os casos",
            OutputLanguage::Russian => "дополнительные факты покрывают все случаи",
            OutputLanguage::Arabic => "الحقائق المكملة تغطي كل الحالات",
            OutputLanguage::Hindi => "पूरक तथ्य सभी मामलों को ढकते हैं",
            OutputLanguage::Vietnamese => "các sự kiện bổ sung bao phủ mọi trường hợp",
            OutputLanguage::Indonesian => "fakta pelengkap mencakup semua kasus",
        }
        .to_string(),
        BuiltinRuleOutputText::OppositeSignProductInRNeg => match output_language {
            OutputLanguage::English => "product of opposite-sign factors is in R_neg",
            OutputLanguage::SimplifiedChinese => "异号因子的乘积属于 R_neg",
            OutputLanguage::TraditionalChinese => "異號因子的乘積屬於 R_neg",
            OutputLanguage::Japanese => "異符号の因子の積は R_neg に属する",
            OutputLanguage::Korean => "부호가 반대인 인수들의 곱은 R_neg에 속함",
            OutputLanguage::Spanish => "el producto de factores de signo opuesto está en R_neg",
            OutputLanguage::French => "le produit de facteurs de signes opposés est dans R_neg",
            OutputLanguage::German => "Produkt von Faktoren mit entgegengesetztem Vorzeichen liegt in R_neg",
            OutputLanguage::Portuguese => "o produto de fatores com sinais opostos está em R_neg",
            OutputLanguage::Russian => "произведение множителей с противоположными знаками находится в R_neg",
            OutputLanguage::Arabic => "حاصل ضرب عوامل بإشارات متعاكسة ينتمي إلى R_neg",
            OutputLanguage::Hindi => "विपरीत चिह्न वाले गुणकों का गुणनफल R_neg में है",
            OutputLanguage::Vietnamese => "tích của các thừa số trái dấu thuộc R_neg",
            OutputLanguage::Indonesian => "hasil kali faktor bertanda berlawanan berada di R_neg",
        }
        .to_string(),
        BuiltinRuleOutputText::OppositeSignProductInQNeg => match output_language {
            OutputLanguage::English => "product of opposite-sign factors is in Q_neg",
            OutputLanguage::SimplifiedChinese => "异号因子的乘积属于 Q_neg",
            OutputLanguage::TraditionalChinese => "異號因子的乘積屬於 Q_neg",
            OutputLanguage::Japanese => "異符号の因子の積は Q_neg に属する",
            OutputLanguage::Korean => "부호가 반대인 인수들의 곱은 Q_neg에 속함",
            OutputLanguage::Spanish => "el producto de factores de signo opuesto está en Q_neg",
            OutputLanguage::French => "le produit de facteurs de signes opposés est dans Q_neg",
            OutputLanguage::German => "Produkt von Faktoren mit entgegengesetztem Vorzeichen liegt in Q_neg",
            OutputLanguage::Portuguese => "o produto de fatores com sinais opostos está em Q_neg",
            OutputLanguage::Russian => "произведение множителей с противоположными знаками находится в Q_neg",
            OutputLanguage::Arabic => "حاصل ضرب عوامل بإشارات متعاكسة ينتمي إلى Q_neg",
            OutputLanguage::Hindi => "विपरीत चिह्न वाले गुणकों का गुणनफल Q_neg में है",
            OutputLanguage::Vietnamese => "tích của các thừa số trái dấu thuộc Q_neg",
            OutputLanguage::Indonesian => "hasil kali faktor bertanda berlawanan berada di Q_neg",
        }
        .to_string(),
        BuiltinRuleOutputText::OppositeSignProductInZNeg => match output_language {
            OutputLanguage::English => "product of opposite-sign factors is in Z_neg",
            OutputLanguage::SimplifiedChinese => "异号因子的乘积属于 Z_neg",
            OutputLanguage::TraditionalChinese => "異號因子的乘積屬於 Z_neg",
            OutputLanguage::Japanese => "異符号の因子の積は Z_neg に属する",
            OutputLanguage::Korean => "부호가 반대인 인수들의 곱은 Z_neg에 속함",
            OutputLanguage::Spanish => "el producto de factores de signo opuesto está en Z_neg",
            OutputLanguage::French => "le produit de facteurs de signes opposés est dans Z_neg",
            OutputLanguage::German => "Produkt von Faktoren mit entgegengesetztem Vorzeichen liegt in Z_neg",
            OutputLanguage::Portuguese => "o produto de fatores com sinais opostos está em Z_neg",
            OutputLanguage::Russian => "произведение множителей с противоположными знаками находится в Z_neg",
            OutputLanguage::Arabic => "حاصل ضرب عوامل بإشارات متعاكسة ينتمي إلى Z_neg",
            OutputLanguage::Hindi => "विपरीत चिह्न वाले गुणकों का गुणनफल Z_neg में है",
            OutputLanguage::Vietnamese => "tích của các thừa số trái dấu thuộc Z_neg",
            OutputLanguage::Indonesian => "hasil kali faktor bertanda berlawanan berada di Z_neg",
        }
        .to_string(),
        BuiltinRuleOutputText::Fallback(text) => text.clone(),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn non_english_builtin_rule_calculation_values_render() {
        let cases = vec![
            (OutputLanguage::English, "calculation"),
            (OutputLanguage::SimplifiedChinese, "计算"),
            (OutputLanguage::TraditionalChinese, "計算"),
            (OutputLanguage::Japanese, "計算"),
            (OutputLanguage::Korean, "계산"),
            (OutputLanguage::Spanish, "cálculo"),
            (OutputLanguage::French, "calcul"),
            (OutputLanguage::German, "Rechnung"),
            (OutputLanguage::Portuguese, "cálculo"),
            (OutputLanguage::Russian, "вычисление"),
            (OutputLanguage::Arabic, "حساب"),
            (OutputLanguage::Hindi, "गणना"),
            (OutputLanguage::Vietnamese, "tính toán"),
            (OutputLanguage::Indonesian, "perhitungan"),
        ];

        for (language, expected) in cases {
            let rendered =
                render_builtin_rule_output_text(language, &BuiltinRuleOutputText::Calculation);

            assert_eq!(rendered, expected);
            assert!(!rendered.is_empty());
        }
    }
}
