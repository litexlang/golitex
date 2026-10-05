//! Shared helpers for Normal JSON projection.

use super::json_keys::localize_key;
use crate::ast::fact::{AtomicFact, ExistShapedFact, Fact};
use crate::ast::line_file::SourceLine;
use crate::knowledge_base::{JsonObject, JsonValue};
use crate::launch_command::OutputLanguage;
use crate::runtime::{FactId, Runtime};
use crate::store_fact_and_infer::{StoreFactAndInferResult, StoreFactResult};

/// Build an object; keys are English in source and remapped by `lang`.
/// Field order follows `entries` (not alphabetical).
pub(super) fn object(lang: OutputLanguage, entries: Vec<(&str, JsonValue)>) -> JsonValue {
    let mut map = JsonObject::new();
    for (key, value) in entries {
        map.insert(localize_key(key, lang), value);
    }
    JsonValue::Object(map)
}

/// Same as `object`, language taken from Runtime (`-lang`).
pub(super) fn object_for(runtime: &Runtime, entries: Vec<(&str, JsonValue)>) -> JsonValue {
    object(output_language(runtime), entries)
}

/// Keep the parsed source identity when projecting a complete code run.
pub(super) fn with_source_statement(
    mut projected: JsonValue,
    statement: Option<&String>,
    lang: OutputLanguage,
) -> JsonValue {
    if let (Some(statement), JsonValue::Object(fields)) = (statement, &mut projected) {
        fields.insert(localize_key("statement", lang), string(statement));
    }
    projected
}

pub(super) fn string(s: impl Into<String>) -> JsonValue {
    JsonValue::String(s.into())
}

pub(super) fn bool_value(b: bool) -> JsonValue {
    JsonValue::Bool(b)
}

pub(super) fn array_of_strings(items: Vec<String>) -> JsonValue {
    JsonValue::Array(items.into_iter().map(string).collect())
}

pub(super) fn empty_string_array() -> JsonValue {
    JsonValue::Array(Vec::new())
}

pub(super) fn fact_display(fact: &Fact) -> String {
    fact.readable_string()
}

pub(super) fn atomic_display(fact: &AtomicFact) -> String {
    fact.readable_string()
}

pub(super) fn fact_line(fact: &Fact) -> Option<usize> {
    fact_source_line(fact).map(|line| line.line)
}

fn fact_source_line(fact: &Fact) -> Option<&SourceLine> {
    match fact {
        Fact::AtomicFact(a) => atomic_source_line(a),
        Fact::AndFact(f) => f.line_file.as_ref(),
        Fact::ChainFact(f) => f.line_file.as_ref(),
        Fact::OrFact(f) => f.line_file.as_ref(),
        Fact::ExistFact(p) | Fact::ExistUniqueFact(p) | Fact::NotExistFact(p) => {
            p.line_file.as_ref()
        }
        Fact::ForallFact(f) => f.line_file.as_ref(),
        Fact::ForallFactWithIff(f) => f.line_file.as_ref(),
        Fact::NotForall(f) => f.line_file.as_ref(),
    }
}

fn atomic_source_line(fact: &AtomicFact) -> Option<&SourceLine> {
    match fact {
        AtomicFact::NormalAtomicFact(f) => f.line_file.as_ref(),
        AtomicFact::NotNormalAtomicFact(f) => f.line_file.as_ref(),
        AtomicFact::EqualFact(f) => f.line_file.as_ref(),
        AtomicFact::NotEqualFact(f) => f.line_file.as_ref(),
        AtomicFact::LessFact(f) => f.line_file.as_ref(),
        AtomicFact::GreaterFact(f) => f.line_file.as_ref(),
        AtomicFact::LessEqualFact(f) => f.line_file.as_ref(),
        AtomicFact::GreaterEqualFact(f) => f.line_file.as_ref(),
        AtomicFact::IsSetFact(f) => f.line_file.as_ref(),
        AtomicFact::IsNonemptySetFact(f) => f.line_file.as_ref(),
        AtomicFact::IsFiniteSetFact(f) => f.line_file.as_ref(),
        AtomicFact::InFact(f) => f.line_file.as_ref(),
        AtomicFact::IsCartFact(f) => f.line_file.as_ref(),
        AtomicFact::IsTupleFact(f) => f.line_file.as_ref(),
        AtomicFact::SubsetFact(f) => f.line_file.as_ref(),
        AtomicFact::SupersetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotLessFact(f) => f.line_file.as_ref(),
        AtomicFact::NotGreaterFact(f) => f.line_file.as_ref(),
        AtomicFact::NotLessEqualFact(f) => f.line_file.as_ref(),
        AtomicFact::NotGreaterEqualFact(f) => f.line_file.as_ref(),
        AtomicFact::NotIsSetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotIsNonemptySetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotIsFiniteSetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotInFact(f) => f.line_file.as_ref(),
        AtomicFact::NotIsCartFact(f) => f.line_file.as_ref(),
        AtomicFact::NotIsTupleFact(f) => f.line_file.as_ref(),
        AtomicFact::NotSubsetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotSupersetFact(f) => f.line_file.as_ref(),
        AtomicFact::ProperSubsetFact(f) => f.line_file.as_ref(),
        AtomicFact::ProperSupersetFact(f) => f.line_file.as_ref(),
        AtomicFact::PrimeFact(f) => f.line_file.as_ref(),
        AtomicFact::CoprimeFact(f) => f.line_file.as_ref(),
        AtomicFact::DvdFact(f) => f.line_file.as_ref(),
        AtomicFact::InjectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::SurjectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::BijectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::IsChoiceFunctionForFact(f) => f.line_file.as_ref(),
        AtomicFact::NotProperSubsetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotProperSupersetFact(f) => f.line_file.as_ref(),
        AtomicFact::NotPrimeFact(f) => f.line_file.as_ref(),
        AtomicFact::NotCoprimeFact(f) => f.line_file.as_ref(),
        AtomicFact::NotDvdFact(f) => f.line_file.as_ref(),
        AtomicFact::NotInjectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::NotSurjectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::NotBijectiveFact(f) => f.line_file.as_ref(),
        AtomicFact::NotIsChoiceFunctionForFact(f) => f.line_file.as_ref(),
    }
}

pub(super) fn cite_from_fact_id(runtime: &Runtime, fact_id: FactId) -> JsonValue {
    let lang = output_language(runtime);
    let type_tag = type_value_cite_known(lang);
    let Some(fact) = runtime.fact_by_id_in_stack(fact_id) else {
        return object(lang, vec![("type", string(type_tag))]);
    };
    let mut entries = vec![
        ("type", string(type_tag)),
        ("cite", string(fact_display(fact))),
    ];
    if let Some(line) = fact_line(fact) {
        entries.insert(1, ("line", JsonValue::Number(line as f64)));
    }
    object(lang, entries)
}

pub(super) fn cite_forall_from_fact_id(runtime: &Runtime, fact_id: FactId) -> JsonValue {
    let lang = output_language(runtime);
    let type_tag = type_value_cite_forall(lang);
    let Some(fact) = runtime.fact_by_id_in_stack(fact_id) else {
        return object(lang, vec![("type", string(type_tag))]);
    };
    let mut entries = vec![
        ("type", string(type_tag)),
        ("cite", string(fact_display(fact))),
    ];
    if let Some(line) = fact_line(fact) {
        entries.insert(1, ("line", JsonValue::Number(line as f64)));
    }
    object(lang, entries)
}

pub(super) fn builtin_rule_with_optional_cite(
    runtime: &Runtime,
    text: &crate::json_output::explain::BuiltinRuleText,
    cite_fact_id: Option<FactId>,
) -> JsonValue {
    let lang = output_language(runtime);
    // The localized payload contains only the displayed rule name and message.
    let mut entries = vec![
        ("type", string(type_value_builtin_rule(lang))),
        ("rule_name", string(text.rule_name.clone())),
        ("message", string(text.message.clone())),
    ];
    if let Some(fact_id) = cite_fact_id {
        if let Some(fact) = runtime.fact_by_id_in_stack(fact_id) {
            if let Some(line) = fact_line(fact) {
                entries.push(("line", JsonValue::Number(line as f64)));
            }
            entries.push(("cite", string(fact_display(fact))));
        }
    }
    object(lang, entries)
}

pub(super) fn output_language(runtime: &Runtime) -> OutputLanguage {
    runtime.launch_command.output_language()
}

pub(super) fn store_fact_texts(store: &StoreFactResult) -> Vec<String> {
    match store {
        StoreFactResult::AtomicFact(r) => vec![atomic_display(&r.fact)],
        StoreFactResult::AndFact(r) => {
            let mut out = vec![fact_display(&Fact::AndFact(r.fact.clone()))];
            for c in &r.components {
                out.push(atomic_display(&c.fact));
            }
            out
        }
        StoreFactResult::ChainFact(r) => {
            let mut out = vec![fact_display(&Fact::ChainFact(r.fact.clone()))];
            for a in &r.adjacent {
                out.push(atomic_display(&a.fact));
            }
            out
        }
        StoreFactResult::OrFact(r) => vec![fact_display(&Fact::OrFact(r.fact.clone()))],
        StoreFactResult::ExistShapedFact(r) => match &r.fact {
            ExistShapedFact::Exist(p) => vec![fact_display(&Fact::ExistFact(p.clone()))],
            ExistShapedFact::ExistUnique(p) => {
                vec![fact_display(&Fact::ExistUniqueFact(p.clone()))]
            }
            ExistShapedFact::NotExist(p) => vec![fact_display(&Fact::NotExistFact(p.clone()))],
        },
        StoreFactResult::NotForallFact(r) => {
            vec![fact_display(&Fact::NotForall(r.fact.clone()))]
        }
        StoreFactResult::ForallFact(r) => vec![fact_display(&Fact::ForallFact(r.fact.clone()))],
        StoreFactResult::ForallFactWithIff(r) => {
            vec![fact_display(&Fact::ForallFactWithIff(r.fact.clone()))]
        }
    }
}

// Infer texts via FactId lookup (avoids matching every Infer* variant type).
pub(super) fn infer_fact_texts_from_store_and_infer(
    runtime: &Runtime,
    node: &StoreFactAndInferResult,
) -> Vec<String> {
    let store_ids = node.store.stored_fact_ids();
    let all_ids = node.stored_fact_ids();
    let mut out = Vec::new();
    for fact_id in all_ids {
        if store_ids.contains(&fact_id) {
            continue;
        }
        if let Some(fact) = runtime.fact_by_id_in_stack(fact_id) {
            out.push(fact_display(fact));
        }
    }
    out
}

pub(super) fn split_have_fact_id_texts(
    runtime: &Runtime,
    fact_ids: &[FactId],
) -> (Vec<String>, Vec<String>) {
    let mut stores = Vec::new();
    let mut infers = Vec::new();
    for (i, fact_id) in fact_ids.iter().enumerate() {
        let Some(fact) = runtime.fact_by_id_in_stack(*fact_id) else {
            continue;
        };
        let text = fact_display(fact);
        if i == 0 {
            stores.push(text);
        } else {
            infers.push(text);
        }
    }
    (stores, infers)
}

pub(super) fn type_value_cite_known(lang: OutputLanguage) -> &'static str {
    match lang {
        OutputLanguage::English => "cite_known",
        OutputLanguage::ChineseTraditional => "引用已知命題",
        OutputLanguage::French => "Citation d'une proposition connue",
        OutputLanguage::Russian => "Ссылка на известное утверждение",
        OutputLanguage::Spanish => "Cita de proposición conocida",
        OutputLanguage::Arabic => "استشهاد بقضية معلومة",
        OutputLanguage::Japanese => "既知の命題の引用",
        OutputLanguage::Korean => "알려진 명제 인용",
        OutputLanguage::Vietnamese => "Trích dẫn mệnh đề đã biết",

        OutputLanguage::Chinese => "引用已知",
    }
}

pub(super) fn type_value_cite_forall(lang: OutputLanguage) -> &'static str {
    match lang {
        OutputLanguage::English => "cite_forall",
        OutputLanguage::ChineseTraditional => "引用全稱命題",
        OutputLanguage::French => "Citation d'une proposition universelle",
        OutputLanguage::Russian => "Ссылка на всеобщее утверждение",
        OutputLanguage::Spanish => "Cita de proposición universal",
        OutputLanguage::Arabic => "استشهاد بقضية كلية",
        OutputLanguage::Japanese => "全称命題の引用",
        OutputLanguage::Korean => "전칭 명제 인용",
        OutputLanguage::Vietnamese => "Trích dẫn mệnh đề phổ quát",

        OutputLanguage::Chinese => "引用全称",
    }
}

pub(super) fn type_value_builtin_rule(lang: OutputLanguage) -> &'static str {
    match lang {
        OutputLanguage::English => "builtin_rule",
        OutputLanguage::ChineseTraditional => "內建規則",
        OutputLanguage::French => "Règle intégrée",
        OutputLanguage::Russian => "Встроенное правило",
        OutputLanguage::Spanish => "Regla incorporada",
        OutputLanguage::Arabic => "قاعدة مدمجة",
        OutputLanguage::Japanese => "組み込み規則",
        OutputLanguage::Korean => "내장 규칙",
        OutputLanguage::Vietnamese => "Quy tắc tích hợp",

        OutputLanguage::Chinese => "内置规则",
    }
}

pub(super) fn phase_value_search_proof(lang: OutputLanguage) -> &'static str {
    match lang {
        OutputLanguage::English => "search_proof",
        OutputLanguage::ChineseTraditional => "搜尋證明",
        OutputLanguage::French => "Recherche de preuve",
        OutputLanguage::Russian => "Поиск доказательства",
        OutputLanguage::Spanish => "Búsqueda de prueba",
        OutputLanguage::Arabic => "بحث عن برهان",
        OutputLanguage::Japanese => "証明探索",
        OutputLanguage::Korean => "증명 탐색",
        OutputLanguage::Vietnamese => "Tìm kiếm chứng minh",

        OutputLanguage::Chinese => "搜索证明",
    }
}

pub(super) fn phase_value_well_defined(lang: OutputLanguage) -> &'static str {
    match lang {
        OutputLanguage::English => "well_defined",
        OutputLanguage::ChineseTraditional => "良定性",
        OutputLanguage::French => "Bonne définition",
        OutputLanguage::Russian => "Корректность определения",
        OutputLanguage::Spanish => "Buena definición",
        OutputLanguage::Arabic => "حسن التعريف",
        OutputLanguage::Japanese => "定義の適切性",
        OutputLanguage::Korean => "정의의 타당성",
        OutputLanguage::Vietnamese => "Tính xác định tốt",

        OutputLanguage::Chinese => "良定性",
    }
}
