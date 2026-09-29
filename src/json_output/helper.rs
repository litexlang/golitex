//! Shared helpers for Normal JSON projection.

use crate::ast::fact::{AtomicFact, ExistShapedFact, Fact};
use crate::ast::line_file::SourceLine;
use crate::knowledge_base::JsonValue;
use crate::runtime::{FactId, Runtime};
use crate::store_fact_and_infer::{StoreFactAndInferResult, StoreFactResult};
use std::collections::BTreeMap;

pub(super) fn object(entries: Vec<(&str, JsonValue)>) -> JsonValue {
    let mut map = BTreeMap::new();
    for (key, value) in entries {
        map.insert(key.to_string(), value);
    }
    JsonValue::Object(map)
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
    }
}

pub(super) fn cite_from_fact_id(runtime: &Runtime, fact_id: FactId) -> JsonValue {
    let Some(fact) = runtime.fact_by_id_in_stack(fact_id) else {
        return object(vec![("type", string("cite_known"))]);
    };
    let mut entries = vec![
        ("type", string("cite_known")),
        ("cite", string(fact_display(fact))),
    ];
    if let Some(line) = fact_line(fact) {
        entries.insert(1, ("line", JsonValue::Number(line as f64)));
    }
    object(entries)
}

pub(super) fn cite_forall_from_fact_id(runtime: &Runtime, fact_id: FactId) -> JsonValue {
    let Some(fact) = runtime.fact_by_id_in_stack(fact_id) else {
        return object(vec![("type", string("cite_forall"))]);
    };
    let mut entries = vec![
        ("type", string("cite_forall")),
        ("cite", string(fact_display(fact))),
    ];
    if let Some(line) = fact_line(fact) {
        entries.insert(1, ("line", JsonValue::Number(line as f64)));
    }
    object(entries)
}

pub(super) fn builtin_rule_with_optional_cite(
    runtime: &Runtime,
    text: &crate::json_output::explain::BuiltinRuleText,
    cite_fact_id: Option<FactId>,
) -> JsonValue {
    // Print rule_name + message only; rule_id stays internal to explain/.
    let mut entries = vec![
        ("type", string("builtin_rule")),
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
    object(entries)
}

pub(super) fn output_language(runtime: &Runtime) -> crate::launch_command::OutputLanguage {
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
