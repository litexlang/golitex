//! Longest-chain analysis, canonical identities, and Mermaid shapes.

use super::*;

pub(super) fn longest_chain_from(
    node_id: &str,
    outgoing: &HashMap<String, Vec<String>>,
    memo: &mut HashMap<String, Vec<String>>,
    visiting: &mut HashSet<String>,
) -> Vec<String> {
    if let Some(chain) = memo.get(node_id) {
        return chain.clone();
    }
    if !visiting.insert(node_id.to_string()) {
        return vec![];
    }
    let mut best_tail = vec![];
    if let Some(next_nodes) = outgoing.get(node_id) {
        for next in next_nodes {
            let candidate = longest_chain_from(next, outgoing, memo, visiting);
            if candidate.len() > best_tail.len() {
                best_tail = candidate;
            }
        }
    }
    visiting.remove(node_id);
    let mut chain = vec![node_id.to_string()];
    chain.append(&mut best_tail);
    memo.insert(node_id.to_string(), chain.clone());
    chain
}

pub(super) fn fact_kind_from_store_reason(reason: &str) -> &'static str {
    if reason == TrustStmt::store_reason() || reason == TrustHaveStmt::store_reason() {
        "trust"
    } else if reason == ClaimStmt::store_reason() {
        "claim_result"
    } else {
        "fact"
    }
}

pub(super) fn fact_node_id(fact: &Fact) -> String {
    format!("fact:{}:{}", line_key(&fact.line_file()), fact)
}

pub(super) fn theorem_id(name: &str) -> String {
    format!("thm:{}", name)
}

pub(super) fn claim_id(line_file: &LineFile) -> String {
    format!("claim:{}", line_key(line_file))
}

pub(super) fn line_key(line_file: &LineFile) -> String {
    if is_default_line_file(line_file) {
        "unknown".to_string()
    } else {
        format!("{}:{}", line_file.1.as_ref(), line_file.0)
    }
}

pub(super) fn line_label(line_file: &LineFile) -> String {
    if is_default_line_file(line_file) {
        "?".to_string()
    } else {
        line_file.0.to_string()
    }
}

pub(super) fn compact_text(text: &str) -> String {
    let compact = text.split_whitespace().collect::<Vec<_>>().join(" ");
    let visible = compact.chars().take(112).collect::<String>();
    if visible.len() < compact.len() {
        format!("{}…", visible)
    } else {
        visible
    }
}

pub(super) fn canonical_fact_text(fact: &Fact) -> String {
    canonical_fact_text_from_text(&fact.to_string())
}

pub(super) fn canonical_fact_text_from_text(text: &str) -> String {
    strip_free_param_numeric_tags_in_display(text)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

pub(super) fn fact_graph_node_belongs_to_main_chain(node: &FactGraphNode) -> bool {
    node.fact_kind.as_deref() != Some("inferred")
}

pub(super) fn fact_graph_line_json_value(line_file: &LineFile) -> JsonValue {
    if is_default_line_file(line_file) {
        JsonValue::Null
    } else {
        JsonValue::Number(line_file.0)
    }
}

pub(super) fn mermaid_id(id: &str) -> String {
    let mut output = "n_".to_string();
    for character in id.chars() {
        if character.is_ascii_alphanumeric() {
            output.push(character);
        } else {
            output.push('_');
        }
    }
    output
}

pub(super) fn mermaid_node_shape(node: &FactGraphNode) -> String {
    let label = node.label.replace('"', "'");
    match node.fact_kind.as_deref() {
        Some("thm") => format!("[[\"{}\"]]", label),
        Some("claim") => format!("([\"{}\"])", label),
        _ => format!("[/\"{}\"/]", label),
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/graph/fact_graph/tests.rs"]
mod tests;
