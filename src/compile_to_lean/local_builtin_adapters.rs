use crate::verify::rule_schema::{RuleFingerprint, RuleId};
use std::collections::HashSet;

pub(super) struct GeneratedLocalBuiltinAdapterSource {
    pub id: &'static str,
    pub semantic_fingerprint: &'static str,
    pub theorem_name: &'static str,
    pub lean_source: &'static str,
}

include!("local_builtin_adapters/generated_manifest.rs");

pub(super) struct LinkedLocalBuiltinAdapter {
    pub theorem_name: &'static str,
}

pub(super) fn local_builtin_adapter(
    rule_id: &RuleId,
    fingerprint: &RuleFingerprint,
) -> Result<LinkedLocalBuiltinAdapter, String> {
    let source = GENERATED_LOCAL_BUILTIN_ADAPTERS
        .iter()
        .find(|source| source.id == rule_id.as_str())
        .ok_or_else(|| format!("no Lean adapter for local builtin `{}`", rule_id.as_str()))?;
    if source.semantic_fingerprint != fingerprint.as_hex() {
        return Err(format!(
            "Lean adapter fingerprint disagrees with local builtin `{}`",
            rule_id.as_str()
        ));
    }
    Ok(LinkedLocalBuiltinAdapter {
        theorem_name: source.theorem_name,
    })
}

pub(super) fn linked_local_builtin_adapter_module(
    required: &HashSet<RuleId>,
) -> Result<String, String> {
    if required.is_empty() {
        return Ok(String::new());
    }
    let mut sources = GENERATED_LOCAL_BUILTIN_ADAPTERS
        .iter()
        .filter(|source| required.iter().any(|id| id.as_str() == source.id))
        .collect::<Vec<_>>();
    sources.sort_by_key(|source| source.id);
    if sources.len() != required.len() {
        let missing = required
            .iter()
            .filter(|id| !sources.iter().any(|source| source.id == id.as_str()))
            .map(RuleId::as_str)
            .collect::<Vec<_>>();
        return Err(format!("missing Lean adapters for {}", missing.join(", ")));
    }
    let mut lines = vec!["namespace Litex.BuiltinRules".to_string(), String::new()];
    for source in sources {
        lines.push(source.lean_source.trim().to_string());
        lines.push(String::new());
    }
    lines.push("end Litex.BuiltinRules".to_string());
    Ok(lines.join("\n"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_adapters_have_unique_ids_and_theorem_names() {
        let mut ids = HashSet::new();
        let mut names = HashSet::new();
        for adapter in GENERATED_LOCAL_BUILTIN_ADAPTERS {
            assert!(ids.insert(adapter.id));
            assert!(names.insert(adapter.theorem_name));
            assert_eq!(adapter.theorem_name, adapter.id.replace('.', "_"));
        }
    }
}
