use super::{text, Capture, Fact, JsonValue, Runtime};
use crate::compile_to_latex::fact_to_display_latex;

impl Capture {
    /// Retain the formula on the exact fact, including a chain's adjacent
    /// relations, which need not have entries in the stored-fact table.
    pub(in crate::reading) fn calculus_formula(
        &mut self,
        node: &mut JsonValue,
        runtime: &Runtime,
        fact: impl FnOnce() -> Fact,
    ) {
        if self.capturing_ast
            || !contains_calculus(node, &self.evidence_nodes, &mut self.calculus_descendants)
        {
            return;
        }
        let Ok(latex) =
            fact_to_display_latex(&fact(), &runtime.global_module_manager, self.language)
        else {
            return;
        };
        if let JsonValue::Object(fields) = node {
            fields.insert("calculus_latex".into(), text(&latex));
        }
    }
}

fn contains_calculus(node: &JsonValue, evidence: &[JsonValue], memo: &mut [Option<bool>]) -> bool {
    match node {
        JsonValue::Array(values) => values
            .iter()
            .any(|node| contains_calculus(node, evidence, memo)),
        JsonValue::Object(fields) => {
            if let Some(JsonValue::String(id)) = fields.get("evidence_id") {
                let Some(index) = id
                    .strip_prefix("evidence")
                    .and_then(|index| index.parse::<usize>().ok())
                    .filter(|index| *index < evidence.len())
                else {
                    return false;
                };
                // Interning adds parents after children, so these references
                // point backwards and the dependency graph is acyclic.
                if let Some(contains) = memo[index] {
                    return contains;
                }
                let contains = evidence[index]
                    .as_object()
                    .ok()
                    .and_then(|entry| entry.get("node"))
                    .is_some_and(|node| contains_calculus(node, evidence, memo));
                memo[index] = Some(contains);
                return contains;
            }
            matches!(
                fields.get("type"),
                Some(JsonValue::String(kind)) if matches!(kind.as_str(),
                    "DerivativeAt" | "RiemannIntegral" | "ImproperIntegral"
                        | "HasDerivativeAtFact" | "HasRiemannIntegralFact"
                )
            ) || fields
                .get("fields")
                .and_then(|fields| fields.as_object().ok())
                .is_some_and(|children| {
                    children
                        .iter()
                        .any(|(_, child)| contains_calculus(child, evidence, memo))
                })
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn improper_integrals_retain_the_calculus_formula() {
        let mut fields = crate::knowledge_base::JsonObject::new();
        fields.insert("type".into(), text("ImproperIntegral"));
        let node = JsonValue::Object(fields);
        assert!(contains_calculus(&node, &[], &mut []));
    }
}
