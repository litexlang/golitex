//! Actual inference outputs, linked to their seed and retained proof evidence.
//! This is an export index; it neither derives nor publishes kernel facts.
use super::*;

impl Capture {
    pub fn record_inference(&mut self, result: &StoreFactAndInferResult, output: &JsonValue) {
        if self.capturing_ast {
            return;
        }
        let Some(infer) = &result.infer else { return };
        let conclusions = infer.stored_fact_ids();
        if conclusions.is_empty() {
            return;
        }
        let evidence = output
            .as_object()
            .ok()
            .and_then(|fields| fields.get("fields"))
            .and_then(|fields| fields.as_object().ok())
            .and_then(|fields| fields.get("infer"))
            .cloned()
            .expect("typed store-and-infer projection includes infer");
        let source = result.primary_fact_id().to_string();
        let scope = self
            .facts
            .get(&source)
            .map(|fact| field_text(fact, "scope_id"))
            .filter(|scope| !scope.is_empty())
            .unwrap_or_else(|| self.current_scope.clone());
        let id = format!("inference{}", self.inferences.len());
        let facts = conclusions
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        let mut rules = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut pending = vec![&evidence];
        while let Some(value) = pending.pop() {
            match value {
                JsonValue::Array(values) => pending.extend(values),
                JsonValue::Object(fields) => {
                    if let Some(JsonValue::String(rule)) = fields.get("rule_id") {
                        if self
                            .rules
                            .get(rule)
                            .is_some_and(|rule| field_text(rule, "category") == "infer")
                        {
                            rules.insert(rule.clone());
                        }
                    }
                    if let Some(JsonValue::String(reference)) = fields.get("evidence_id") {
                        if seen.insert(reference.clone()) {
                            if let Some(node) = reference
                                .strip_prefix("evidence")
                                .and_then(|index| index.parse::<usize>().ok())
                                .and_then(|index| self.evidence_nodes.get(index))
                                .and_then(|node| node.as_object().ok())
                                .and_then(|fields| fields.get("node"))
                            {
                                pending.push(node);
                            }
                        }
                    } else {
                        pending.extend(fields.iter().map(|(_, value)| value));
                    }
                }
                _ => {}
            }
        }
        self.inferences.push(object(vec![
            ("id", text(&id)),
            ("source_fact_id", text(&source)),
            ("fact_ids", strings(&facts)),
            ("producer_statement_id", text(&self.current_statement)),
            ("scope_id", text(&scope)),
            ("rule_ids", strings(&rules.into_iter().collect::<Vec<_>>())),
            ("evidence", evidence),
        ]));
        for fact in facts {
            if let Some(JsonValue::Object(fields)) = self.facts.get_mut(&fact) {
                let mut entries = fields
                    .get("inference_ids")
                    .cloned()
                    .unwrap_or_else(|| JsonValue::Array(Vec::new()));
                if let JsonValue::Array(entries) = &mut entries {
                    entries.push(text(&id));
                }
                fields.insert("inference_ids".into(), entries);
            }
        }
    }

    pub fn annotate_inferred_facts(&mut self) {
        let mut by_statement = BTreeMap::<String, BTreeSet<String>>::new();
        for inference in &self.inferences {
            if let Some(JsonValue::Array(facts)) = inference
                .as_object()
                .ok()
                .and_then(|fields| fields.get("fact_ids"))
            {
                let inferred = by_statement
                    .entry(field_text(inference, "producer_statement_id"))
                    .or_default();
                inferred.extend(
                    facts
                        .iter()
                        .filter_map(|fact| fact.as_str().ok())
                        .map(ToString::to_string),
                );
            }
        }
        for statement in &mut self.statements {
            let id = field_text(statement, "id");
            let inferred = if field_text(statement, "status") == "accepted" {
                by_statement.remove(&id).unwrap_or_default()
            } else {
                BTreeSet::new()
            };
            if let JsonValue::Object(fields) = statement {
                fields.insert(
                    "inferred_fact_ids".into(),
                    strings(&inferred.into_iter().collect::<Vec<_>>()),
                );
            }
        }
    }
}
