//! Actual inference outputs, linked to their seed and retained proof evidence.
//! This is an export index; it neither derives nor publishes kernel facts.
use super::*;

impl Capture {
    pub fn record_inference(
        &mut self,
        result: &StoreFactAndInferResult,
        output: &JsonValue,
        runtime: &Runtime,
    ) {
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
        // An exact normal-atomic seed identifies the named definition. A
        // compound seed may involve several predicates; do not guess its owner.
        let source_symbol = match &result.store {
            StoreFactResult::AtomicFact(stored) => match &stored.fact {
                AtomicFact::NormalAtomicFact(normal) => {
                    let reference = self.atomic_name(&normal.predicate, runtime);
                    field_text(&reference, "symbol_id")
                }
                _ => String::new(),
            },
            _ => String::new(),
        };
        let definition = self
            .symbols
            .get(&source_symbol)
            .map(|symbol| field_text(symbol, "definition_statement_id"))
            .unwrap_or_default();
        let mut rules = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut origins = Vec::new();
        let mut origin_keys = BTreeSet::new();
        let mut pending = vec![(&evidence, String::new())];
        while let Some((value, inherited_rule)) = pending.pop() {
            match value {
                JsonValue::Array(values) => {
                    pending.extend(values.iter().map(|value| (value, inherited_rule.clone())))
                }
                JsonValue::Object(fields) => {
                    let mut current_rule = inherited_rule;
                    if let Some(JsonValue::String(rule)) = fields.get("rule_id") {
                        if self
                            .rules
                            .get(rule)
                            .is_some_and(|rule| field_text(rule, "category") == "infer")
                        {
                            rules.insert(rule.clone());
                            current_rule = rule.clone();
                        }
                    }
                    if field_text(value, "type") == "StoreInferredFactResult" {
                        let descriptor = self.rules.get(&current_rule);
                        let family = descriptor
                            .map(|rule| field_text(rule, "family"))
                            .unwrap_or_default();
                        let variant = descriptor
                            .map(|rule| field_text(rule, "variant"))
                            .unwrap_or_default();
                        let kind = match (family.as_str(), variant.as_str()) {
                            ("InferNormalAtomicFactResult", "ParamTypes") => "parameter_type",
                            (_, "ExpandDefinition" | "Definition") => "definition",
                            _ if current_rule.is_empty() => "unavailable",
                            _ => "rule",
                        };
                        let named =
                            family == "InferNormalAtomicFactResult" && !source_symbol.is_empty();
                        if let Some(JsonValue::Array(stored)) = fields.get("stored_fact_ids") {
                            for fact in stored.iter().filter_map(|id| id.as_str().ok()) {
                                if facts.iter().any(|id| id == fact)
                                    && origin_keys.insert((fact.to_string(), current_rule.clone()))
                                {
                                    origins.push(object(vec![
                                        ("fact_id", text(fact)),
                                        ("kind", text(kind)),
                                        (
                                            "rule_id",
                                            if current_rule.is_empty() {
                                                JsonValue::Null
                                            } else {
                                                text(&current_rule)
                                            },
                                        ),
                                        (
                                            "source_symbol_id",
                                            if named {
                                                text(&source_symbol)
                                            } else {
                                                JsonValue::Null
                                            },
                                        ),
                                        (
                                            "definition_statement_id",
                                            if named && !definition.is_empty() {
                                                text(&definition)
                                            } else {
                                                JsonValue::Null
                                            },
                                        ),
                                    ]));
                                }
                            }
                        }
                        continue;
                    }
                    if let Some(JsonValue::String(reference)) = fields.get("evidence_id") {
                        if seen.insert((reference.clone(), current_rule.clone())) {
                            if let Some(node) = reference
                                .strip_prefix("evidence")
                                .and_then(|index| index.parse::<usize>().ok())
                                .and_then(|index| self.evidence_nodes.get(index))
                                .and_then(|node| node.as_object().ok())
                                .and_then(|fields| fields.get("node"))
                            {
                                pending.push((node, current_rule));
                            }
                        }
                    } else {
                        pending.extend(
                            fields
                                .iter()
                                .map(|(_, value)| (value, current_rule.clone())),
                        );
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
            ("conclusion_origins", JsonValue::Array(origins)),
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
            let mut inferred = if field_text(statement, "status") == "accepted" {
                by_statement.remove(&id).unwrap_or_default()
            } else {
                BTreeSet::new()
            };
            // Checking a declaration can infer facts in a temporary local
            // environment. Those remain proof evidence, not statement outputs.
            let published = statement
                .as_object()
                .ok()
                .and_then(|fields| fields.get("produced_fact_ids"))
                .and_then(|facts| facts.as_array().ok())
                .unwrap_or(&[]);
            inferred.retain(|id| {
                published
                    .iter()
                    .any(|fact| fact.as_str().ok() == Some(id.as_str()))
            });
            if let JsonValue::Object(fields) = statement {
                fields.insert(
                    "inferred_fact_ids".into(),
                    strings(&inferred.into_iter().collect::<Vec<_>>()),
                );
            }
        }
    }
}
