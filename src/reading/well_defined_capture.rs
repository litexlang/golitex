//! Read-only WD registration index. Creation comes from the two typed formed-
//! object records; references reuse those exact IDs, never object spelling.
use super::*;

impl Capture {
    pub fn index_well_definedness(&mut self, environment: &ExecEnv) {
        let mut entries = environment
            .well_defined_objects
            .wd_id_to_object
            .iter()
            .collect::<Vec<_>>();
        entries.sort_by_key(|(id, _)| id.value());
        for (id, object_value) in entries {
            self.well_definedness
                .entry(id.to_string())
                .or_insert_with(|| {
                    object(vec![
                        ("id", text(&id.to_string())),
                        ("object", text(&object_value.readable_string())),
                        ("scope_id", text(&self.current_scope)),
                        ("coverage", text("registration")),
                    ])
                });
        }
    }

    pub fn wd_identity(&mut self, id: &WellDefinednessId, _runtime: &Runtime) -> JsonValue {
        if !self.capturing_ast {
            self.wd_uses.insert(id.to_string());
        }
        object(vec![
            ("kind", text("well_definedness_identity")),
            ("id", text(&id.to_string())),
        ])
    }

    pub fn wd_registration(&mut self, id: &WellDefinednessId, output: &JsonValue) {
        if self.capturing_ast {
            return;
        }
        let registration = self.intern_evidence(output.clone());
        if let Some(JsonValue::Object(fields)) = self.well_definedness.get_mut(&id.to_string()) {
            if fields.get("producer_statement_id").is_none() {
                fields.insert(
                    "producer_statement_id".into(),
                    text(&self.current_statement),
                );
                fields.insert("registration".into(), registration);
            }
        }
    }

    pub fn wd_evidence(&mut self, id: &WellDefinednessId, evidence: &JsonValue, kind: &str) {
        if let Some(JsonValue::Object(fields)) = self.well_definedness.get_mut(&id.to_string()) {
            if fields.get("evidence").is_none() {
                fields.insert("evidence".into(), evidence.clone());
                fields.insert("evidence_kind".into(), text(kind));
            }
        }
    }

    pub fn evidence_field(&self, value: &JsonValue, name: &str) -> Option<JsonValue> {
        let mut value = value.clone();
        let mut seen = BTreeSet::new();
        while field_text(&value, "kind") == "evidence_reference" {
            let id = field_text(&value, "evidence_id");
            if !seen.insert(id.clone()) {
                return None;
            }
            value = id
                .strip_prefix("evidence")
                .and_then(|index| index.parse::<usize>().ok())
                .and_then(|index| self.evidence_nodes.get(index))
                .and_then(|entry| entry.as_object().ok())
                .and_then(|fields| fields.get("node"))?
                .clone();
        }
        value
            .as_object()
            .ok()?
            .get("fields")?
            .as_object()
            .ok()?
            .get(name)
            .cloned()
    }

    pub fn annotate_wd_coverage(&mut self) {
        for statement in &mut self.statements {
            if let JsonValue::Object(fields) = statement {
                let ids = fields
                    .get("well_definedness_ids")
                    .and_then(|value| value.as_array().ok());
                let Some(ids) = ids else { continue };
                let missing = ids
                    .iter()
                    .filter_map(|id| id.as_str().ok())
                    .filter(|id| {
                        self.well_definedness.get(*id).is_none_or(|entry| {
                            field_text(entry, "producer_statement_id").is_empty()
                        })
                    })
                    .map(ToString::to_string)
                    .collect::<Vec<_>>();
                if let Some(JsonValue::Object(mut coverage)) = fields.get("coverage").cloned() {
                    coverage.insert(
                        "well_definedness".into(),
                        text(if missing.is_empty() {
                            "complete"
                        } else {
                            "partial"
                        }),
                    );
                    coverage.insert("missing_well_definedness_ids".into(), strings(&missing));
                    fields.insert("coverage".into(), JsonValue::Object(coverage));
                }
            }
        }
    }
}
