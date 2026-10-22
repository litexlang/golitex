//! Fact-level context comes from the stage that actually stored the seed.
//! Local hypotheses are not verified truth; inference and publication stay
//! separate from this read-only presentation index.
use super::*;

impl Capture {
    pub fn fact_context(
        &mut self,
        store: &StoreFactAndInferResult,
        role: &str,
        output: &JsonValue,
        evidence_field: &str,
    ) {
        if self.capturing_ast {
            return;
        }
        let evidence = output
            .as_object()
            .ok()
            .and_then(|fields| fields.get("fields"))
            .and_then(|fields| fields.as_object().ok())
            .and_then(|fields| fields.get(evidence_field))
            .cloned();
        let primary = store.primary_fact_id().to_string();
        for formed in &store.formed_subjects {
            if let Some(JsonValue::Object(fields)) =
                self.well_definedness.get_mut(&formed.wd_id.to_string())
            {
                fields.insert("source_fact_id".into(), text(&primary));
            }
            if let Some(evidence) = &evidence {
                self.wd_evidence(
                    &formed.wd_id,
                    evidence,
                    if role == "hypothesis" {
                        "well_definedness"
                    } else {
                        "verification"
                    },
                );
            }
        }
        for id in store.store.stored_fact_ids() {
            if let Some(JsonValue::Object(fields)) = self.facts.get_mut(&id.to_string()) {
                if fields.get("role").is_none() {
                    fields.insert("role".into(), text(role));
                    fields.insert(
                        "is_primary".into(),
                        JsonValue::Bool(id.to_string() == primary),
                    );
                    if let Some(evidence) = &evidence {
                        fields.insert("evidence".into(), evidence.clone());
                    }
                }
            }
        }
    }
}
