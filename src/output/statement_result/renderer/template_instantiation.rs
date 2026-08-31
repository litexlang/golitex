//! Template instantiation results.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn template_instantiation(
        &mut self,
        result: &SuccessTemplateInstantiationResult,
    ) -> JsonValue {
        match result {
            SuccessTemplateInstantiationResult::Reused(result) => object(vec![
                string_field("kind", "Reused"),
                string_field("application", result.application.to_string()),
            ]),
            SuccessTemplateInstantiationResult::Created(result) => object(vec![
                string_field("kind", "Created"),
                string_field("application", result.application.to_string()),
                (
                    "template_argument_results".to_string(),
                    array(
                        result
                            .template_argument_results
                            .iter()
                            .map(|argument| {
                                object(vec![
                                    number_field("argument_index", argument.argument_index),
                                    string_field("argument", argument.argument.to_string()),
                                    string_field(
                                        "expected_type",
                                        argument.expected_type.to_string(),
                                    ),
                                    (
                                        "verification".to_string(),
                                        self.wd_fact_check(&argument.verification),
                                    ),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "template_domain_results".to_string(),
                    array(
                        result
                            .template_domain_results
                            .iter()
                            .map(|domain| {
                                object(vec![
                                    number_field("domain_index", domain.domain_index),
                                    ("proof".to_string(), self.wd_fact_check(&domain.proof)),
                                    ("store".to_string(), self.store_fact(&domain.store)),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "surface_equality".to_string(),
                    self.store_fact(&result.surface_equality),
                ),
                (
                    "body_statement_result".to_string(),
                    self.success_stmt(&result.body_statement_result),
                ),
                (
                    "public_value_equalities".to_string(),
                    array(
                        result
                            .public_value_equalities
                            .iter()
                            .map(|store| self.store_fact(store))
                            .collect(),
                    ),
                ),
                (
                    "supplemental_stores".to_string(),
                    array(
                        result
                            .supplemental_stores
                            .iter()
                            .map(|store| self.store_fact(store))
                            .collect(),
                    ),
                ),
                (
                    "registered_set_builder".to_string(),
                    result
                        .registered_set_builder
                        .as_ref()
                        .map(|value| string(value.to_string()))
                        .unwrap_or(JsonValue::Null),
                ),
            ]),
        }
    }
}
