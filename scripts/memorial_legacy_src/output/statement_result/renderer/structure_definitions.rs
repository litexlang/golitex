//! Structure definition results.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn def_struct_stmt(
        &mut self,
        result: &SuccessDefStructStmtResult,
    ) -> JsonValue {
        let run_in_local_env = result
            .run_in_local_env
            .as_ref()
            .map(|local| {
                object(vec![
                    string_field("kind", "SuccessVerifyDefStructLocalEnvResult"),
                    (
                        "structure_parameter_definition".to_string(),
                        local
                            .structure_parameter_definition
                            .as_ref()
                            .map(infer_result_value)
                            .unwrap_or(JsonValue::Null),
                    ),
                    (
                        "structure_domains".to_string(),
                        array(
                            local
                                .structure_domains
                                .iter()
                                .map(|domain| {
                                    object(vec![
                                        number_field("domain_index", domain.domain_index),
                                        string_field("proposition", domain.proposition.to_string()),
                                        (
                                            "well_definedness".to_string(),
                                            self.fact_well_definedness(&domain.well_definedness),
                                        ),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                    (
                        "field_types".to_string(),
                        array(
                            local
                                .field_types
                                .iter()
                                .map(|field| {
                                    object(vec![
                                        number_field("field_index", field.field_index),
                                        string_field("binding", field.binding.name()),
                                        string_field("field_type", field.field_type.to_string()),
                                        (
                                            "well_definedness".to_string(),
                                            self.shared_wd_obj(&field.well_definedness),
                                        ),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                    (
                        "field_scope_run_in_local_env".to_string(),
                        object(vec![
                            (
                                "field_definitions".to_string(),
                                array(
                                    local
                                        .field_scope_run_in_local_env
                                        .field_definitions
                                        .iter()
                                        .map(|field| {
                                            object(vec![
                                                number_field("field_index", field.field_index),
                                                string_field("binding", field.binding.name()),
                                                string_field(
                                                    "field_type",
                                                    field.field_type.to_string(),
                                                ),
                                                (
                                                    "infers".to_string(),
                                                    infer_result_value(&field.infers),
                                                ),
                                            ])
                                        })
                                        .collect(),
                                ),
                            ),
                            (
                                "equivalent_facts".to_string(),
                                array(
                                    local
                                        .field_scope_run_in_local_env
                                        .equivalent_facts
                                        .iter()
                                        .map(|fact| self.local_fact_wd_result(fact))
                                        .collect(),
                                ),
                            ),
                        ]),
                    ),
                ])
            })
            .unwrap_or(JsonValue::Null);
        self.non_fact_stmt(
            "DefStructStmt",
            result.statement.to_string(),
            &result.common,
            vec![("run_in_local_env".to_string(), run_in_local_env)],
        )
    }
}
