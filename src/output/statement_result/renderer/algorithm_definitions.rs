//! Algorithm definition results.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn def_algo_stmt(
        &mut self,
        result: &SuccessDefAlgoStmtResult,
    ) -> JsonValue {
        let run_in_local_env = result
            .run_in_local_env
            .as_ref()
            .map(|local| {
                object(vec![
                    string_field("kind", "SuccessVerifyDefAlgoLocalEnvResult"),
                    string_field(
                        "declared_function_set",
                        local.definition_function_set.to_string(),
                    ),
                    (
                        "parameter_retagging".to_string(),
                        array(
                            local
                                .parameter_retagging
                                .iter()
                                .map(|parameter| {
                                    object(vec![
                                        number_field("parameter_index", parameter.parameter_index),
                                        string_field(
                                            "source_binding",
                                            parameter.source_binding.name(),
                                        ),
                                        string_field(
                                            "verification_object",
                                            parameter.verification_object.to_string(),
                                        ),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                    (
                        "requirement_facts".to_string(),
                        display_values(&local.requirement_facts),
                    ),
                    string_field(
                        "parameter_definition",
                        local.parameter_definition.to_string(),
                    ),
                    string_field("function_call", local.function_call.to_string()),
                    (
                        "cases".to_string(),
                        array(
                            local
                                .cases
                                .iter()
                                .map(|case| {
                                    object(vec![
                                        number_field("case_index", case.case_index),
                                        string_field(
                                            "verification_fact",
                                            case.verification_fact.to_string(),
                                        ),
                                        (
                                            "verification".to_string(),
                                            self.stmt_result(&case.verification),
                                        ),
                                    ])
                                })
                                .collect(),
                        ),
                    ),
                    (
                        "default_return".to_string(),
                        local
                            .default_return
                            .as_ref()
                            .map(|default| {
                                object(vec![
                                    string_field(
                                        "verification_fact",
                                        default.verification_fact.to_string(),
                                    ),
                                    (
                                        "verification".to_string(),
                                        self.stmt_result(&default.verification),
                                    ),
                                ])
                            })
                            .unwrap_or(JsonValue::Null),
                    ),
                    (
                        "coverage".to_string(),
                        local
                            .coverage
                            .as_ref()
                            .map(|coverage| {
                                object(vec![
                                    string_field(
                                        "verification_fact",
                                        coverage.verification_fact.to_string(),
                                    ),
                                    (
                                        "verification".to_string(),
                                        self.stmt_result(&coverage.verification),
                                    ),
                                ])
                            })
                            .unwrap_or(JsonValue::Null),
                    ),
                ])
            })
            .unwrap_or(JsonValue::Null);
        self.non_fact_stmt(
            "DefAlgoStmt",
            result.statement.to_string(),
            &result.common,
            vec![("run_in_local_env".to_string(), run_in_local_env)],
        )
    }
}
