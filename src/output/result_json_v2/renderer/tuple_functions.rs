//! Tuple, Cartesian, and indexed function results.

use super::*;

impl StmtResultJsonV2 {
    pub(in super::super) fn tuple_or_cart_stmt(
        &mut self,
        kind: &str,
        statement: String,
        common: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyTupleOrCartDefinitionResult>,
    ) -> JsonValue {
        let verification = verification
            .map(|verification| {
                object(vec![
                    string_field("kind", "SuccessVerifyTupleOrCartDefinitionResult"),
                    (
                        "value_well_definedness".to_string(),
                        self.shared_wd_obj(&verification.value_well_definedness),
                    ),
                    (
                        "dimension".to_string(),
                        object(vec![
                            string_field("kind", "SuccessVerifyTupleOrCartDimensionResult"),
                            (
                                "positive_check".to_string(),
                                self.stmt_result(&verification.dimension.positive_check),
                            ),
                            (
                                "at_least_two_check".to_string(),
                                self.stmt_result(&verification.dimension.at_least_two_check),
                            ),
                        ]),
                    ),
                ])
            })
            .unwrap_or(JsonValue::Null);
        self.non_fact_stmt(
            kind,
            statement,
            common,
            vec![("verification".to_string(), verification)],
        )
    }

    pub(in super::super) fn indexed_function_stmt(
        &mut self,
        kind: &str,
        statement: String,
        common: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyIndexedFunctionDefinitionResult>,
    ) -> JsonValue {
        let verification = verification
            .map(|verification| {
                object(vec![
                    string_field("kind", "SuccessVerifyIndexedFunctionDefinitionResult"),
                    (
                        "well_definedness".to_string(),
                        object(vec![
                            string_field(
                                "kind",
                                "SuccessVerifyIndexedFunctionDefinitionWellDefinedResult",
                            ),
                            (
                                "surface_set".to_string(),
                                self.shared_wd_obj(&verification.well_definedness.surface_set),
                            ),
                            (
                                "anonymous_function".to_string(),
                                self.shared_wd_obj(
                                    &verification.well_definedness.anonymous_function,
                                ),
                            ),
                            (
                                "function_set".to_string(),
                                self.shared_wd_obj(&verification.well_definedness.function_set),
                            ),
                        ]),
                    ),
                    (
                        "bound_checks".to_string(),
                        self.stmt_results(&verification.bound_checks),
                    ),
                    (
                        "assumption_infers".to_string(),
                        infer_result_value(&verification.assumption_infers),
                    ),
                    (
                        "return_check".to_string(),
                        self.stmt_result(&verification.return_check),
                    ),
                ])
            })
            .unwrap_or(JsonValue::Null);
        self.non_fact_stmt(
            kind,
            statement,
            common,
            vec![("verification".to_string(), verification)],
        )
    }
}
