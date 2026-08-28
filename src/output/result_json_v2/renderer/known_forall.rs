//! Known universal fact instantiation.

use super::*;

impl StmtResultJsonV2 {
    pub(in super::super) fn known_forall(
        &mut self,
        result: &SuccessInstantiateKnownForallResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "KnownForallInstantiation"),
            string_field("source_fact", result.source_fact.to_string()),
            string_field("source_fact_id", fact_id(result.source_fact_id)),
            (
                "source_conclusion_location".to_string(),
                forall_conclusion_location(result.source_conclusion_location),
            ),
            (
                "instantiation".to_string(),
                array(
                    result
                        .instantiation
                        .iter()
                        .map(|item| {
                            object(vec![
                                string_field("parameter", item.param.clone()),
                                string_field("argument", item.arg_obj.to_string()),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "requirements".to_string(),
                array(
                    result
                        .requirements
                        .iter()
                        .map(|requirement| {
                            object(vec![
                                string_field(
                                    "kind",
                                    match requirement.kind {
                                        KnownForallRequirementKind::ParameterType => {
                                            "ParameterType"
                                        }
                                        KnownForallRequirementKind::Domain => "Domain",
                                    },
                                ),
                                string_field("statement", requirement.stmt.to_string()),
                                ("result".to_string(), self.stmt_result(&requirement.result)),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
    }
}
