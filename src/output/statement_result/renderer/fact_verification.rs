//! Fact verification and proof result dispatch.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn verify_fact(&mut self, result: &SuccessVerifyFactResult) -> JsonValue {
        object(vec![
            string_field("kind", verify_fact_kind(result)),
            string_field("statement", result.fact().to_string()),
            ("proof".to_string(), self.fact_proof(result.proof())),
        ])
    }

    pub(in super::super) fn fact_proof(&mut self, proof: &SuccessFactProofResult) -> JsonValue {
        match proof {
            SuccessFactProofResult::BuiltinRule(result) => {
                self.builtin_proof("BuiltinRule", result)
            }
            SuccessFactProofResult::BuiltinStrategy(result) => {
                self.builtin_proof("BuiltinStrategy", result)
            }
            SuccessFactProofResult::StoredFactCitation(result) => object(vec![
                string_field("kind", "StoredFactCitation"),
                optional_string_field("detail", result.detail.as_deref()),
                string_field("source_fact", result.source_fact.to_string()),
                string_field("source_fact_id", fact_id(result.source_fact_id)),
            ]),
            SuccessFactProofResult::DefinitionReduction(result) => object(vec![
                string_field("kind", "DefinitionReduction"),
                optional_string_field("detail", result.detail.as_deref()),
                string_field("definition", result.definition.to_string()),
                (
                    "argument_verification".to_string(),
                    args_satisfy_param_def_verification_value(
                        self,
                        &result.verification.argument_verification,
                    ),
                ),
                (
                    "clause_checks".to_string(),
                    array(
                        result
                            .verification
                            .clause_facts
                            .iter()
                            .zip(result.verification.clause_checks.iter())
                            .map(|(fact, check)| {
                                object(vec![
                                    string_field("fact", fact.to_string()),
                                    ("result".to_string(), self.stmt_result(check)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => object(vec![
                string_field("kind", "CheckedFunctionDefinitionReduction"),
                optional_string_field("detail", result.detail.as_deref()),
                string_field(
                    "definition_object",
                    result.verification.definition_object.to_string(),
                ),
                string_field(
                    "defining_equality",
                    result.verification.defining_equality.to_string(),
                ),
                string_field(
                    "defining_equality_fact_id",
                    fact_id(result.verification.defining_equality_fact_id),
                ),
                string_field(
                    "application_side",
                    result.verification.application_side.to_string(),
                ),
                string_field("reduced", result.verification.reduced.to_string()),
                string_field("other_side", result.verification.other_side.to_string()),
                (
                    "application_is_left".to_string(),
                    JsonValue::Bool(result.verification.application_is_left),
                ),
                (
                    "reduced_matches_other_by_alpha".to_string(),
                    JsonValue::Bool(result.verification.reduced_matches_other_by_alpha),
                ),
            ]),
            SuccessFactProofResult::DiagnosticOnly(result) => object(vec![
                string_field("kind", "DiagnosticOnly"),
                string_field("detail", result.detail.clone()),
            ]),
            SuccessFactProofResult::KnownForallInstantiation(result) => self.known_forall(result),
            SuccessFactProofResult::CombinedProofs(result) => object(vec![
                string_field("kind", "CombinedProofs"),
                (
                    "primary".to_string(),
                    result
                        .primary
                        .as_ref()
                        .map(|proof| self.verify_fact(proof))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "steps".to_string(),
                    array(
                        result
                            .steps
                            .iter()
                            .map(|step| self.stmt_result(step))
                            .collect(),
                    ),
                ),
            ]),
            SuccessFactProofResult::ForallProof(result) => object(vec![
                string_field("kind", "ForallProof"),
                string_field("forall_fact", result.forall_fact.to_string()),
                (
                    "parameter_assumptions".to_string(),
                    array(
                        result
                            .parameter_assumptions
                            .iter()
                            .map(|assumption| {
                                object(vec![
                                    string_field("fact", assumption.fact.to_string()),
                                    string_field("fact_id", fact_id(assumption.fact_id)),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "domain_assumptions".to_string(),
                    array(
                        result
                            .domain_assumptions
                            .iter()
                            .map(|assumption| {
                                object(vec![
                                    string_field("fact", assumption.fact.to_string()),
                                    string_field("fact_id", fact_id(assumption.fact_id)),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "assumption_infers".to_string(),
                    infer_result_value(&result.assumption_infers),
                ),
                (
                    "proves".to_string(),
                    array(
                        result
                            .proves
                            .iter()
                            .map(|proved| {
                                object(vec![
                                    string_field("statement", proved.stmt.to_string()),
                                    ("result".to_string(), self.stmt_result(&proved.result)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
            SuccessFactProofResult::Transform(result) => object(vec![
                string_field("kind", "Transform"),
                (
                    "rule".to_string(),
                    fact_transformation_rule_value(&result.rule),
                ),
                ("source".to_string(), self.verify_fact(&result.source)),
            ]),
            SuccessFactProofResult::Reuse(result) => object(vec![
                string_field("kind", "Reuse"),
                ("source".to_string(), self.shared_fact(&result.source)),
            ]),
        }
    }
}
