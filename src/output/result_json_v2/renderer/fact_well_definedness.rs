//! Fact well-definedness proofs, binders, parameters, and local facts.

use super::*;

impl StmtResultJsonV2 {
    pub(in super::super) fn fact_well_definedness(
        &mut self,
        result: &SuccessVerifyFactWellDefinedResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyFactWellDefinedResult"),
            (
                "recursive".to_string(),
                result
                    .recursive
                    .as_ref()
                    .map(|proof| self.fact_well_definedness_proof(proof))
                    .unwrap_or(JsonValue::Null),
            ),
        ])
    }

    pub(in super::super) fn fact_well_definedness_proof(
        &mut self,
        result: &SuccessVerifyFactWellDefinedProofResult,
    ) -> JsonValue {
        match result {
            SuccessVerifyFactWellDefinedProofResult::AtomicFact(result) => object(vec![
                string_field("kind", "AtomicFact"),
                string_field("statement", result.statement.to_string()),
                (
                    "arguments".to_string(),
                    array(
                        result
                            .arguments
                            .iter()
                            .map(|argument| {
                                object(vec![
                                    number_field("argument_index", argument.argument_index),
                                    string_field("object", argument.source_object.to_string()),
                                    ("result".to_string(), self.shared_wd_obj(&argument.result)),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "predicate".to_string(),
                    object(vec![
                        string_field("kind", "SuccessVerifyAtomicPredicateWellDefinedResult"),
                        string_field("name", result.predicate.name.clone()),
                        number_field("expected_arity", result.predicate.expected_arity),
                        (
                            "domain_checks".to_string(),
                            array(
                                result
                                    .predicate
                                    .domain_checks
                                    .iter()
                                    .map(|check| {
                                        object(vec![
                                            string_field(
                                                "role",
                                                atomic_predicate_domain_check_role(check.role),
                                            ),
                                            ("result".to_string(), self.stmt_result(&check.result)),
                                        ])
                                    })
                                    .collect(),
                            ),
                        ),
                    ]),
                ),
            ]),
            SuccessVerifyFactWellDefinedProofResult::AndFact(result) => object(vec![
                string_field("kind", "AndFact"),
                string_field("statement", result.statement.to_string()),
                (
                    "conjuncts".to_string(),
                    array(
                        result
                            .conjuncts
                            .iter()
                            .map(|child| self.fact_well_definedness_proof(child))
                            .collect(),
                    ),
                ),
            ]),
            SuccessVerifyFactWellDefinedProofResult::ChainFact(result) => object(vec![
                string_field("kind", "ChainFact"),
                string_field("statement", result.statement.to_string()),
                (
                    "comparisons".to_string(),
                    array(
                        result
                            .comparisons
                            .iter()
                            .map(|child| self.fact_well_definedness_proof(child))
                            .collect(),
                    ),
                ),
            ]),
            SuccessVerifyFactWellDefinedProofResult::OrFact(result) => object(vec![
                string_field("kind", "OrFact"),
                string_field("statement", result.statement.to_string()),
                (
                    "branches".to_string(),
                    array(
                        result
                            .branches
                            .iter()
                            .map(|child| self.fact_well_definedness_proof(child))
                            .collect(),
                    ),
                ),
            ]),
            SuccessVerifyFactWellDefinedProofResult::ExistFact(result) => object(vec![
                string_field("kind", "ExistFact"),
                string_field("statement", result.statement.to_string()),
                (
                    "binder".to_string(),
                    self.fact_binder_result(&result.binder),
                ),
                (
                    "body".to_string(),
                    array(
                        result
                            .body
                            .iter()
                            .map(|child| self.local_fact_wd_result(child))
                            .collect(),
                    ),
                ),
            ]),
            SuccessVerifyFactWellDefinedProofResult::ForallFact(result) => object(vec![
                string_field("kind", "ForallFact"),
                string_field("statement", result.statement.to_string()),
                (
                    "binder".to_string(),
                    self.fact_binder_result(&result.binder),
                ),
                (
                    "premises".to_string(),
                    array(
                        result
                            .premises
                            .iter()
                            .map(|child| self.local_fact_wd_result(child))
                            .collect(),
                    ),
                ),
                (
                    "conclusions".to_string(),
                    array(
                        result
                            .conclusions
                            .iter()
                            .map(|child| self.local_fact_wd_result(child))
                            .collect(),
                    ),
                ),
            ]),
            SuccessVerifyFactWellDefinedProofResult::ForallFactWithIff(result) => object(vec![
                string_field("kind", "ForallFactWithIff"),
                string_field("statement", result.statement.to_string()),
                (
                    "forward".to_string(),
                    self.fact_well_definedness_proof(&result.forward),
                ),
                (
                    "reverse".to_string(),
                    self.fact_well_definedness_proof(&result.reverse),
                ),
            ]),
            SuccessVerifyFactWellDefinedProofResult::NotForallFact(result) => object(vec![
                string_field("kind", "NotForallFact"),
                string_field("statement", result.statement.to_string()),
                (
                    "inner".to_string(),
                    self.fact_well_definedness_proof(&result.inner),
                ),
            ]),
        }
    }

    pub(in super::super) fn fact_binder_result(
        &mut self,
        result: &SuccessVerifyFactBinderResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyFactBinderResult"),
            (
                "parameter_groups".to_string(),
                self.fact_parameter_groups(&result.parameter_groups),
            ),
        ])
    }

    pub(in super::super) fn fact_parameter_groups(
        &mut self,
        groups: &[SuccessVerifyFactParameterGroupResult],
    ) -> JsonValue {
        array(
            groups
                .iter()
                .map(|group| {
                    object(vec![
                        number_field("group_index", group.group_index),
                        string_field("parameter_type", group.parameter_type.to_string()),
                        (
                            "carrier".to_string(),
                            group
                                .carrier
                                .as_ref()
                                .map(|carrier| self.wd_child_result(carrier))
                                .unwrap_or(JsonValue::Null),
                        ),
                        (
                            "parameters".to_string(),
                            array(
                                group
                                    .parameters
                                    .iter()
                                    .map(|parameter| self.wd_binder_premise_result(parameter))
                                    .collect(),
                            ),
                        ),
                    ])
                })
                .collect(),
        )
    }

    pub(in super::super) fn local_fact_wd_result(
        &mut self,
        result: &SuccessVerifyLocalFactWellDefinedResult,
    ) -> JsonValue {
        object(vec![
            string_field("proposition", result.proposition.to_string()),
            (
                "well_definedness".to_string(),
                self.fact_well_definedness_proof(&result.well_definedness),
            ),
            ("store".to_string(), self.store_fact(&result.store)),
        ])
    }
}
