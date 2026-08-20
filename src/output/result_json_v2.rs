use crate::common::json_value::{render_json_value, JsonValue};
use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

const SCHEMA: &str = "litex.statement-result.v2";

/// Deterministic structural JSON for the recursive runtime result.
///
/// This visitor reads the result only. It does not query `Runtime`, infer a
/// proof rule from a diagnostic label, or flatten child results into a legacy
/// output DTO.
pub fn display_stmt_result_json_v2(result: &StmtResult) -> String {
    render_json_value(&StmtResultJsonV2::default().stmt_result(result), 0)
}

#[derive(Default)]
struct StmtResultJsonV2 {
    shared_fact_ids: HashMap<usize, String>,
    next_shared_fact_id: usize,
    shared_wd_obj_ids: HashMap<usize, String>,
    next_shared_wd_obj_id: usize,
}

impl StmtResultJsonV2 {
    fn stmt_result(&mut self, result: &StmtResult) -> JsonValue {
        match result {
            StmtResult::Success(success) => object(vec![
                string_field("schema", SCHEMA),
                string_field("outcome", "success"),
                ("result".to_string(), self.success_stmt(success)),
            ]),
            StmtResult::Unknown(unknown) => object(vec![
                string_field("schema", SCHEMA),
                string_field("outcome", "unknown"),
                ("result".to_string(), self.unknown_stmt(unknown)),
            ]),
        }
    }

    fn success_stmt(&mut self, success: &SuccessStmtResult) -> JsonValue {
        match success {
            SuccessStmtResult::Fact(result) => self.success_fact_stmt(result),
            SuccessStmtResult::UnsafeStmt(result) => match result {
                SuccessUnsafeStmtResult::TrustStmt(result) => self.non_fact_stmt(
                    "TrustStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![],
                ),
                SuccessUnsafeStmtResult::TrustHaveStmt(result) => self.non_fact_stmt(
                    "TrustHaveStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![],
                ),
            },
            SuccessStmtResult::DefObjStmt(result) => self.def_obj_stmt(result),
            SuccessStmtResult::DefPredicateStmt(result) => match result {
                SuccessDefPredicateStmtResult::DefPropStmt(result) => self.non_fact_stmt(
                    "DefPropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![],
                ),
                SuccessDefPredicateStmtResult::DefAbstractPropStmt(result) => self.non_fact_stmt(
                    "DefAbstractPropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![],
                ),
            },
            SuccessStmtResult::DefInterfaceStmt(result) => match result {
                SuccessDefInterfaceStmtResult::DefSettingStmt(result) => self.non_fact_stmt(
                    "DefSettingStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![],
                ),
                SuccessDefInterfaceStmtResult::DefTemplateStmt(result) => self.non_fact_stmt(
                    "DefTemplateStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![],
                ),
                SuccessDefInterfaceStmtResult::DefStructStmt(result) => self.non_fact_stmt(
                    "DefStructStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![],
                ),
            },
            SuccessStmtResult::DefAlgoStmt(result) => self.non_fact_stmt(
                "DefAlgoStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
            SuccessStmtResult::DefThmStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.theorem_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "DefThmStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessStmtResult::AxiomStmt(result) => {
                let well_definedness = result
                    .well_definedness
                    .as_ref()
                    .map(|well_definedness| self.fact_well_definedness(well_definedness))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "AxiomStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("well_definedness".to_string(), well_definedness)],
                )
            }
            SuccessStmtResult::DefStrategyStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyStrategyDefinitionResult"),
                            (
                                "proof_steps".to_string(),
                                self.stmt_results(&verification.proof_steps),
                            ),
                            (
                                "conclusion_checks".to_string(),
                                self.stmt_results(&verification.conclusion_checks),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "DefStrategyStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessStmtResult::By(result) => self.by_stmt(result),
            SuccessStmtResult::Witness(result) => self.witness_stmt(result),
            SuccessStmtResult::ProofBlock(result) => self.proof_block_stmt(result),
            SuccessStmtResult::Command(result) => self.command_stmt(result),
        }
    }

    fn non_fact_stmt(
        &mut self,
        kind: &str,
        statement: String,
        common: &SuccessStmtCommonResult,
        mut specific_fields: Vec<(String, JsonValue)>,
    ) -> JsonValue {
        let mut fields = vec![
            string_field("kind", kind),
            string_field("statement", statement),
            ("common".to_string(), self.common(common)),
        ];
        fields.append(&mut specific_fields);
        object(fields)
    }

    fn def_obj_stmt(&mut self, result: &SuccessDefObjStmtResult) -> JsonValue {
        match result {
            SuccessDefObjStmtResult::LetObjStmt(result) => self.non_fact_stmt(
                "LetObjStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
            SuccessDefObjStmtResult::HaveObjInNonemptySetStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| object_choice_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "HaveObjInNonemptySetStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefObjStmtResult::HaveObjEqualStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyHaveObjEqualResult"),
                            (
                                "type_checks".to_string(),
                                self.stmt_results(&verification.type_checks),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "HaveObjEqualStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefObjStmtResult::HaveObjByExistFactsStmt(result) => {
                let verification =
                    optional_existential_elimination(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "HaveObjByExistFactsStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefObjStmtResult::ObtainObjFromExistFact(result) => {
                let verification =
                    optional_existential_elimination(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ObtainObjFromExistFact",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefObjStmtResult::ObtainObjFromAtomicFact(result) => {
                let verification =
                    optional_existential_elimination(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ObtainObjFromAtomicFact",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefObjStmtResult::ObtainObjFromThm(result) => {
                let verification =
                    optional_existential_elimination(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ObtainObjFromThm",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefObjStmtResult::HaveByPreimageStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyPreimageResult"),
                            (
                                "source_membership_check".to_string(),
                                self.stmt_result(&verification.source_membership_check),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "HaveByPreimageStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefObjStmtResult::HaveFnEqualStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| function_definition_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "HaveFnEqualStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefObjStmtResult::HaveFnEqualCaseByCaseStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyCaseFunctionDefinitionResult"),
                            (
                                "coverage_check".to_string(),
                                self.stmt_result(&verification.coverage_check),
                            ),
                            (
                                "return_checks".to_string(),
                                self.stmt_results(&verification.return_checks),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "HaveFnEqualCaseByCaseStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefObjStmtResult::HaveFnByInducStmt(result) => self.non_fact_stmt(
                "HaveFnByInducStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
            SuccessDefObjStmtResult::HaveFnByForallExistUniqueStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyFunctionFromUniqueExistenceResult"),
                            (
                                "source_forall_check".to_string(),
                                verification
                                    .source_forall_check
                                    .as_ref()
                                    .map(|check| self.stmt_result(check))
                                    .unwrap_or(JsonValue::Null),
                            ),
                            (
                                "proof_steps".to_string(),
                                self.stmt_results(&verification.proof_steps),
                            ),
                            (
                                "conclusion_checks".to_string(),
                                self.stmt_results(&verification.conclusion_checks),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "HaveFnByForallExistUniqueStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefObjStmtResult::HaveTupleStmt(result) => self.tuple_or_cart_stmt(
                "HaveTupleStmt",
                result.statement.to_string(),
                &result.common,
                result.verification.as_ref(),
            ),
            SuccessDefObjStmtResult::HaveCartStmt(result) => self.tuple_or_cart_stmt(
                "HaveCartStmt",
                result.statement.to_string(),
                &result.common,
                result.verification.as_ref(),
            ),
            SuccessDefObjStmtResult::HaveSeqStmt(result) => self.indexed_function_stmt(
                "HaveSeqStmt",
                result.statement.to_string(),
                &result.common,
                result.verification.as_ref(),
            ),
            SuccessDefObjStmtResult::HaveFiniteSeqStmt(result) => self.indexed_function_stmt(
                "HaveFiniteSeqStmt",
                result.statement.to_string(),
                &result.common,
                result.verification.as_ref(),
            ),
            SuccessDefObjStmtResult::HaveMatrixStmt(result) => self.indexed_function_stmt(
                "HaveMatrixStmt",
                result.statement.to_string(),
                &result.common,
                result.verification.as_ref(),
            ),
        }
    }

    fn tuple_or_cart_stmt(
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

    fn indexed_function_stmt(
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

    fn by_stmt(&mut self, result: &SuccessByStmtResult) -> JsonValue {
        match result {
            SuccessByStmtResult::ByCasesStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.by_cases_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByCasesStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByContraStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.by_contra_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByContraStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByEnumerateFiniteSetStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        by_enumerate_finite_set_verification_value(self, verification)
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByEnumerateFiniteSetStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByFiniteSetInducStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_induc_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByFiniteSetInducStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByInducStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_induc_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByInducStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByForStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_for_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByForStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByExtensionStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_extension_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByExtensionStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByEnumerateRangeStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_enumerate_range_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByEnumerateRangeStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByClosedRangeAsCasesStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_enumerate_range_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByClosedRangeAsCasesStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByTransitivePropStmt(result) => {
                let verification = optional_prop_registration(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByTransitivePropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::BySymmetricPropStmt(result) => {
                let verification = optional_prop_registration(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "BySymmetricPropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByReflexivePropStmt(result) => {
                let verification = optional_prop_registration(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByReflexivePropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByAntisymmetricPropStmt(result) => {
                let verification = optional_prop_registration(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByAntisymmetricPropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByZornLemmaStmt(result) => {
                let verification = optional_choice_verification(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByZornLemmaStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByAxiomOfChoiceStmt(result) => {
                let verification = optional_choice_verification(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByAxiomOfChoiceStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByRegularityAxiomStmt(result) => {
                let verification = optional_choice_verification(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ByRegularityAxiomStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByDefStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_definition_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByDefStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessByStmtResult::ByStructDefStmt(result) => {
                let membership_check = result
                    .membership_check
                    .as_ref()
                    .map(|check| self.stmt_result(check))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByStructDefStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("membership_check".to_string(), membership_check)],
                )
            }
            SuccessByStmtResult::ByThmStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| by_theorem_verification_value(self, verification))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ByThmStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
        }
    }

    fn witness_stmt(&mut self, result: &SuccessWitnessStmtResult) -> JsonValue {
        match result {
            SuccessWitnessStmtResult::WitnessExistFact(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.witness_exist_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "WitnessExistFact",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessWitnessStmtResult::WitnessAtomicFact(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.witness_atomic_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "WitnessAtomicFact",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessWitnessStmtResult::WitnessNonemptySet(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyWitnessNonemptySetResult"),
                            (
                                "proof_steps".to_string(),
                                self.stmt_results(&verification.proof_steps),
                            ),
                            (
                                "nonempty_check".to_string(),
                                self.stmt_result(&verification.nonempty_check),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "WitnessNonemptySet",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
        }
    }

    fn proof_block_stmt(&mut self, result: &SuccessProofBlockStmtResult) -> JsonValue {
        match result {
            SuccessProofBlockStmtResult::ClaimStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.claim_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ClaimStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessProofBlockStmtResult::ExampleStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.claim_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "ExampleStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessProofBlockStmtResult::SketchStmt(result) => {
                let proof = result
                    .proof
                    .as_ref()
                    .map(|proof| {
                        object(vec![
                            string_field("kind", "SuccessSketchProofResult"),
                            (
                                "proof_scope".to_string(),
                                self.local_proof_scope(&proof.proof_scope),
                            ),
                            (
                                "proof_steps".to_string(),
                                self.stmt_results(&proof.proof_steps),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "SketchStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("proof".to_string(), proof)],
                )
            }
            SuccessProofBlockStmtResult::TryStmt(result) => {
                let proof = result
                    .proof
                    .as_ref()
                    .map(|proof| {
                        object(vec![
                            string_field("kind", "SuccessTryProofResult"),
                            (
                                "proof_steps".to_string(),
                                self.stmt_results(&proof.proof_steps),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "TryStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("proof".to_string(), proof)],
                )
            }
        }
    }

    fn command_stmt(&mut self, result: &SuccessCommandStmtResult) -> JsonValue {
        match result {
            SuccessCommandStmtResult::ImportStmt(result) => self.non_fact_stmt(
                "ImportStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
            SuccessCommandStmtResult::DoNothingStmt(result) => self.non_fact_stmt(
                "DoNothingStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
            SuccessCommandStmtResult::ClearStmt(result) => self.non_fact_stmt(
                "ClearStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
            SuccessCommandStmtResult::EvalStmt(result) => self.non_fact_stmt(
                "EvalStmt",
                result.statement.to_string(),
                &result.common,
                vec![(
                    "reported_store_facts".to_string(),
                    array(
                        result
                            .reported_store_facts
                            .iter()
                            .map(store_fact_output_value)
                            .collect(),
                    ),
                )],
            ),
            SuccessCommandStmtResult::UseStrategyStmt(result) => self.non_fact_stmt(
                "UseStrategyStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
            SuccessCommandStmtResult::StopStrategyStmt(result) => self.non_fact_stmt(
                "StopStrategyStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
        }
    }

    fn success_fact_stmt(&mut self, result: &SuccessFactStmtResult) -> JsonValue {
        object(vec![
            string_field("kind", "Fact"),
            string_field("statement", result.fact().to_string()),
            (
                "verification".to_string(),
                self.verify_fact(&result.verification),
            ),
            (
                "well_definedness".to_string(),
                self.fact_well_definedness(&result.well_definedness),
            ),
            ("store".to_string(), self.store_fact(&result.store)),
            (
                "execution_trace".to_string(),
                optional_trace(result.execution_trace.as_ref()),
            ),
        ])
    }

    fn fact_well_definedness(&mut self, result: &SuccessVerifyFactWellDefinedResult) -> JsonValue {
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

    fn fact_well_definedness_proof(
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

    fn shared_wd_obj(&mut self, result: &Rc<SuccessVerifyObjWellDefinedResult>) -> JsonValue {
        let pointer = Rc::as_ptr(result) as usize;
        if let Some(id) = self.shared_wd_obj_ids.get(&pointer) {
            return object(vec![string_field("$ref", id.clone())]);
        }
        let id = format!("wd-node-{}", self.next_shared_wd_obj_id);
        self.next_shared_wd_obj_id += 1;
        self.shared_wd_obj_ids.insert(pointer, id.clone());
        object(vec![
            string_field("$id", id),
            ("value".to_string(), self.wd_obj_result(result)),
        ])
    }

    fn fact_binder_result(&mut self, result: &SuccessVerifyFactBinderResult) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyFactBinderResult"),
            (
                "parameter_groups".to_string(),
                array(
                    result
                        .parameter_groups
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
                                            .map(|parameter| {
                                                self.wd_binder_premise_result(parameter)
                                            })
                                            .collect(),
                                    ),
                                ),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
    }

    fn local_fact_wd_result(
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

    fn wd_obj_result(&mut self, result: &SuccessVerifyObjWellDefinedResult) -> JsonValue {
        match result {
            SuccessVerifyObjWellDefinedResult::Direct(result) => object(vec![
                string_field("kind", "Direct"),
                string_field("object", result.object.to_string()),
                (
                    "intrinsic_result_set".to_string(),
                    result
                        .intrinsic_result_set
                        .as_ref()
                        .map(|value| string(value.to_string()))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "children".to_string(),
                    array(
                        result
                            .steps
                            .children
                            .iter()
                            .map(|child| {
                                object(vec![
                                    ("role".to_string(), wd_child_role_value(child.role)),
                                    string_field("object", child.source_object.to_string()),
                                    ("result".to_string(), self.shared_wd_obj(&child.result)),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "fact_checks".to_string(),
                    array(
                        result
                            .steps
                            .fact_checks
                            .iter()
                            .map(|check| {
                                object(vec![
                                    string_field(
                                        "expected_proposition",
                                        check.expected_proposition.to_string(),
                                    ),
                                    (
                                        "verification".to_string(),
                                        self.shared_fact(&check.verification),
                                    ),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "target_requirements".to_string(),
                    array(
                        result
                            .steps
                            .target_requirements
                            .iter()
                            .map(|requirement| {
                                object(vec![
                                    ("role".to_string(), wd_requirement_role(requirement.role)),
                                    string_field(
                                        "expected_proposition",
                                        requirement.expected_proposition.to_string(),
                                    ),
                                    (
                                        "verification".to_string(),
                                        self.shared_fact(&requirement.verification),
                                    ),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "stores".to_string(),
                    array(
                        result
                            .steps
                            .stores
                            .iter()
                            .map(|store| self.store_fact(store))
                            .collect(),
                    ),
                ),
                (
                    "binder".to_string(),
                    result
                        .steps
                        .binder
                        .as_ref()
                        .map(|binder| self.wd_binder_result(binder))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "template_materialization".to_string(),
                    result
                        .steps
                        .template_materialization
                        .as_ref()
                        .map(|materialization| self.template_materialization(materialization))
                        .unwrap_or(JsonValue::Null),
                ),
            ]),
            SuccessVerifyObjWellDefinedResult::Reuse(result) => object(vec![
                string_field("kind", "Reuse"),
                string_field("object", result.object.to_string()),
                ("source".to_string(), self.shared_wd_obj(&result.source)),
            ]),
            SuccessVerifyObjWellDefinedResult::RecursiveReference(result) => object(vec![
                string_field("kind", "RecursiveReference"),
                string_field("object", result.object.to_string()),
                string_field("ancestor_key", result.ancestor_key.clone()),
            ]),
        }
    }

    fn template_materialization(
        &mut self,
        result: &SuccessVerifyTemplateMaterializationResult,
    ) -> JsonValue {
        match result {
            SuccessVerifyTemplateMaterializationResult::Reuse(result) => object(vec![
                string_field("kind", "Reuse"),
                string_field("instance_name", result.instance_name.clone()),
            ]),
            SuccessVerifyTemplateMaterializationResult::Materialized(result) => object(vec![
                string_field("kind", "Materialized"),
                string_field("template_name", result.template_name.clone()),
                string_field("instance_name", result.instance_name.clone()),
                (
                    "header_arguments".to_string(),
                    array(
                        result
                            .header_arguments
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
                    "header_domains".to_string(),
                    array(
                        result
                            .header_domains
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
                string_field("body_statement", result.body_statement.to_string()),
                (
                    "body_execution".to_string(),
                    self.stmt_result(&result.body_execution),
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

    fn wd_binder_result(
        &mut self,
        result: &SuccessVerifyBinderObjectWellDefinedResult,
    ) -> JsonValue {
        match result {
            SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(result) => object(vec![
                string_field("kind", "SetBuilder"),
                (
                    "parameter_carrier".to_string(),
                    self.wd_child_result(&result.parameter_carrier),
                ),
                (
                    "parameter".to_string(),
                    self.wd_binder_premise_result(&result.parameter),
                ),
                (
                    "conditions".to_string(),
                    array(
                        result
                            .conditions
                            .iter()
                            .map(|condition| {
                                object(vec![
                                    number_field("condition_index", condition.condition_index),
                                    (
                                        "well_definedness".to_string(),
                                        self.fact_well_definedness(&condition.well_definedness),
                                    ),
                                    ("store".to_string(), self.store_fact(&condition.store)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(result) => object(vec![
                string_field("kind", "FunctionSet"),
                (
                    "parameter_carriers".to_string(),
                    array(
                        result
                            .parameter_carriers
                            .iter()
                            .map(|child| self.wd_child_result(child))
                            .collect(),
                    ),
                ),
                (
                    "parameters".to_string(),
                    array(
                        result
                            .parameters
                            .iter()
                            .map(|premise| self.wd_binder_premise_result(premise))
                            .collect(),
                    ),
                ),
                (
                    "domains".to_string(),
                    array(
                        result
                            .domains
                            .iter()
                            .map(|premise| self.wd_binder_premise_result(premise))
                            .collect(),
                    ),
                ),
                (
                    "return_carrier".to_string(),
                    self.wd_child_result(&result.return_carrier),
                ),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(result) => object(vec![
                string_field("kind", "AnonymousFunction"),
                (
                    "parameter_carriers".to_string(),
                    array(
                        result
                            .parameter_carriers
                            .iter()
                            .map(|child| self.wd_child_result(child))
                            .collect(),
                    ),
                ),
                (
                    "parameters".to_string(),
                    array(
                        result
                            .parameters
                            .iter()
                            .map(|premise| self.wd_binder_premise_result(premise))
                            .collect(),
                    ),
                ),
                (
                    "domains".to_string(),
                    array(
                        result
                            .domains
                            .iter()
                            .map(|premise| self.wd_binder_premise_result(premise))
                            .collect(),
                    ),
                ),
                (
                    "return_carrier".to_string(),
                    self.wd_child_result(&result.return_carrier),
                ),
                ("body".to_string(), self.wd_child_result(&result.body)),
                (
                    "body_membership".to_string(),
                    object(vec![
                        (
                            "role".to_string(),
                            wd_requirement_role(result.body_membership.role),
                        ),
                        string_field(
                            "expected_proposition",
                            result.body_membership.expected_proposition.to_string(),
                        ),
                        (
                            "verification".to_string(),
                            self.shared_fact(&result.body_membership.verification),
                        ),
                    ]),
                ),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(result) => object(vec![
                string_field("kind", "Iteration"),
                string_field("operation", result.operation.clone()),
                (
                    "scalar_return".to_string(),
                    result
                        .scalar_return
                        .as_ref()
                        .map(|value| self.iteration_scalar_return(value))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "interval".to_string(),
                    self.iteration_interval(&result.interval),
                ),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(result) => object(vec![
                string_field("kind", "FiniteAggregate"),
                string_field("operation", result.operation.clone()),
                (
                    "scalar_return".to_string(),
                    result
                        .scalar_return
                        .as_ref()
                        .map(|value| self.iteration_scalar_return(value))
                        .unwrap_or(JsonValue::Null),
                ),
                ("mode".to_string(), self.finite_aggregate_mode(&result.mode)),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::Reduce(result) => object(vec![
                string_field("kind", "Reduce"),
                string_field("operation", result.operation.clone()),
                (
                    "signature".to_string(),
                    object(vec![
                        string_field(
                            "left_parameter_carrier",
                            result.signature.left_parameter_carrier.to_string(),
                        ),
                        string_field(
                            "right_parameter_carrier",
                            result.signature.right_parameter_carrier.to_string(),
                        ),
                        string_field(
                            "return_carrier",
                            result.signature.return_carrier.to_string(),
                        ),
                    ]),
                ),
                string_field(
                    "iterand_return_carrier",
                    result.iterand_return_carrier.to_string(),
                ),
                (
                    "seed_membership".to_string(),
                    self.wd_fact_check(&result.seed_membership),
                ),
                (
                    "operation_laws".to_string(),
                    result
                        .operation_laws
                        .as_ref()
                        .map(|laws| self.finite_reduce_operation_laws(laws))
                        .unwrap_or(JsonValue::Null),
                ),
                ("mode".to_string(), self.reduce_mode(&result.mode)),
            ]),
            SuccessVerifyBinderObjectWellDefinedResult::Structure(result) => object(vec![
                string_field("kind", "Structure"),
                string_field("structure_name", result.structure_name.clone()),
                (
                    "header_arguments".to_string(),
                    array(
                        result
                            .header_arguments
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
                    "header_domains".to_string(),
                    array(
                        result
                            .header_domains
                            .iter()
                            .map(|check| self.wd_fact_check(check))
                            .collect(),
                    ),
                ),
                (
                    "fields".to_string(),
                    array(
                        result
                            .fields
                            .iter()
                            .map(|field| {
                                object(vec![
                                    number_field("field_index", field.field_index),
                                    string_field("field_name", field.field_name.clone()),
                                    ("carrier".to_string(), self.wd_child_result(&field.carrier)),
                                    (
                                        "premise".to_string(),
                                        self.wd_binder_premise_result(&field.premise),
                                    ),
                                ])
                            })
                            .collect(),
                    ),
                ),
                (
                    "equivalent_facts".to_string(),
                    array(
                        result
                            .equivalent_facts
                            .iter()
                            .map(|fact| {
                                object(vec![
                                    number_field("fact_index", fact.fact_index),
                                    string_field("proposition", fact.proposition.to_string()),
                                    (
                                        "well_definedness".to_string(),
                                        self.fact_well_definedness(&fact.well_definedness),
                                    ),
                                    ("store".to_string(), self.store_fact(&fact.store)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
        }
    }

    fn wd_fact_check(&mut self, check: &SuccessVerifyFactForObjWellDefinedResult) -> JsonValue {
        object(vec![
            string_field(
                "expected_proposition",
                check.expected_proposition.to_string(),
            ),
            (
                "verification".to_string(),
                self.shared_fact(&check.verification),
            ),
        ])
    }

    fn finite_reduce_operation_laws(
        &mut self,
        result: &SuccessVerifyFiniteReduceOperationLawsResult,
    ) -> JsonValue {
        object(vec![
            (
                "parameter_carrier".to_string(),
                self.wd_child_result(&result.parameter_carrier),
            ),
            (
                "parameters".to_string(),
                array(
                    result
                        .parameters
                        .iter()
                        .map(|premise| self.wd_binder_premise_result(premise))
                        .collect(),
                ),
            ),
            (
                "associativity".to_string(),
                self.wd_fact_check(&result.associativity),
            ),
            (
                "commutativity".to_string(),
                self.wd_fact_check(&result.commutativity),
            ),
        ])
    }

    fn reduce_mode(&mut self, result: &SuccessVerifyReduceModeResult) -> JsonValue {
        match result {
            SuccessVerifyReduceModeResult::Empty(result) => object(vec![
                string_field("kind", "Empty"),
                (
                    "empty_range_or_set".to_string(),
                    self.wd_fact_check(&result.empty_range_or_set),
                ),
            ]),
            SuccessVerifyReduceModeResult::Interval(result) => object(vec![
                string_field("kind", "Interval"),
                (
                    "interval".to_string(),
                    self.iteration_interval(&result.interval),
                ),
            ]),
            SuccessVerifyReduceModeResult::Elements(result) => object(vec![
                string_field("kind", "Elements"),
                (
                    "body_memberships".to_string(),
                    array(
                        result
                            .body_memberships
                            .iter()
                            .map(|check| self.wd_fact_check(check))
                            .collect(),
                    ),
                ),
                (
                    "applications".to_string(),
                    array(
                        result
                            .applications
                            .iter()
                            .map(|application| self.wd_child_result(application))
                            .collect(),
                    ),
                ),
            ]),
            SuccessVerifyReduceModeResult::Symbolic(result) => object(vec![
                string_field("kind", "Symbolic"),
                (
                    "coverage".to_string(),
                    match &result.coverage {
                        SuccessVerifyFiniteReduceDomainCoverageResult::Exact(result) => {
                            object(vec![
                                string_field("kind", "Exact"),
                                string_field("aggregate_set", result.aggregate_set.to_string()),
                                string_field("iterand_domain", result.iterand_domain.to_string()),
                            ])
                        }
                        SuccessVerifyFiniteReduceDomainCoverageResult::Subset(result) => {
                            object(vec![
                                string_field("kind", "Subset"),
                                string_field("aggregate_set", result.aggregate_set.to_string()),
                                string_field("iterand_domain", result.iterand_domain.to_string()),
                                ("proof".to_string(), self.wd_fact_check(&result.subset)),
                            ])
                        }
                    },
                ),
            ]),
        }
    }

    fn finite_aggregate_mode(
        &mut self,
        result: &SuccessVerifyFiniteAggregateModeResult,
    ) -> JsonValue {
        let fact_check =
            |serializer: &mut Self, check: &SuccessVerifyFactForObjWellDefinedResult| {
                object(vec![
                    string_field(
                        "expected_proposition",
                        check.expected_proposition.to_string(),
                    ),
                    (
                        "verification".to_string(),
                        serializer.shared_fact(&check.verification),
                    ),
                ])
            };
        match result {
            SuccessVerifyFiniteAggregateModeResult::Empty(result) => object(vec![
                string_field("kind", "Empty"),
                ("empty_set".to_string(), fact_check(self, &result.empty_set)),
            ]),
            SuccessVerifyFiniteAggregateModeResult::Elements(result) => object(vec![
                string_field("kind", "Elements"),
                (
                    "body_memberships".to_string(),
                    array(
                        result
                            .body_memberships
                            .iter()
                            .map(|check| fact_check(self, check))
                            .collect(),
                    ),
                ),
                (
                    "applications".to_string(),
                    array(
                        result
                            .applications
                            .iter()
                            .map(|application| self.wd_child_result(application))
                            .collect(),
                    ),
                ),
            ]),
            SuccessVerifyFiniteAggregateModeResult::ClosedRange(result) => object(vec![
                string_field("kind", "ClosedRange"),
                (
                    "aggregate_dependency".to_string(),
                    self.wd_child_result(&result.aggregate_dependency),
                ),
            ]),
            SuccessVerifyFiniteAggregateModeResult::Symbolic(result) => object(vec![
                string_field("kind", "Symbolic"),
                string_field("exact_domain", result.exact_domain.to_string()),
            ]),
        }
    }

    fn iteration_scalar_return(
        &mut self,
        result: &SuccessVerifyIterationScalarReturnResult,
    ) -> JsonValue {
        object(vec![
            (
                "parameter_carriers".to_string(),
                array(
                    result
                        .parameter_carriers
                        .iter()
                        .map(|child| self.wd_child_result(child))
                        .collect(),
                ),
            ),
            (
                "parameters".to_string(),
                array(
                    result
                        .parameters
                        .iter()
                        .map(|premise| self.wd_binder_premise_result(premise))
                        .collect(),
                ),
            ),
            (
                "domains".to_string(),
                array(
                    result
                        .domains
                        .iter()
                        .map(|premise| self.wd_binder_premise_result(premise))
                        .collect(),
                ),
            ),
            (
                "return_carrier".to_string(),
                self.wd_child_result(&result.return_carrier),
            ),
            (
                "return_subset".to_string(),
                object(vec![
                    string_field(
                        "expected_proposition",
                        result.return_subset.expected_proposition.to_string(),
                    ),
                    (
                        "verification".to_string(),
                        self.shared_fact(&result.return_subset.verification),
                    ),
                ]),
            ),
        ])
    }

    fn iteration_interval(&mut self, result: &SuccessVerifyIterationIntervalResult) -> JsonValue {
        object(vec![
            string_field("parameter_set", result.parameter_set.to_string()),
            (
                "coverage".to_string(),
                self.iteration_coverage(&result.coverage),
            ),
            (
                "parameter_carriers".to_string(),
                array(
                    result
                        .parameter_carriers
                        .iter()
                        .map(|child| self.wd_child_result(child))
                        .collect(),
                ),
            ),
            (
                "parameters".to_string(),
                array(
                    result
                        .parameters
                        .iter()
                        .map(|premise| self.wd_binder_premise_result(premise))
                        .collect(),
                ),
            ),
            (
                "lower_bound".to_string(),
                self.store_fact(&result.lower_bound),
            ),
            (
                "upper_bound".to_string(),
                self.store_fact(&result.upper_bound),
            ),
            (
                "domains".to_string(),
                array(
                    result
                        .domains
                        .iter()
                        .map(|domain| {
                            object(vec![
                                string_field("proposition", domain.proposition.to_string()),
                                (
                                    "verification".to_string(),
                                    self.shared_fact(&domain.verification),
                                ),
                                ("store".to_string(), self.store_fact(&domain.store)),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "return_carrier".to_string(),
                self.wd_child_result(&result.return_carrier),
            ),
            (
                "body".to_string(),
                result
                    .body
                    .as_ref()
                    .map(|body| self.wd_child_result(body))
                    .unwrap_or(JsonValue::Null),
            ),
            (
                "body_membership".to_string(),
                result
                    .body_membership
                    .as_ref()
                    .map(|membership| {
                        object(vec![
                            ("role".to_string(), wd_requirement_role(membership.role)),
                            string_field(
                                "expected_proposition",
                                membership.expected_proposition.to_string(),
                            ),
                            (
                                "verification".to_string(),
                                self.shared_fact(&membership.verification),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null),
            ),
        ])
    }

    fn iteration_coverage(&mut self, result: &SuccessVerifyIterationCoverageResult) -> JsonValue {
        let fact_check =
            |serializer: &mut Self, check: &SuccessVerifyFactForObjWellDefinedResult| {
                object(vec![
                    string_field(
                        "expected_proposition",
                        check.expected_proposition.to_string(),
                    ),
                    (
                        "verification".to_string(),
                        serializer.shared_fact(&check.verification),
                    ),
                ])
            };
        match result {
            SuccessVerifyIterationCoverageResult::UniversalIntegerCarrier(result) => object(vec![
                string_field("kind", "UniversalIntegerCarrier"),
                string_field("parameter_set", result.parameter_set.to_string()),
            ]),
            SuccessVerifyIterationCoverageResult::Enumerated(result) => object(vec![
                string_field("kind", "Enumerated"),
                (
                    "checks".to_string(),
                    array(
                        result
                            .checks
                            .iter()
                            .map(|check| fact_check(self, check))
                            .collect(),
                    ),
                ),
            ]),
            SuccessVerifyIterationCoverageResult::Endpoint(result) => object(vec![
                string_field("kind", "Endpoint"),
                ("check".to_string(), fact_check(self, &result.check)),
            ]),
            SuccessVerifyIterationCoverageResult::IntervalSubset(result) => object(vec![
                string_field("kind", "IntervalSubset"),
                ("check".to_string(), fact_check(self, &result.check)),
            ]),
        }
    }

    fn wd_child_result(&mut self, child: &SuccessVerifyChildObjWellDefinedResult) -> JsonValue {
        object(vec![
            ("role".to_string(), wd_child_role_value(child.role)),
            string_field("object", child.source_object.to_string()),
            ("result".to_string(), self.shared_wd_obj(&child.result)),
        ])
    }

    fn wd_binder_premise_result(&mut self, result: &SuccessVerifyBinderPremiseResult) -> JsonValue {
        object(vec![
            ("role".to_string(), wd_binder_premise_role(result.role)),
            optional_symbol_id_field("symbol_id", result.symbol_id),
            string_field("proposition", result.proposition.to_string()),
            (
                "well_definedness".to_string(),
                self.fact_well_definedness(&result.well_definedness),
            ),
            ("infers".to_string(), infer_result_value(&result.infers)),
        ])
    }

    fn verify_fact(&mut self, result: &SuccessVerifyFactResult) -> JsonValue {
        object(vec![
            string_field("kind", verify_fact_kind(result)),
            string_field("statement", result.fact().to_string()),
            ("proof".to_string(), self.fact_proof(result.proof())),
        ])
    }

    fn fact_proof(&mut self, proof: &SuccessFactProofResult) -> JsonValue {
        match proof {
            SuccessFactProofResult::BuiltinRule(result) => {
                self.builtin_proof("BuiltinRule", result)
            }
            SuccessFactProofResult::BuiltinStrategy(result) => {
                self.builtin_proof("BuiltinStrategy", result)
            }
            SuccessFactProofResult::Fact(result) => object(vec![
                string_field("kind", "FactCitation"),
                optional_string_field("detail", result.detail.as_deref()),
                string_field("cited_statement", result.cite_what.to_string()),
                optional_fact_id_field("source_fact_id", result.source_fact_id),
                (
                    "equality_transport".to_string(),
                    equality_transport_value(result.equality_transport.as_ref()),
                ),
                (
                    "fact_transformation".to_string(),
                    fact_transformation_value(result.fact_transformation.as_ref()),
                ),
            ]),
            SuccessFactProofResult::KnownForallInstantiation(result) => self.known_forall(result),
            SuccessFactProofResult::CombinedProofs(result) => object(vec![
                string_field("kind", "CombinedProofs"),
                (
                    "proofs".to_string(),
                    array(
                        result
                            .cite_what
                            .iter()
                            .map(|proof| self.combined_fact_proof(proof))
                            .collect(),
                    ),
                ),
            ]),
            SuccessFactProofResult::ForallProof(result) => object(vec![
                string_field("kind", "ForallProof"),
                string_field("forall_fact", result.forall_fact.to_string()),
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

    fn builtin_proof(&mut self, kind: &str, result: &SuccessBuiltinFactProofResult) -> JsonValue {
        object(vec![
            string_field("kind", kind),
            string_field("diagnostic_label", result.msg.clone()),
            (
                "evidence".to_string(),
                result
                    .evidence
                    .as_ref()
                    .map(|evidence| self.builtin_evidence(evidence))
                    .unwrap_or(JsonValue::Null),
            ),
            (
                "subgoals".to_string(),
                array(
                    result
                        .subgoals
                        .iter()
                        .map(|result| self.stmt_result(result))
                        .collect(),
                ),
            ),
        ])
    }

    fn combined_fact_proof(&mut self, proof: &SuccessCombinedFactProofItemResult) -> JsonValue {
        match proof {
            SuccessCombinedFactProofItemResult::ByBuiltinRule(result)
            | SuccessCombinedFactProofItemResult::ByBuiltinStrategy(result) => object(vec![
                string_field(
                    "kind",
                    if matches!(proof, SuccessCombinedFactProofItemResult::ByBuiltinRule(_)) {
                        "BuiltinRule"
                    } else {
                        "BuiltinStrategy"
                    },
                ),
                string_field("statement", result.verify_what.to_string()),
                string_field("diagnostic_label", result.msg.clone()),
                (
                    "evidence".to_string(),
                    result
                        .evidence
                        .as_ref()
                        .map(|evidence| self.builtin_evidence(evidence))
                        .unwrap_or(JsonValue::Null),
                ),
                (
                    "subgoals".to_string(),
                    array(
                        result
                            .subgoals
                            .iter()
                            .map(|result| self.stmt_result(result))
                            .collect(),
                    ),
                ),
            ]),
            SuccessCombinedFactProofItemResult::ByFact(result) => object(vec![
                string_field("kind", "FactCitation"),
                string_field("statement", result.verify_what.to_string()),
                string_field("cited_statement", result.cite_what.to_string()),
                optional_fact_id_field("source_fact_id", result.source_fact_id),
            ]),
            SuccessCombinedFactProofItemResult::ByKnownForall(result) => object(vec![
                string_field("kind", "KnownForallInstantiation"),
                string_field("statement", result.verify_what.to_string()),
                ("result".to_string(), self.known_forall(&result.result)),
            ]),
            SuccessCombinedFactProofItemResult::Reuse(result) => object(vec![
                string_field("kind", "Reuse"),
                string_field("statement", result.statement.to_string()),
                ("source".to_string(), self.shared_fact(&result.source)),
            ]),
        }
    }

    fn known_forall(&mut self, result: &SuccessInstantiateKnownForallResult) -> JsonValue {
        object(vec![
            string_field("kind", "KnownForallInstantiation"),
            string_field("cited_statement", result.cite_what.to_string()),
            optional_fact_id_field("source_fact_id", result.source_fact_id),
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

    fn builtin_evidence(&mut self, evidence: &BuiltinRuleEvidence) -> JsonValue {
        match evidence {
            BuiltinRuleEvidence::RegisteredLocal(result) => object(vec![
                string_field("kind", "RegisteredLocal"),
                string_field("rule_id", result.rule_id.as_str()),
                string_field("semantic_fingerprint", result.semantic_fingerprint.as_hex()),
                ("bindings".to_string(), display_values(&result.bindings)),
                number_field(
                    "parameter_requirement_count",
                    result.parameter_requirement_count,
                ),
            ]),
            BuiltinRuleEvidence::DefinitionProjection(result) => object(vec![
                string_field("kind", "DefinitionProjection"),
                string_field("fact", result.fact.to_string()),
                string_field("definition", result.definition.to_string()),
            ]),
            BuiltinRuleEvidence::SetBuilderMembership(result) => object(vec![
                string_field("kind", "SetBuilderMembership"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "expected_premises".to_string(),
                    display_values(&result.expected_premises),
                ),
            ]),
            BuiltinRuleEvidence::FunctionSetMembership(result) => object(vec![
                string_field("kind", "FunctionSetMembership"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("expected_pointwise", result.expected_pointwise.to_string()),
            ]),
            BuiltinRuleEvidence::RefinedNumericMembership(result) => object(vec![
                string_field("kind", "RefinedNumericMembership"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "expected_premises".to_string(),
                    display_values(&result.expected_premises),
                ),
            ]),
            BuiltinRuleEvidence::ClosedNumericMembership(result) => object(vec![
                string_field("kind", "ClosedNumericMembership"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("target_set", result.target_set.to_string()),
                (
                    "evaluation".to_string(),
                    evaluation_value(&result.evaluation),
                ),
            ]),
            BuiltinRuleEvidence::ClosedNumericNonmembership(result) => object(vec![
                string_field("kind", "ClosedNumericNonmembership"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("target_set", result.target_set.to_string()),
                (
                    "evaluation".to_string(),
                    evaluation_value(&result.evaluation),
                ),
            ]),
            BuiltinRuleEvidence::ClosedNumericComparison(result) => object(vec![
                string_field("kind", "ClosedNumericComparison"),
                string_field("expected_target", result.expected_target.to_string()),
            ]),
            BuiltinRuleEvidence::ObjectReflexivity(result) => object(vec![
                string_field("kind", "ObjectReflexivity"),
                string_field("expected_target", result.expected_target.to_string()),
            ]),
            BuiltinRuleEvidence::RationalNormalization(result) => object(vec![
                string_field("kind", "RationalNormalization"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "left_evaluation".to_string(),
                    evaluation_value(&result.left_evaluation),
                ),
                (
                    "right_evaluation".to_string(),
                    evaluation_value(&result.right_evaluation),
                ),
            ]),
            BuiltinRuleEvidence::StandardSetNonempty(result) => object(vec![
                string_field("kind", "StandardSetNonempty"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("target_set", result.target_set.to_string()),
            ]),
            BuiltinRuleEvidence::DisjunctionIntroduction(result) => object(vec![
                string_field("kind", "DisjunctionIntroduction"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("expected_selected", result.expected_selected.to_string()),
                number_field("selected_index", result.selected_index),
            ]),
            BuiltinRuleEvidence::FunctionApplicationReturnMembership(result) => object(vec![
                string_field("kind", "FunctionApplicationReturnMembership"),
                string_field("typed_return_set", result.typed_return_set.to_string()),
                string_field("expected_target", result.expected_target.to_string()),
                string_field(
                    "expected_head_membership",
                    result.expected_head_membership.to_string(),
                ),
            ]),
            BuiltinRuleEvidence::MatrixExpressionMembership(result) => object(vec![
                string_field("kind", "MatrixExpressionMembership"),
                string_field(
                    "inferred_matrix_set",
                    Obj::from(result.inferred_matrix_set.clone()).to_string(),
                ),
                string_field("expected_target", result.expected_target.to_string()),
            ]),
            BuiltinRuleEvidence::KnownEqualityPath(result) => object(vec![
                string_field("kind", "KnownEqualityPath"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "steps".to_string(),
                    array(
                        result
                            .steps
                            .iter()
                            .map(|step| {
                                object(vec![
                                    string_field("from", step.from.to_string()),
                                    string_field("to", step.to.to_string()),
                                    string_field("equality", step.equality.to_string()),
                                    string_field("source_fact_id", fact_id(step.source_fact_id)),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ]),
            BuiltinRuleEvidence::DivNotEqualZero(result) => object(vec![
                string_field("kind", "DivNotEqualZero"),
                string_field("numerator", result.numerator.to_string()),
                string_field("denominator", result.denominator.to_string()),
                string_field(
                    "orientation",
                    match result.orientation {
                        NonzeroExpressionOrientation::ExpressionOnLeft => "ExpressionOnLeft",
                        NonzeroExpressionOrientation::ExpressionOnRight => "ExpressionOnRight",
                    },
                ),
            ]),
            BuiltinRuleEvidence::Arithmetic(rule) => {
                rule_evidence_value("Arithmetic", arithmetic_builtin_rule_name(*rule))
            }
            BuiltinRuleEvidence::IntegerMembershipClosure(rule) => rule_evidence_value(
                "IntegerMembershipClosure",
                integer_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::NaturalMembershipClosure(rule) => rule_evidence_value(
                "NaturalMembershipClosure",
                natural_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::RationalMembershipClosure(rule) => rule_evidence_value(
                "RationalMembershipClosure",
                rational_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule) => rule_evidence_value(
                "ComplexArithmeticMembershipClosure",
                complex_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule) => rule_evidence_value(
                "RealArithmeticMembershipClosure",
                real_membership_closure_rule_name(*rule),
            ),
            BuiltinRuleEvidence::NativeConstantMembership(rule) => rule_evidence_value(
                "NativeConstantMembership",
                native_constant_membership_rule_name(*rule),
            ),
            BuiltinRuleEvidence::NotEqualSymmetry => {
                object(vec![string_field("kind", "NotEqualSymmetry")])
            }
            BuiltinRuleEvidence::NotEqualFromStrictOrder => {
                object(vec![string_field("kind", "NotEqualFromStrictOrder")])
            }
            BuiltinRuleEvidence::SetRelationDuality(rule) => {
                rule_evidence_value("SetRelationDuality", set_relation_duality_rule_name(*rule))
            }
            BuiltinRuleEvidence::Set(rule) => {
                rule_evidence_value("Set", set_builtin_rule_name(*rule))
            }
            BuiltinRuleEvidence::FiniteSet(rule) => {
                rule_evidence_value("FiniteSet", finite_set_builtin_rule_name(*rule))
            }
            BuiltinRuleEvidence::ListSetMembership(result) => object(vec![
                string_field("kind", "ListSetMembership"),
                number_field("selected_index", result.selected_index),
            ]),
            BuiltinRuleEvidence::TupleLiteralShape => {
                object(vec![string_field("kind", "TupleLiteralShape")])
            }
            BuiltinRuleEvidence::AbsoluteValue(rule) => {
                rule_evidence_value("AbsoluteValue", absolute_value_builtin_rule_name(*rule))
            }
            BuiltinRuleEvidence::PrimeU64Reflection => {
                object(vec![string_field("kind", "PrimeU64Reflection")])
            }
            BuiltinRuleEvidence::CoprimeNaturalReflection => {
                object(vec![string_field("kind", "CoprimeNaturalReflection")])
            }
            BuiltinRuleEvidence::StandardSetMembershipProjection => object(vec![string_field(
                "kind",
                "StandardSetMembershipProjection",
            )]),
            BuiltinRuleEvidence::StandardSetSubset => {
                object(vec![string_field("kind", "StandardSetSubset")])
            }
        }
    }

    fn store_fact(&mut self, result: &SuccessStoreFactResult) -> JsonValue {
        success_store_fact_value(result)
    }

    fn by_cases_verification(&mut self, result: &SuccessVerifyByCasesResult) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyByCasesResult"),
            (
                "goal_well_definedness".to_string(),
                array(
                    result
                        .goal_well_definedness
                        .iter()
                        .map(|well_definedness| self.fact_well_definedness(well_definedness))
                        .collect(),
                ),
            ),
            (
                "coverage_check".to_string(),
                self.stmt_result(&result.coverage_check),
            ),
            ("then_facts".to_string(), display_values(&result.then_facts)),
            (
                "branches".to_string(),
                array(
                    result
                        .branches
                        .iter()
                        .map(|branch| self.by_case_branch(branch))
                        .collect(),
                ),
            ),
        ])
    }

    fn by_case_branch(&mut self, result: &SuccessVerifyByCaseBranchResult) -> JsonValue {
        let exit = match &result.exit {
            SuccessVerifyByCaseBranchExitResult::Conclusions(conclusions) => object(vec![
                string_field("kind", "SuccessVerifyByCaseConclusionsResult"),
                ("checks".to_string(), self.stmt_results(&conclusions.checks)),
            ]),
            SuccessVerifyByCaseBranchExitResult::Contradiction(contradiction) => object(vec![
                string_field("kind", "SuccessVerifyByCaseContradictionResult"),
                string_field("impossible_fact", contradiction.impossible_fact.to_string()),
                (
                    "contradiction".to_string(),
                    self.contradiction_verification(&contradiction.contradiction),
                ),
            ]),
        };
        object(vec![
            string_field("kind", "SuccessVerifyByCaseBranchResult"),
            string_field("assumption", result.assumption.to_string()),
            string_field("assumption_fact_id", fact_id(result.assumption_fact_id)),
            (
                "proof_scope".to_string(),
                self.local_proof_scope(&result.proof_scope),
            ),
            (
                "proof_steps".to_string(),
                self.stmt_results(&result.proof_steps),
            ),
            ("exit".to_string(), exit),
        ])
    }

    fn by_contra_verification(&mut self, result: &SuccessVerifyByContraResult) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyByContraResult"),
            string_field("to_prove", result.to_prove.to_string()),
            string_field("reverse_assumption", result.reverse_assumption.to_string()),
            string_field(
                "reverse_assumption_fact_id",
                fact_id(result.reverse_assumption_fact_id),
            ),
            (
                "proof_scope".to_string(),
                self.local_proof_scope(&result.proof_scope),
            ),
            (
                "proof_steps".to_string(),
                self.stmt_results(&result.proof_steps),
            ),
            string_field("impossible_fact", result.impossible_fact.to_string()),
            (
                "contradiction".to_string(),
                self.contradiction_verification(&result.contradiction),
            ),
        ])
    }

    fn contradiction_verification(
        &mut self,
        result: &SuccessVerifyContradictionResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyContradictionResult"),
            (
                "impossible_check".to_string(),
                self.stmt_result(&result.impossible_check),
            ),
            (
                "negated_impossible_check".to_string(),
                self.stmt_result(&result.negated_impossible_check),
            ),
        ])
    }

    fn local_proof_scope(&mut self, result: &SuccessVerifyLocalProofScopeResult) -> JsonValue {
        object(vec![
            (
                "assumption_infers".to_string(),
                infer_result_value(&result.assumption_infers),
            ),
            (
                "assumption_components".to_string(),
                array(
                    result
                        .assumption_components
                        .iter()
                        .map(|(id, fact)| {
                            object(vec![
                                string_field("fact_id", fact_id(*id)),
                                string_field("statement", fact.to_string()),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
    }

    fn witness_exist_verification(
        &mut self,
        result: &SuccessVerifyWitnessExistResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyWitnessExistResult"),
            (
                "proof_steps".to_string(),
                self.stmt_results(&result.proof_steps),
            ),
            (
                "parameter_checks".to_string(),
                array(
                    result
                        .parameter_checks
                        .iter()
                        .map(|result| {
                            result
                                .as_ref()
                                .map(|result| self.stmt_result(result))
                                .unwrap_or(JsonValue::Null)
                        })
                        .collect(),
                ),
            ),
            (
                "body_checks".to_string(),
                self.stmt_results(&result.body_checks),
            ),
            (
                "uniqueness_check".to_string(),
                result
                    .uniqueness_check
                    .as_ref()
                    .map(|result| self.stmt_result(result))
                    .unwrap_or(JsonValue::Null),
            ),
        ])
    }

    fn witness_atomic_verification(
        &mut self,
        result: &SuccessVerifyWitnessAtomicFactResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyWitnessAtomicFactResult"),
            string_field("definition", result.definition.to_string()),
            string_field(
                "instantiated_existential",
                result.instantiated_existential.to_string(),
            ),
            (
                "definition_parameter_verification".to_string(),
                args_satisfy_param_def_verification_value(
                    self,
                    &result.definition_parameter_verification,
                ),
            ),
            (
                "witness_verification".to_string(),
                self.witness_exist_verification(&result.witness_verification),
            ),
        ])
    }

    fn common(&mut self, common: &SuccessStmtCommonResult) -> JsonValue {
        object(vec![
            ("infers".to_string(), infer_result_value(&common.infers)),
            (
                "execution_trace".to_string(),
                optional_trace(common.execution_trace.as_ref()),
            ),
        ])
    }

    fn stmt_results(&mut self, results: &[StmtResult]) -> JsonValue {
        array(
            results
                .iter()
                .map(|result| self.stmt_result(result))
                .collect(),
        )
    }

    fn claim_verification(&mut self, result: &SuccessVerifyClaimResult) -> JsonValue {
        match result {
            SuccessVerifyClaimResult::Forall(result) => object(vec![
                string_field("kind", "SuccessVerifyClaimForallResult"),
                string_field("forall_fact", result.forall_fact.to_string()),
                (
                    "well_definedness".to_string(),
                    self.fact_well_definedness(&result.well_definedness),
                ),
                (
                    "proof_scope".to_string(),
                    self.local_proof_scope(&result.proof_scope),
                ),
                (
                    "proof_steps".to_string(),
                    self.stmt_results(&result.proof_steps),
                ),
                (
                    "conclusion_checks".to_string(),
                    self.stmt_results(&result.conclusion_checks),
                ),
            ]),
            SuccessVerifyClaimResult::Fact(result) => object(vec![
                string_field("kind", "SuccessVerifyClaimFactResult"),
                string_field("fact", result.fact.to_string()),
                (
                    "well_definedness".to_string(),
                    self.fact_well_definedness(&result.well_definedness),
                ),
                (
                    "proof_scope".to_string(),
                    self.local_proof_scope(&result.proof_scope),
                ),
                (
                    "proof_steps".to_string(),
                    self.stmt_results(&result.proof_steps),
                ),
                (
                    "conclusion_check".to_string(),
                    self.stmt_result(&result.conclusion_check),
                ),
            ]),
        }
    }

    fn theorem_verification(&mut self, result: &SuccessVerifyTheoremResult) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyTheoremResult"),
            string_field("name", result.name.clone()),
            string_field("forall_fact", result.forall_fact.to_string()),
            (
                "well_definedness".to_string(),
                self.fact_well_definedness(&result.well_definedness),
            ),
            (
                "proof_scope".to_string(),
                self.local_proof_scope(&result.proof_scope),
            ),
            (
                "proof_steps".to_string(),
                self.stmt_results(&result.proof_steps),
            ),
            (
                "conclusion_checks".to_string(),
                self.stmt_results(&result.conclusion_checks),
            ),
        ])
    }

    fn shared_fact(&mut self, result: &Rc<SuccessVerifyFactResult>) -> JsonValue {
        let pointer = Rc::as_ptr(result) as usize;
        if let Some(id) = self.shared_fact_ids.get(&pointer) {
            return object(vec![string_field("$ref", id.clone())]);
        }
        let id = format!("proof-node-{}", self.next_shared_fact_id);
        self.next_shared_fact_id += 1;
        self.shared_fact_ids.insert(pointer, id.clone());
        object(vec![
            string_field("$id", id),
            ("value".to_string(), self.verify_fact(result)),
        ])
    }

    fn unknown_stmt(&mut self, unknown: &UnknownStmtResult) -> JsonValue {
        match unknown {
            UnknownStmtResult::Generic(result) => object(vec![
                string_field("kind", "Generic"),
                (
                    "detail".to_string(),
                    optional_strings(result.detail.as_ref()),
                ),
            ]),
            UnknownStmtResult::Fact(result) => object(vec![
                string_field("kind", unknown_fact_kind(result)),
                string_field("goal", result.goal().to_string()),
                ("detail".to_string(), optional_strings(result.detail())),
            ]),
        }
    }
}

fn verify_fact_kind(result: &SuccessVerifyFactResult) -> &'static str {
    match result {
        SuccessVerifyFactResult::AtomicFact(_) => "AtomicFact",
        SuccessVerifyFactResult::ExistFact(_) => "ExistFact",
        SuccessVerifyFactResult::OrFact(_) => "OrFact",
        SuccessVerifyFactResult::AndFact(_) => "AndFact",
        SuccessVerifyFactResult::ChainFact(_) => "ChainFact",
        SuccessVerifyFactResult::ForallFact(_) => "ForallFact",
        SuccessVerifyFactResult::ForallFactWithIff(_) => "ForallFactWithIff",
        SuccessVerifyFactResult::NotForallFact(_) => "NotForallFact",
    }
}

fn unknown_fact_kind(result: &UnknownFactResult) -> &'static str {
    match result {
        UnknownFactResult::AtomicFact(_) => "AtomicFact",
        UnknownFactResult::ExistFact(_) => "ExistFact",
        UnknownFactResult::OrFact(_) => "OrFact",
        UnknownFactResult::AndFact(_) => "AndFact",
        UnknownFactResult::ChainFact(_) => "ChainFact",
        UnknownFactResult::ForallFact(_) => "ForallFact",
        UnknownFactResult::ForallFactWithIff(_) => "ForallFactWithIff",
        UnknownFactResult::NotForall(_) => "NotForallFact",
    }
}

fn function_definition_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyFunctionDefinitionResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyFunctionDefinitionResult"),
        (
            "return_check".to_string(),
            renderer.stmt_result(&result.return_check),
        ),
        (
            "assumption_infers".to_string(),
            infer_result_value(&result.assumption_infers),
        ),
        string_field(
            "function_membership",
            result.function_membership.to_string(),
        ),
        string_field("defining_equality", result.defining_equality.to_string()),
    ])
}

fn by_assignment_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByAssignmentResult,
) -> JsonValue {
    object(vec![
        ("assignment".to_string(), string_pairs(&result.assignment)),
        ("assumptions".to_string(), string_pairs(&result.assumptions)),
        (
            "domain_checks".to_string(),
            array(
                result
                    .domain_checks
                    .iter()
                    .map(|domain| {
                        object(vec![
                            string_field("fact", domain.fact.to_string()),
                            ("check".to_string(), renderer.stmt_result(&domain.check)),
                            (
                                "negated_check".to_string(),
                                domain
                                    .negated_check
                                    .as_ref()
                                    .map(|check| renderer.stmt_result(check))
                                    .unwrap_or(JsonValue::Null),
                            ),
                            ("satisfied".to_string(), JsonValue::Bool(domain.satisfied)),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "conclusion_checks".to_string(),
            renderer.stmt_results(&result.conclusion_checks),
        ),
    ])
}

fn by_enumerate_finite_set_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByEnumerateFiniteSetResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByEnumerateFiniteSetResult"),
        ("parameters".to_string(), strings(&result.parameters)),
        (
            "parameter_sets".to_string(),
            strings(&result.parameter_sets),
        ),
        string_field("prove_goal", result.prove_goal.clone()),
        (
            "assignments".to_string(),
            array(
                result
                    .assignments
                    .iter()
                    .map(|assignment| by_assignment_verification_value(renderer, assignment))
                    .collect(),
            ),
        ),
        string_field("generated_forall", result.generated_forall.clone()),
    ])
}

fn by_for_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByForResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByForResult"),
        string_field("iteration_mode", result.iteration_mode.clone()),
        ("parameters".to_string(), strings(&result.parameters)),
        ("domains".to_string(), strings(&result.domains)),
        string_field("prove_goal", result.prove_goal.clone()),
        (
            "assignments".to_string(),
            array(
                result
                    .assignments
                    .iter()
                    .map(|assignment| by_assignment_verification_value(renderer, assignment))
                    .collect(),
            ),
        ),
        string_field("generated_forall", result.generated_forall.clone()),
    ])
}

fn by_enumerate_range_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByEnumerateRangeResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByEnumerateRangeResult"),
        string_field("proof_type", result.proof_type.clone()),
        string_field("element", result.element.clone()),
        string_field("range", result.range.clone()),
        string_field("membership_fact", result.membership_fact.clone()),
        (
            "endpoint_facts".to_string(),
            strings(&result.endpoint_facts),
        ),
        string_field("generated_cases", result.generated_cases.clone()),
        (
            "membership_check".to_string(),
            renderer.stmt_result(&result.membership_check),
        ),
        (
            "endpoint_checks".to_string(),
            renderer.stmt_results(&result.endpoint_checks),
        ),
    ])
}

fn by_induc_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByInducResult,
) -> JsonValue {
    let proof = match &result.proof {
        SuccessVerifyByInducProofResult::IntegerUnstructured(proof) => object(vec![
            string_field("kind", "IntegerUnstructured"),
            ("strong".to_string(), JsonValue::Bool(proof.strong)),
            string_field("start", proof.start.clone()),
            (
                "base_assumptions".to_string(),
                string_pairs(&proof.base_assumptions),
            ),
            (
                "step_assumptions".to_string(),
                string_pairs(&proof.step_assumptions),
            ),
            (
                "proof_steps".to_string(),
                renderer.stmt_results(&proof.proof_steps),
            ),
            (
                "goals".to_string(),
                array(
                    proof
                        .goals
                        .iter()
                        .map(|goal| by_induc_goal_value(renderer, goal))
                        .collect(),
                ),
            ),
        ]),
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => object(vec![
            string_field("kind", "IntegerStructured"),
            ("strong".to_string(), JsonValue::Bool(proof.strong)),
            string_field("start", proof.start.clone()),
            (
                "start_in_z_check".to_string(),
                renderer.stmt_result(&proof.start_in_z_check),
            ),
            (
                "base".to_string(),
                by_induc_case_value(renderer, &proof.base),
            ),
            (
                "step".to_string(),
                by_induc_case_value(renderer, &proof.step),
            ),
        ]),
        SuccessVerifyByInducProofResult::FiniteSet(proof) => object(vec![
            string_field("kind", "FiniteSet"),
            (
                "base".to_string(),
                by_induc_case_value(renderer, &proof.base),
            ),
            (
                "step".to_string(),
                by_induc_case_value(renderer, &proof.step),
            ),
        ]),
    };
    object(vec![
        string_field("kind", "SuccessVerifyByInducResult"),
        string_field("parameter", result.parameter.clone()),
        ("prove_goals".to_string(), strings(&result.prove_goals)),
        string_field("generated_forall", result.generated_forall.clone()),
        ("proof".to_string(), proof),
    ])
}

fn by_induc_goal_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByInducGoalResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByInducGoalResult"),
        string_field("source_goal", result.source_goal.to_string()),
        (
            "base_check".to_string(),
            renderer.stmt_result(&result.base_check),
        ),
        (
            "start_in_z_check".to_string(),
            renderer.stmt_result(&result.start_in_z_check),
        ),
        (
            "step_check".to_string(),
            renderer.stmt_result(&result.step_check),
        ),
        ("infers".to_string(), infer_result_value(&result.infers)),
    ])
}

fn by_induc_case_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByInducCaseResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByInducCaseResult"),
        ("assumptions".to_string(), string_pairs(&result.assumptions)),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "conclusion_checks".to_string(),
            renderer.stmt_results(&result.conclusion_checks),
        ),
    ])
}

fn by_extension_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByExtensionResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByExtensionResult"),
        string_field("left", result.left.clone()),
        string_field("right", result.right.clone()),
        string_field("prove_goal", result.prove_goal.clone()),
        string_field("left_to_right_subset", result.left_to_right_subset.clone()),
        string_field("right_to_left_subset", result.right_to_left_subset.clone()),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "left_to_right_check".to_string(),
            renderer.stmt_result(&result.left_to_right_check),
        ),
        (
            "right_to_left_check".to_string(),
            renderer.stmt_result(&result.right_to_left_check),
        ),
    ])
}

fn prop_registration_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByPropRegistrationResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByPropRegistrationResult"),
        string_field("registration_type", result.registration_type.clone()),
        string_field("prop_name", result.prop_name.clone()),
        string_field("forall_fact", result.forall_fact.to_string()),
        (
            "assumption_infers".to_string(),
            infer_result_value(&result.assumption_infers),
        ),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "conclusion_check".to_string(),
            renderer.stmt_result(&result.conclusion_check),
        ),
    ])
}

fn optional_prop_registration(
    renderer: &mut StmtResultJsonV2,
    result: Option<&SuccessVerifyByPropRegistrationResult>,
) -> JsonValue {
    result
        .map(|result| prop_registration_verification_value(renderer, result))
        .unwrap_or(JsonValue::Null)
}

fn by_choice_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByChoiceResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByChoiceResult"),
        string_field("proof_type", result.proof_type.clone()),
        string_field("target", result.target.clone()),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "obligations".to_string(),
            array(
                result
                    .obligations
                    .iter()
                    .map(|obligation| {
                        object(vec![
                            string_field("role", obligation.role.clone()),
                            string_field("statement", obligation.fact.clone()),
                            (
                                "check".to_string(),
                                obligation
                                    .check
                                    .as_ref()
                                    .map(|check| renderer.stmt_result(check))
                                    .unwrap_or(JsonValue::Null),
                            ),
                        ])
                    })
                    .collect(),
            ),
        ),
        string_field("trusted_conclusion", result.trusted_conclusion.clone()),
    ])
}

fn optional_choice_verification(
    renderer: &mut StmtResultJsonV2,
    result: Option<&SuccessVerifyByChoiceResult>,
) -> JsonValue {
    result
        .map(|result| by_choice_verification_value(renderer, result))
        .unwrap_or(JsonValue::Null)
}

fn by_theorem_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByTheoremResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByTheoremResult"),
        string_field("theorem", result.theorem.clone()),
        string_field("theorem_source", result.theorem_source.clone()),
        optional_fact_id_field("source_fact_id", result.source_fact_id),
        string_field("mode", result.mode.clone()),
        ("arguments".to_string(), strings(&result.arguments)),
        ("domain_facts".to_string(), strings(&result.domain_facts)),
        (
            "requirement_roles".to_string(),
            strings(&result.requirement_roles),
        ),
        (
            "direct_conclusions".to_string(),
            display_values(&result.direct_conclusions),
        ),
        (
            "stored_then_facts".to_string(),
            strings(&result.stored_then_facts),
        ),
        (
            "temporary_then_facts".to_string(),
            strings(&result.temporary_then_facts),
        ),
        optional_string_field("selected_fact", result.selected_fact.as_deref()),
        (
            "parent_stored_facts".to_string(),
            strings(&result.parent_stored_facts),
        ),
        optional_string_field("provenance", result.provenance.as_deref()),
        (
            "argument_verification".to_string(),
            result
                .argument_verification
                .as_ref()
                .map(|verification| {
                    args_satisfy_param_def_verification_value(renderer, verification)
                })
                .unwrap_or(JsonValue::Null),
        ),
        (
            "requirement_checks".to_string(),
            renderer.stmt_results(&result.requirement_checks),
        ),
        (
            "domain_checks".to_string(),
            renderer.stmt_results(&result.domain_checks),
        ),
        (
            "selected_fact_check".to_string(),
            result
                .selected_fact_check
                .as_ref()
                .map(|check| renderer.stmt_result(check))
                .unwrap_or(JsonValue::Null),
        ),
    ])
}

fn by_definition_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByDefinitionResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByDefinitionResult"),
        string_field("prop", result.prop.clone()),
        optional_string_field(
            "definition",
            result
                .definition
                .as_ref()
                .map(ToString::to_string)
                .as_deref(),
        ),
        ("arguments".to_string(), strings(&result.arguments)),
        (
            "definition_clauses".to_string(),
            strings(&result.definition_clauses),
        ),
        string_field("stored_fact", result.stored_fact.clone()),
        (
            "concrete_user_prop".to_string(),
            JsonValue::Bool(result.concrete_user_prop),
        ),
        (
            "definition_clause_facts".to_string(),
            display_values(&result.definition_clause_facts),
        ),
        (
            "argument_verification".to_string(),
            result
                .argument_verification
                .as_ref()
                .map(|verification| {
                    args_satisfy_param_def_verification_value(renderer, verification)
                })
                .unwrap_or(JsonValue::Null),
        ),
        (
            "clause_checks".to_string(),
            renderer.stmt_results(&result.clause_checks),
        ),
    ])
}

fn args_satisfy_param_def_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyArgsSatisfyParamDefResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyArgsSatisfyParamDefResult"),
        ("checks".to_string(), renderer.stmt_results(&result.checks)),
        ("infers".to_string(), infer_result_value(&result.infers)),
    ])
}

fn object_choice_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyObjectChoiceResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyObjectChoiceResult"),
        (
            "groups".to_string(),
            array(
                result
                    .groups
                    .iter()
                    .map(|group| {
                        object(vec![
                            (
                                "selected_type_facts".to_string(),
                                display_values(&group.selected_type_facts),
                            ),
                            (
                                "nonempty_check".to_string(),
                                group
                                    .nonempty_check
                                    .as_ref()
                                    .map(|check| renderer.stmt_result(check))
                                    .unwrap_or(JsonValue::Null),
                            ),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

fn existential_elimination_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyExistentialEliminationResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyExistentialEliminationResult"),
        (
            "source_result".to_string(),
            renderer.stmt_result(&result.source_result),
        ),
        string_field("source_exist_fact", result.source_exist_fact.to_string()),
        (
            "witness_type_facts".to_string(),
            display_values(&result.witness_type_facts),
        ),
        (
            "instantiated_body_facts".to_string(),
            display_values(&result.instantiated_body_facts),
        ),
        (
            "includes_uniqueness".to_string(),
            JsonValue::Bool(result.includes_uniqueness),
        ),
    ])
}

fn optional_existential_elimination(
    renderer: &mut StmtResultJsonV2,
    result: Option<&SuccessVerifyExistentialEliminationResult>,
) -> JsonValue {
    result
        .map(|result| existential_elimination_value(renderer, result))
        .unwrap_or(JsonValue::Null)
}

fn infer_result_value(result: &SuccessInferResult) -> JsonValue {
    object(vec![
        (
            "stores".to_string(),
            array(
                result
                    .store_fact_outputs
                    .iter()
                    .map(store_fact_output_value)
                    .collect(),
            ),
        ),
        (
            "rule_applications".to_string(),
            array(
                result
                    .rule_applications
                    .iter()
                    .map(infer_rule_application_value)
                    .collect(),
            ),
        ),
    ])
}

fn infer_rule_application_value(result: &SuccessInferRuleApplicationResult) -> JsonValue {
    object(vec![
        string_field(
            "rule",
            match result.rule {
                InferRule::NaturalMembershipImpliesNonnegative => {
                    "NaturalMembershipImpliesNonnegative"
                }
            },
        ),
        (
            "premises".to_string(),
            array(
                result
                    .premises
                    .iter()
                    .map(|premise| {
                        object(vec![
                            string_field("statement", premise.fact.to_string()),
                            optional_fact_id_field("fact_id", premise.fact_id),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "conclusions".to_string(),
            array(
                result
                    .conclusions
                    .iter()
                    .map(success_store_fact_value)
                    .collect(),
            ),
        ),
    ])
}

fn success_store_fact_value(result: &SuccessStoreFactResult) -> JsonValue {
    object(vec![
        string_field("fact", result.fact.to_string()),
        optional_fact_id_field("fact_id", result.fact_id),
        ("infers".to_string(), infer_result_value(&result.infers)),
    ])
}

fn store_fact_output_value(store: &SuccessStoreFactOutput) -> JsonValue {
    object(vec![
        optional_fact_id_field("fact_id", store.fact_id),
        string_field(
            "statement",
            store.itself_and_why_itself_is_stored.0.to_string(),
        ),
        string_field("reason", store.itself_and_why_itself_is_stored.1.clone()),
        (
            "inferred_facts".to_string(),
            array(
                store
                    .inferred_facts
                    .iter()
                    .zip(store.inferred_fact_ids.iter())
                    .map(|(fact, id)| {
                        object(vec![
                            optional_fact_id_field("fact_id", *id),
                            string_field("statement", fact.to_string()),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

fn evaluation_value(result: &SuccessEvaluateObjResult) -> JsonValue {
    let step = match &result.step {
        SuccessEvaluateObjStepResult::Literal(literal) => object(vec![
            string_field("kind", "Literal"),
            string_field("literal", literal.literal.to_string()),
        ]),
        SuccessEvaluateObjStepResult::Unary(unary) => object(vec![
            string_field("kind", "Unary"),
            string_field("operator", unary_operator(unary.operator)),
            ("argument".to_string(), evaluation_value(&unary.argument)),
        ]),
        SuccessEvaluateObjStepResult::Binary(binary) => object(vec![
            string_field("kind", "Binary"),
            string_field("operator", binary_operator(binary.operator)),
            ("left".to_string(), evaluation_value(&binary.left)),
            ("right".to_string(), evaluation_value(&binary.right)),
        ]),
        SuccessEvaluateObjStepResult::Shape(shape) => object(vec![
            string_field("kind", "Shape"),
            string_field("operator", shape_operator(shape.operator)),
            (
                "inputs".to_string(),
                array(
                    shape
                        .inputs
                        .iter()
                        .map(|input| string(input.to_string()))
                        .collect(),
                ),
            ),
            (
                "evaluated_children".to_string(),
                array(
                    shape
                        .evaluated_children
                        .iter()
                        .map(evaluation_value)
                        .collect(),
                ),
            ),
        ]),
    };
    object(vec![
        string_field("expression", result.expression.to_string()),
        string_field("value", result.value.to_string()),
        ("step".to_string(), step),
    ])
}

fn optional_trace(trace: Option<&StatementExecutionTrace>) -> JsonValue {
    trace
        .map(|trace| {
            object(vec![
                (
                    "verify_well_definedness".to_string(),
                    phase_trace_value(&trace.verify_well_definedness),
                ),
                (
                    "verify_process".to_string(),
                    phase_trace_value(&trace.verify_process),
                ),
                (
                    "affect_environment".to_string(),
                    phase_trace_value(&trace.affect_environment),
                ),
                optional_string_field("verification_status", trace.verification_status.as_deref()),
            ])
        })
        .unwrap_or(JsonValue::Null)
}

fn phase_trace_value(trace: &ExecutionPhaseTrace) -> JsonValue {
    object(vec![
        string_field("status", phase_status(trace.status)),
        optional_string_field("message", trace.message.as_deref()),
    ])
}

fn equality_transport_value(result: Option<&EqualityTransportEvidence>) -> JsonValue {
    result
        .map(|result| {
            array(
                result
                    .steps
                    .iter()
                    .map(|step| {
                        object(vec![
                            string_field("from", step.from.to_string()),
                            string_field("to", step.to.to_string()),
                            string_field("equality", step.equality.to_string()),
                            optional_fact_id_field("equality_fact_id", step.equality_fact_id),
                        ])
                    })
                    .collect(),
            )
        })
        .unwrap_or(JsonValue::Null)
}

fn fact_transformation_value(result: Option<&FactTransformationEvidence>) -> JsonValue {
    result
        .map(|result| {
            object(vec![
                string_field("source", result.source.to_string()),
                (
                    "steps".to_string(),
                    array(
                        result
                            .steps
                            .iter()
                            .map(|step| {
                                object(vec![
                                    string_field("result", step.result.to_string()),
                                    (
                                        "rule".to_string(),
                                        fact_transformation_rule_value(&step.rule),
                                    ),
                                ])
                            })
                            .collect(),
                    ),
                ),
            ])
        })
        .unwrap_or(JsonValue::Null)
}

fn fact_transformation_rule_value(rule: &FactTransformationRule) -> JsonValue {
    match rule {
        FactTransformationRule::EqualityRewrite(evidence) => object(vec![
            string_field("kind", "EqualityRewrite"),
            (
                "transport".to_string(),
                equality_transport_value(Some(evidence)),
            ),
        ]),
        FactTransformationRule::RationalNormalization => {
            object(vec![string_field("kind", "RationalNormalization")])
        }
    }
}

fn rule_evidence_value(kind: &str, rule: &str) -> JsonValue {
    object(vec![string_field("kind", kind), string_field("rule", rule)])
}

fn arithmetic_builtin_rule_name(rule: ArithmeticBuiltinRule) -> &'static str {
    match rule {
        ArithmeticBuiltinRule::OrderTransitivity => "OrderTransitivity",
        ArithmeticBuiltinRule::LessEqualFromStrictOrder => "LessEqualFromStrictOrder",
        ArithmeticBuiltinRule::GreaterEqualFromStrictOrder => "GreaterEqualFromStrictOrder",
        ArithmeticBuiltinRule::SubNonnegativeFromLessEqual => "SubNonnegativeFromLessEqual",
        ArithmeticBuiltinRule::SubPositiveFromLess => "SubPositiveFromLess",
        ArithmeticBuiltinRule::AddNonnegative => "AddNonnegative",
        ArithmeticBuiltinRule::AddPositive => "AddPositive",
        ArithmeticBuiltinRule::AddPositiveLeftStrict => "AddPositiveLeftStrict",
        ArithmeticBuiltinRule::AddPositiveRightStrict => "AddPositiveRightStrict",
        ArithmeticBuiltinRule::MulNonnegative => "MulNonnegative",
        ArithmeticBuiltinRule::MulPositive => "MulPositive",
        ArithmeticBuiltinRule::DivNonnegative => "DivNonnegative",
        ArithmeticBuiltinRule::DivPositive => "DivPositive",
        ArithmeticBuiltinRule::AddCommonLeftLessEqual => "AddCommonLeftLessEqual",
        ArithmeticBuiltinRule::SubRightNonnegativeLessEqual => "SubRightNonnegativeLessEqual",
        ArithmeticBuiltinRule::AddRightNonnegativeLessEqual => "AddRightNonnegativeLessEqual",
        ArithmeticBuiltinRule::AddComponentwiseLessEqual => "AddComponentwiseLessEqual",
        ArithmeticBuiltinRule::AddCommonLeftLess => "AddCommonLeftLess",
        ArithmeticBuiltinRule::AddComponentwiseLess => "AddComponentwiseLess",
        ArithmeticBuiltinRule::AddComponentwiseLessLessEqual => "AddComponentwiseLessLessEqual",
        ArithmeticBuiltinRule::AddComponentwiseLessEqualLess => "AddComponentwiseLessEqualLess",
    }
}

fn integer_membership_closure_rule_name(rule: IntegerMembershipClosureBuiltinRule) -> &'static str {
    match rule {
        IntegerMembershipClosureBuiltinRule::Add => "Add",
        IntegerMembershipClosureBuiltinRule::Sub => "Sub",
        IntegerMembershipClosureBuiltinRule::Mul => "Mul",
        IntegerMembershipClosureBuiltinRule::Mod => "Mod",
    }
}

fn natural_membership_closure_rule_name(rule: NaturalMembershipClosureBuiltinRule) -> &'static str {
    match rule {
        NaturalMembershipClosureBuiltinRule::Add => "Add",
        NaturalMembershipClosureBuiltinRule::Mul => "Mul",
    }
}

fn rational_membership_closure_rule_name(
    rule: RationalMembershipClosureBuiltinRule,
) -> &'static str {
    match rule {
        RationalMembershipClosureBuiltinRule::Add => "Add",
        RationalMembershipClosureBuiltinRule::Sub => "Sub",
        RationalMembershipClosureBuiltinRule::Mul => "Mul",
        RationalMembershipClosureBuiltinRule::Div => "Div",
        RationalMembershipClosureBuiltinRule::Pow => "Pow",
    }
}

fn complex_membership_closure_rule_name(
    rule: ComplexArithmeticMembershipClosureBuiltinRule,
) -> &'static str {
    match rule {
        ComplexArithmeticMembershipClosureBuiltinRule::Add => "Add",
        ComplexArithmeticMembershipClosureBuiltinRule::Sub => "Sub",
        ComplexArithmeticMembershipClosureBuiltinRule::Mul => "Mul",
        ComplexArithmeticMembershipClosureBuiltinRule::Div => "Div",
    }
}

fn real_membership_closure_rule_name(
    rule: RealArithmeticMembershipClosureBuiltinRule,
) -> &'static str {
    match rule {
        RealArithmeticMembershipClosureBuiltinRule::Add => "Add",
        RealArithmeticMembershipClosureBuiltinRule::Sub => "Sub",
        RealArithmeticMembershipClosureBuiltinRule::Mul => "Mul",
        RealArithmeticMembershipClosureBuiltinRule::Div => "Div",
        RealArithmeticMembershipClosureBuiltinRule::Pow => "Pow",
    }
}

fn native_constant_membership_rule_name(rule: NativeConstantMembershipBuiltinRule) -> &'static str {
    match rule {
        NativeConstantMembershipBuiltinRule::ImaginaryUnitInComplex => "ImaginaryUnitInComplex",
        NativeConstantMembershipBuiltinRule::EulerNumberInReal => "EulerNumberInReal",
        NativeConstantMembershipBuiltinRule::PiInReal => "PiInReal",
    }
}

fn set_relation_duality_rule_name(rule: SetRelationDualityBuiltinRule) -> &'static str {
    match rule {
        SetRelationDualityBuiltinRule::SubsetFromSuperset => "SubsetFromSuperset",
        SetRelationDualityBuiltinRule::SupersetFromSubset => "SupersetFromSubset",
        SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset => "NotSubsetFromNotSuperset",
        SetRelationDualityBuiltinRule::NotSupersetFromNotSubset => "NotSupersetFromNotSubset",
    }
}

fn set_builtin_rule_name(rule: SetBuiltinRule) -> &'static str {
    match rule {
        SetBuiltinRule::UnionCommutative => "UnionCommutative",
        SetBuiltinRule::UnionAssociative => "UnionAssociative",
        SetBuiltinRule::UnionIdempotent => "UnionIdempotent",
        SetBuiltinRule::UnionEmptyIdentity => "UnionEmptyIdentity",
        SetBuiltinRule::IntersectCommutative => "IntersectCommutative",
        SetBuiltinRule::IntersectAssociative => "IntersectAssociative",
        SetBuiltinRule::UnionMembershipLeft => "UnionMembershipLeft",
        SetBuiltinRule::UnionMembershipRight => "UnionMembershipRight",
        SetBuiltinRule::IntersectMembershipBoth => "IntersectMembershipBoth",
        SetBuiltinRule::IntersectNonMembershipLeft => "IntersectNonMembershipLeft",
        SetBuiltinRule::IntersectNonMembershipRight => "IntersectNonMembershipRight",
        SetBuiltinRule::SetMinusMembership => "SetMinusMembership",
    }
}

fn finite_set_builtin_rule_name(rule: FiniteSetBuiltinRule) -> &'static str {
    match rule {
        FiniteSetBuiltinRule::ListSet => "ListSet",
        FiniteSetBuiltinRule::Range => "Range",
        FiniteSetBuiltinRule::ClosedRange => "ClosedRange",
    }
}

fn absolute_value_builtin_rule_name(rule: AbsoluteValueBuiltinRule) -> &'static str {
    match rule {
        AbsoluteValueBuiltinRule::NonnegativeIdentity => "NonnegativeIdentity",
        AbsoluteValueBuiltinRule::NonpositiveNegation => "NonpositiveNegation",
        AbsoluteValueBuiltinRule::Product => "Product",
        AbsoluteValueBuiltinRule::PositiveFromNonzero => "PositiveFromNonzero",
    }
}

fn unary_operator(operator: EvaluateUnaryObjOperator) -> &'static str {
    match operator {
        EvaluateUnaryObjOperator::Floor => "Floor",
        EvaluateUnaryObjOperator::Ceil => "Ceil",
        EvaluateUnaryObjOperator::Exp => "Exp",
        EvaluateUnaryObjOperator::Ln => "Ln",
        EvaluateUnaryObjOperator::Sign => "Sign",
        EvaluateUnaryObjOperator::Factorial => "Factorial",
        EvaluateUnaryObjOperator::Abs => "Abs",
    }
}

fn binary_operator(operator: EvaluateBinaryObjOperator) -> &'static str {
    match operator {
        EvaluateBinaryObjOperator::Add => "Add",
        EvaluateBinaryObjOperator::Sub => "Sub",
        EvaluateBinaryObjOperator::Mul => "Mul",
        EvaluateBinaryObjOperator::Div => "Div",
        EvaluateBinaryObjOperator::Mod => "Mod",
        EvaluateBinaryObjOperator::Quot => "Quot",
        EvaluateBinaryObjOperator::Gcd => "Gcd",
        EvaluateBinaryObjOperator::Lcm => "Lcm",
        EvaluateBinaryObjOperator::Min => "Min",
        EvaluateBinaryObjOperator::Max => "Max",
        EvaluateBinaryObjOperator::Pow => "Pow",
    }
}

fn shape_operator(operator: EvaluateObjShapeOperator) -> &'static str {
    match operator {
        EvaluateObjShapeOperator::CartDim => "CartDim",
        EvaluateObjShapeOperator::TupleDim => "TupleDim",
        EvaluateObjShapeOperator::ListSetSize => "ListSetSize",
        EvaluateObjShapeOperator::ClosedRangeSize => "ClosedRangeSize",
        EvaluateObjShapeOperator::RangeSize => "RangeSize",
        EvaluateObjShapeOperator::CartSize => "CartSize",
        EvaluateObjShapeOperator::FiniteSetMax => "FiniteSetMax",
        EvaluateObjShapeOperator::FiniteSetMin => "FiniteSetMin",
    }
}

fn wd_child_role_value(role: WellDefinedObjChildRole) -> JsonValue {
    match role {
        WellDefinedObjChildRole::FunctionPrefix {
            through_layer_index,
        } => object(vec![
            string_field("kind", "FunctionPrefix"),
            number_field("through_layer_index", through_layer_index),
        ]),
        WellDefinedObjChildRole::FunctionHead => object(vec![string_field("kind", "FunctionHead")]),
        WellDefinedObjChildRole::FunctionArgument {
            layer_index,
            argument_index,
        } => object(vec![
            string_field("kind", "FunctionArgument"),
            number_field("layer_index", layer_index),
            number_field("argument_index", argument_index),
        ]),
        WellDefinedObjChildRole::BuiltinArgument { argument_index } => object(vec![
            string_field("kind", "BuiltinArgument"),
            number_field("argument_index", argument_index),
        ]),
        WellDefinedObjChildRole::ConstructorArgument { argument_index } => object(vec![
            string_field("kind", "ConstructorArgument"),
            number_field("argument_index", argument_index),
        ]),
        WellDefinedObjChildRole::BinderParameterCarrier {
            parameter_group_index,
        } => object(vec![
            string_field("kind", "BinderParameterCarrier"),
            number_field("parameter_group_index", parameter_group_index),
        ]),
        WellDefinedObjChildRole::BinderReturnCarrier => {
            object(vec![string_field("kind", "BinderReturnCarrier")])
        }
        WellDefinedObjChildRole::BinderBody => object(vec![string_field("kind", "BinderBody")]),
        WellDefinedObjChildRole::VerificationDependency { dependency_index } => object(vec![
            string_field("kind", "VerificationDependency"),
            number_field("dependency_index", dependency_index),
        ]),
    }
}

fn wd_binder_premise_role(role: WellDefinedBinderPremiseRole) -> JsonValue {
    match role {
        WellDefinedBinderPremiseRole::ParameterMembership {
            parameter_group_index,
            parameter_index,
        } => object(vec![
            string_field("kind", "ParameterMembership"),
            number_field("parameter_group_index", parameter_group_index),
            number_field("parameter_index", parameter_index),
        ]),
        WellDefinedBinderPremiseRole::Domain { domain_index } => object(vec![
            string_field("kind", "Domain"),
            number_field("domain_index", domain_index),
        ]),
        WellDefinedBinderPremiseRole::LocalCondition { condition_index } => object(vec![
            string_field("kind", "LocalCondition"),
            number_field("condition_index", condition_index),
        ]),
    }
}

fn wd_requirement_role(role: WellDefinednessRequirementRole) -> JsonValue {
    match role {
        WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index } => {
            object(vec![
                string_field("kind", "BuiltinArgumentMembership"),
                number_field("argument_index", argument_index),
            ])
        }
        WellDefinednessRequirementRole::BuiltinArgumentNonzero { argument_index } => object(vec![
            string_field("kind", "BuiltinArgumentNonzero"),
            number_field("argument_index", argument_index),
        ]),
        WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
            left_index,
            right_index,
        } => object(vec![
            string_field("kind", "ConstructorPairwiseDistinct"),
            number_field("left_index", left_index),
            number_field("right_index", right_index),
        ]),
        WellDefinednessRequirementRole::FunctionArgumentMembership {
            layer_index,
            parameter_index,
        } => object(vec![
            string_field("kind", "FunctionArgumentMembership"),
            number_field("layer_index", layer_index),
            number_field("parameter_index", parameter_index),
        ]),
        WellDefinednessRequirementRole::FunctionDomain {
            layer_index,
            domain_index,
        } => object(vec![
            string_field("kind", "FunctionDomain"),
            number_field("layer_index", layer_index),
            number_field("domain_index", domain_index),
        ]),
        WellDefinednessRequirementRole::AnonymousFunctionBodyMembership => {
            object(vec![string_field(
                "kind",
                "AnonymousFunctionBodyMembership",
            )])
        }
        WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset {
            parameter_group_index,
            parameter_index,
        } => object(vec![
            string_field("kind", "AnonymousFunctionBoundParameterSubset"),
            number_field("parameter_group_index", parameter_group_index),
            number_field("parameter_index", parameter_index),
        ]),
    }
}

fn phase_status(status: StatementPhaseStatus) -> &'static str {
    match status {
        StatementPhaseStatus::Success => "Success",
        StatementPhaseStatus::Unknown => "Unknown",
        StatementPhaseStatus::Error => "Error",
        StatementPhaseStatus::Skipped => "Skipped",
        StatementPhaseStatus::NotRun => "NotRun",
    }
}

fn fact_id(id: FactId) -> String {
    id.to_string()
}

fn atomic_predicate_domain_check_role(role: AtomicPredicateDomainCheckRole) -> &'static str {
    match role {
        AtomicPredicateDomainCheckRole::ChoiceFunctionIndexSet => "ChoiceFunctionIndexSet",
        AtomicPredicateDomainCheckRole::ChoiceFunctionFamilySet => "ChoiceFunctionFamilySet",
        AtomicPredicateDomainCheckRole::ChoiceFunctionFamily => "ChoiceFunctionFamily",
        AtomicPredicateDomainCheckRole::ChoiceFunctionMember => "ChoiceFunctionMember",
        AtomicPredicateDomainCheckRole::PrimeNaturalArgument => "PrimeNaturalArgument",
        AtomicPredicateDomainCheckRole::CoprimeNaturalArgument => "CoprimeNaturalArgument",
        AtomicPredicateDomainCheckRole::DivisibilityIntegerArgument => {
            "DivisibilityIntegerArgument"
        }
        AtomicPredicateDomainCheckRole::DivisibilityNonzeroIntegerArgument => {
            "DivisibilityNonzeroIntegerArgument"
        }
        AtomicPredicateDomainCheckRole::OrderedRealCarrierEvidence => "OrderedRealCarrierEvidence",
        AtomicPredicateDomainCheckRole::FunctionPropertySignature => "FunctionPropertySignature",
    }
}

fn strings(values: &[String]) -> JsonValue {
    array(values.iter().cloned().map(string).collect())
}

fn display_values<T: ToString>(values: &[T]) -> JsonValue {
    array(
        values
            .iter()
            .map(|value| string(value.to_string()))
            .collect(),
    )
}

fn string_pairs(values: &[(String, String)]) -> JsonValue {
    array(
        values
            .iter()
            .map(|(left, right)| {
                object(vec![
                    string_field("left", left.clone()),
                    string_field("right", right.clone()),
                ])
            })
            .collect(),
    )
}

fn object(fields: Vec<(String, JsonValue)>) -> JsonValue {
    JsonValue::Object(fields)
}

fn array(values: Vec<JsonValue>) -> JsonValue {
    JsonValue::Array(values)
}

fn string(value: impl Into<String>) -> JsonValue {
    JsonValue::JsonString(value.into())
}

fn string_field(name: &str, value: impl Into<String>) -> (String, JsonValue) {
    (name.to_string(), string(value))
}

fn number_field(name: &str, value: usize) -> (String, JsonValue) {
    (name.to_string(), JsonValue::Number(value))
}

fn optional_string_field(name: &str, value: Option<&str>) -> (String, JsonValue) {
    (
        name.to_string(),
        value.map(string).unwrap_or(JsonValue::Null),
    )
}

fn optional_strings(values: Option<&Vec<String>>) -> JsonValue {
    values
        .map(|values| array(values.iter().cloned().map(string).collect()))
        .unwrap_or(JsonValue::Null)
}

fn optional_fact_id_field(name: &str, id: Option<FactId>) -> (String, JsonValue) {
    (
        name.to_string(),
        id.map(|id| string(fact_id(id))).unwrap_or(JsonValue::Null),
    )
}

fn optional_symbol_id_field(name: &str, id: Option<SymbolId>) -> (String, JsonValue) {
    (
        name.to_string(),
        id.map(|id| string(format!("symbol-{}", id.value())))
            .unwrap_or(JsonValue::Null),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numeric_fact_json_v2_retains_normalization_store_and_infer() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("numeric_fact_json_v2");
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks("2 + 3 $in N", Rc::from("numeric_fact_json_v2.lit"))
            .expect("numeric membership tokenizes");
        let stmt = runtime
            .parse_stmt(&mut blocks[0])
            .expect("numeric membership parses");
        let result = runtime
            .exec_stmt(&stmt)
            .expect("numeric membership verifies");

        let success = result
            .factual_success()
            .expect("numeric membership returns a factual success");

        let SuccessVerifyFactWellDefinedProofResult::AtomicFact(fact_wd) = success
            .well_definedness
            .recursive
            .as_deref()
            .expect("fact execution owns its recursive WD result")
        else {
            panic!("numeric membership must use the atomic-fact WD layer");
        };
        assert_eq!(fact_wd.arguments.len(), 2);
        let SuccessVerifyObjWellDefinedResult::Direct(add_wd) =
            fact_wd.arguments[0].result.as_ref()
        else {
            panic!("the source expression must own a direct object WD result");
        };
        assert_eq!(add_wd.object.to_string(), "2 + 3");
        assert_eq!(add_wd.steps.children.len(), 2);
        assert_eq!(add_wd.steps.children[0].source_object.to_string(), "2");
        assert_eq!(add_wd.steps.children[1].source_object.to_string(), "3");
        assert_eq!(add_wd.steps.target_requirements.len(), 2);
        assert!(add_wd.steps.target_requirements.iter().all(|requirement| {
            matches!(
                requirement.verification.as_ref(),
                SuccessVerifyFactResult::AtomicFact(_)
            )
        }));
        assert!(matches!(
            fact_wd.arguments[1].result.as_ref(),
            SuccessVerifyObjWellDefinedResult::Direct(_)
        ));

        let SuccessFactProofResult::BuiltinRule(proof) = success.proof() else {
            panic!("closed numeric membership must retain its builtin proof");
        };
        let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) = &proof.evidence else {
            panic!("closed numeric membership must retain its evaluation evidence");
        };
        assert_eq!(evidence.evaluation.expression.to_string(), "2 + 3");
        assert_eq!(evidence.evaluation.value.to_string(), "5");
        let SuccessEvaluateObjStepResult::Binary(evaluation) = &evidence.evaluation.step else {
            panic!("2 + 3 must retain a binary evaluation layer");
        };
        assert_eq!(evaluation.operator, EvaluateBinaryObjOperator::Add);
        assert_eq!(evaluation.left.value.to_string(), "2");
        assert_eq!(evaluation.right.value.to_string(), "3");

        assert!(success.store.infers.store_fact_outputs[0].inferred_fact_ids[0].is_some());
        let application = success
            .store
            .infers
            .rule_applications
            .first()
            .expect("natural membership records its selected infer rule");
        assert_eq!(
            application.rule,
            InferRule::NaturalMembershipImpliesNonnegative
        );
        assert_eq!(application.premises.len(), 1);
        assert_eq!(application.conclusions.len(), 1);
        assert_eq!(
            application.premises[0].fact_id, success.store.fact_id,
            "the infer premise cites the stored source fact"
        );
        assert!(application.conclusions[0].fact_id.is_some());
        assert_ne!(
            application.conclusions[0].fact_id, success.store.fact_id,
            "source and inferred facts have distinct identities"
        );

        let json = display_stmt_result_json_v2(&result);
        assert!(json.contains("\"schema\": \"litex.statement-result.v2\""));
        assert!(json.contains("\"kind\": \"ClosedNumericMembership\""));
        assert!(json.contains("\"operator\": \"Add\""));
        assert!(json.contains("\"value\": \"5\""));
        assert!(json.contains("\"statement\": \"2 + 3 >= 0\""));
        assert!(json.contains("\"rule\": \"NaturalMembershipImpliesNonnegative\""));
        assert!(!json.contains("LegacyPassThrough"));
    }

    #[test]
    fn object_choice_json_v2_retains_typed_standard_set_nonempty_child_evidence() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("object_choice_json_v2");
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks("have chosen R", Rc::from("object_choice_json_v2.lit"))
            .expect("object choice tokenizes");
        let stmt = runtime
            .parse_stmt(&mut blocks[0])
            .expect("object choice parses");
        let result = runtime.exec_stmt(&stmt).expect("object choice verifies");

        let StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::HaveObjInNonemptySetStmt(choice),
        )) = &result
        else {
            panic!("object choice returns its named result variant")
        };
        let nonempty = choice
            .verification
            .as_ref()
            .expect("object choice retains verification")
            .groups[0]
            .nonempty_check
            .as_deref()
            .expect("standard carrier retains nonempty child")
            .factual_success()
            .expect("nonempty child is factual");
        let SuccessFactProofResult::BuiltinRule(proof) = nonempty.proof() else {
            panic!("standard carrier nonempty child is builtin")
        };
        let Some(BuiltinRuleEvidence::StandardSetNonempty(evidence)) = &proof.evidence else {
            panic!("standard carrier nonempty child retains typed evidence")
        };
        assert_eq!(evidence.target_set, StandardSet::R);
        assert_eq!(evidence.expected_target.to_string(), "$is_nonempty_set(R)");

        let json = display_stmt_result_json_v2(&result);
        assert!(json.contains("\"kind\": \"StandardSetNonempty\""));
        assert!(json.contains("\"target_set\": \"R\""));
        assert!(json.contains("\"expected_target\": \"$is_nonempty_set(R)\""));
    }

    #[test]
    fn claim_json_v2_serializes_named_verification_fields_and_children() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("claim_json_v2");
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(
                "claim:\n    ? 1 = 1\n    1 = 1",
                Rc::from("claim_json_v2.lit"),
            )
            .expect("claim tokenizes");
        let stmt = runtime.parse_stmt(&mut blocks[0]).expect("claim parses");
        let result = runtime.exec_stmt(&stmt).expect("claim verifies");

        let StmtResult::Success(SuccessStmtResult::ProofBlock(
            SuccessProofBlockStmtResult::ClaimStmt(claim),
        )) = &result
        else {
            panic!("claim returns its matching successful statement result");
        };
        let Some(SuccessVerifyClaimResult::Fact(verification)) = &claim.verification else {
            panic!("ordinary claim owns its fact verification result");
        };
        assert_eq!(verification.proof_steps.len(), 1);
        assert_eq!(
            verification
                .conclusion_check
                .factual_success()
                .expect("claim conclusion is factual")
                .fact()
                .to_string(),
            "1 = 1"
        );

        let json = display_stmt_result_json_v2(&result);
        assert!(json.contains("\"kind\": \"ClaimStmt\""));
        assert!(json.contains("\"kind\": \"SuccessVerifyClaimFactResult\""));
        assert!(json.contains("\"proof_steps\":"));
        assert!(json.contains("\"conclusion_check\":"));
        assert!(json.contains("\"kind\": \"AtomicFact\""));
    }

    #[test]
    fn set_builder_wd_scope_is_owned_by_recursive_binder_fields() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("set_builder_recursive_wd");
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(
                "{x R: x > 0} = {x R: x > 0}",
                Rc::from("set_builder_recursive_wd.lit"),
            )
            .expect("set-builder equality tokenizes");
        let stmt = runtime
            .parse_stmt(&mut blocks[0])
            .expect("set-builder equality parses");
        let result = runtime
            .exec_stmt(&stmt)
            .expect("set-builder equality verifies");

        let fact = result
            .factual_success()
            .expect("set-builder equality returns a fact result");
        let SuccessVerifyFactWellDefinedProofResult::AtomicFact(wd) = fact
            .well_definedness
            .recursive
            .as_deref()
            .expect("fact owns recursive WD")
        else {
            panic!("set-builder equality uses atomic-fact WD");
        };
        assert_eq!(wd.arguments.len(), 2);
        for argument in &wd.arguments {
            let SuccessVerifyObjWellDefinedResult::Direct(object_wd) = argument.result.as_ref()
            else {
                panic!("each set-builder occurrence owns a direct WD node");
            };
            let Some(binder) = object_wd.steps.binder.as_deref() else {
                panic!("set-builder WD owns its binder result as a nested field");
            };
            let SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(binder) = binder else {
                panic!("set-builder object must own a set-builder binder result");
            };
            assert_eq!(binder.parameter_carrier.source_object.to_string(), "R");
            assert_eq!(binder.conditions.len(), 1);
            let Fact::AtomicFact(AtomicFact::InFact(parameter_membership)) =
                &binder.parameter.proposition
            else {
                panic!("set-builder parameter premise is membership");
            };
            let Fact::AtomicFact(AtomicFact::GreaterFact(condition)) =
                &binder.conditions[0].store.fact
            else {
                panic!("set-builder condition retains its greater-than fact");
            };
            assert!(objs_equal_with_nested_binder_alpha_equivalence(
                &parameter_membership.element,
                &condition.left,
            ));
            assert!(binder.conditions[0].store.fact_id.is_some());
        }

        let json = display_stmt_result_json_v2(&result);
        assert!(json.contains("\"kind\": \"SetBuilder\""));
        assert!(!json.contains("ambient_scope"));
        assert!(!json.contains("LegacyPassThrough"));
    }

    #[test]
    fn anonymous_function_wd_keeps_each_body_inside_its_own_binder_result() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("anonymous_function_recursive_wd");
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(
                "fn(x R) R {x + 1} = fn(y R) R {y + 1}",
                Rc::from("anonymous_function_recursive_wd.lit"),
            )
            .expect("anonymous-function equality tokenizes");
        let stmt = runtime
            .parse_stmt(&mut blocks[0])
            .expect("anonymous-function equality parses");
        let result = runtime
            .exec_stmt(&stmt)
            .expect("alpha-equivalent anonymous functions verify");
        let fact = result.factual_success().expect("result is factual");
        let SuccessVerifyFactWellDefinedProofResult::AtomicFact(wd) = fact
            .well_definedness
            .recursive
            .as_deref()
            .expect("fact owns recursive WD")
        else {
            panic!("function equality uses atomic-fact WD");
        };
        assert_eq!(wd.arguments.len(), 2);
        let mut binder_addresses = Vec::new();
        for argument in &wd.arguments {
            let SuccessVerifyObjWellDefinedResult::Direct(object_wd) = argument.result.as_ref()
            else {
                panic!("each anonymous-function occurrence owns direct WD");
            };
            let Some(binder) = object_wd.steps.binder.as_deref() else {
                panic!("anonymous-function WD owns its binder subtree");
            };
            binder_addresses.push(binder as *const _ as usize);
            let SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(binder) = binder
            else {
                panic!("anonymous function owns the matching binder result");
            };
            assert_eq!(binder.parameters.len(), 1);
            assert_eq!(binder.parameter_carriers[0].source_object.to_string(), "R");
            let Fact::AtomicFact(AtomicFact::InFact(parameter_membership)) =
                &binder.parameters[0].proposition
            else {
                panic!("anonymous-function parameter premise is membership");
            };
            let Obj::Add(body) = &binder.body.source_object else {
                panic!("anonymous-function body retains its addition object");
            };
            assert!(objs_equal_with_nested_binder_alpha_equivalence(
                &parameter_membership.element,
                &body.left,
            ));
            let Fact::AtomicFact(AtomicFact::InFact(body_membership)) =
                &binder.body_membership.expected_proposition
            else {
                panic!("anonymous-function body obligation is membership");
            };
            assert!(objs_equal_with_nested_binder_alpha_equivalence(
                &body_membership.element,
                &binder.body.source_object,
            ));
            assert_eq!(body_membership.set.to_string(), "R");
        }
        assert_ne!(binder_addresses[0], binder_addresses[1]);

        let json = display_stmt_result_json_v2(&result);
        assert!(json.contains("\"kind\": \"AnonymousFunction\""));
        assert!(!json.contains("ambient_scope"));
        assert!(!json.contains("LegacyPassThrough"));
    }

    #[test]
    fn forall_wd_returns_binder_premise_and_conclusion_layers() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("forall_recursive_wd");
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks(
                "forall x R:\n    x >= 0\n    =>:\n        x = x",
                Rc::from("forall_recursive_wd.lit"),
            )
            .expect("forall tokenizes");
        let stmt = runtime.parse_stmt(&mut blocks[0]).expect("forall parses");
        let result = runtime.exec_stmt(&stmt).expect("forall verifies");
        let fact = result.factual_success().expect("result is factual");
        let SuccessVerifyFactWellDefinedProofResult::ForallFact(wd) = fact
            .well_definedness
            .recursive
            .as_deref()
            .expect("forall owns recursive WD")
        else {
            panic!("forall statement owns a forall WD result");
        };
        assert_eq!(wd.binder.parameter_groups.len(), 1);
        assert_eq!(wd.binder.parameter_groups[0].parameters.len(), 1);
        assert_eq!(wd.premises.len(), 1);
        assert_eq!(wd.conclusions.len(), 1);
        assert!(wd.premises[0].store.fact_id.is_some());
        assert!(wd.conclusions[0].store.fact_id.is_some());
        let json = display_stmt_result_json_v2(&result);
        assert!(json.contains("\"kind\": \"ForallFact\""));
        assert!(json.contains("\"kind\": \"SuccessVerifyFactBinderResult\""));
        assert!(!json.contains("ambient_scope"));
        assert!(!json.contains("LegacyPassThrough"));
    }

    #[test]
    fn partial_predicate_wd_retains_its_domain_proof_result() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("partial_predicate_recursive_wd");
        let tokenizer = Tokenizer::new();
        let mut blocks = tokenizer
            .parse_blocks("$prime(2)", Rc::from("partial_predicate_recursive_wd.lit"))
            .expect("prime fact tokenizes");
        let stmt = runtime
            .parse_stmt(&mut blocks[0])
            .expect("prime fact parses");
        let result = runtime.exec_stmt(&stmt).expect("prime fact verifies");
        let fact = result.factual_success().expect("result is factual");
        let SuccessVerifyFactWellDefinedProofResult::AtomicFact(wd) = fact
            .well_definedness
            .recursive
            .as_deref()
            .expect("prime fact owns recursive WD")
        else {
            panic!("prime statement owns atomic WD");
        };
        assert_eq!(wd.predicate.name, PRIME);
        assert_eq!(wd.predicate.expected_arity, 1);
        assert_eq!(wd.predicate.domain_checks.len(), 1);
        assert_eq!(
            wd.predicate.domain_checks[0].role,
            AtomicPredicateDomainCheckRole::PrimeNaturalArgument
        );
        assert_eq!(
            wd.predicate.domain_checks[0]
                .result
                .factual_success()
                .expect("prime domain check is factual")
                .fact()
                .to_string(),
            "2 $in N"
        );

        let json = display_stmt_result_json_v2(&result);
        assert!(json.contains("\"kind\": \"SuccessVerifyAtomicPredicateWellDefinedResult\""));
        assert!(json.contains("\"role\": \"PrimeNaturalArgument\""));
    }
}
