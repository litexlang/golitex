//! Definition statement results.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn definition_stmt(
        &mut self,
        result: &SuccessDefinitionStmtResult,
    ) -> JsonValue {
        match result {
            SuccessDefinitionStmtResult::LetObjStmt(result) => self.non_fact_stmt(
                "LetObjStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
            SuccessDefinitionStmtResult::HaveObjInNonemptySetStmt(result) => {
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
            SuccessDefinitionStmtResult::HaveObjEqualStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyHaveObjEqualResult"),
                            (
                                "type_checks".to_string(),
                                self.verify_fact_results(&verification.type_checks),
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
            SuccessDefinitionStmtResult::HaveObjByExistFactsStmt(result) => {
                let verification =
                    optional_existential_elimination(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "HaveObjByExistFactsStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefinitionStmtResult::ObtainObjFromExistFact(result) => {
                let verification =
                    optional_existential_elimination(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ObtainObjFromExistFact",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefinitionStmtResult::ObtainObjFromAtomicFact(result) => {
                let verification =
                    optional_existential_elimination(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ObtainObjFromAtomicFact",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefinitionStmtResult::ObtainObjFromThm(result) => {
                let verification =
                    optional_existential_elimination(self, result.verification.as_ref());
                self.non_fact_stmt(
                    "ObtainObjFromThm",
                    result.statement.to_string(),
                    &result.common,
                    vec![("verification".to_string(), verification)],
                )
            }
            SuccessDefinitionStmtResult::HaveByPreimageStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyPreimageResult"),
                            (
                                "source_membership_check".to_string(),
                                self.verify_fact_result(&verification.source_membership_check),
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
            SuccessDefinitionStmtResult::HaveFnEqualStmt(result) => {
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
            SuccessDefinitionStmtResult::HaveFnEqualCaseByCaseStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyCaseFunctionDefinitionResult"),
                            (
                                "coverage_check".to_string(),
                                self.verify_fact_result(&verification.coverage_check),
                            ),
                            (
                                "return_checks".to_string(),
                                self.verify_fact_results(&verification.return_checks),
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
            SuccessDefinitionStmtResult::HaveFnByInducStmt(result) => {
                self.have_fn_by_induc_stmt(result)
            }
            SuccessDefinitionStmtResult::HaveFnByForallExistUniqueStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyFunctionFromUniqueExistenceResult"),
                            (
                                "well_definedness".to_string(),
                                self.fact_well_definedness(&verification.well_definedness),
                            ),
                            (
                                "proof_scope".to_string(),
                                self.local_proof_scope(&verification.proof_scope),
                            ),
                            (
                                "source_forall_check".to_string(),
                                verification
                                    .source_forall_check
                                    .as_ref()
                                    .map(|check| self.verify_fact_result(check))
                                    .unwrap_or(JsonValue::Null),
                            ),
                            (
                                "proof_steps".to_string(),
                                self.stmt_results(&verification.proof_steps),
                            ),
                            (
                                "conclusion_checks".to_string(),
                                self.verify_fact_results(&verification.conclusion_checks),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                let published_property_well_definedness = result
                    .published_property_well_definedness
                    .as_ref()
                    .map(|well_definedness| self.fact_well_definedness(well_definedness))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "HaveFnByForallExistUniqueStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![
                        ("verification".to_string(), verification),
                        (
                            "published_property_well_definedness".to_string(),
                            published_property_well_definedness,
                        ),
                    ],
                )
            }
            SuccessDefinitionStmtResult::DefPropStmt(result) => {
                let run_in_local_env = result
                    .run_in_local_env
                    .as_ref()
                    .map(|local| {
                        object(vec![
                            string_field("kind", "SuccessVerifyDefPropLocalEnvResult"),
                            ("binder".to_string(), self.fact_binder_result(&local.binder)),
                            (
                                "body".to_string(),
                                array(
                                    local
                                        .body
                                        .iter()
                                        .map(|fact| self.local_fact_wd_result(fact))
                                        .collect(),
                                ),
                            ),
                        ])
                    })
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "DefPropStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![("run_in_local_env".to_string(), run_in_local_env)],
                )
            }
            SuccessDefinitionStmtResult::DefAbstractPropStmt(result) => self.non_fact_stmt(
                "DefAbstractPropStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
            SuccessDefinitionStmtResult::DefSettingStmt(result) => self.non_fact_stmt(
                "DefSettingStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
            SuccessDefinitionStmtResult::DefTemplateStmt(result) => object(vec![
                string_field("kind", "DefTemplateStmt"),
                string_field("statement", result.statement.to_string()),
                (
                    "template_parameter_groups".to_string(),
                    self.fact_parameter_groups(&result.template_parameter_groups),
                ),
                (
                    "template_domain_results".to_string(),
                    array(
                        result
                            .template_domain_results
                            .iter()
                            .map(|domain| self.local_fact_wd_result(domain))
                            .collect(),
                    ),
                ),
                (
                    "body_statement_result".to_string(),
                    self.success_stmt(&result.body_statement_result),
                ),
            ]),
            SuccessDefinitionStmtResult::DefStructStmt(result) => self.def_struct_stmt(result),
            SuccessDefinitionStmtResult::DefAlgoStmt(result) => self.def_algo_stmt(result),
            SuccessDefinitionStmtResult::DefThmStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|result| self.theorem_verification(result))
                    .unwrap_or(JsonValue::Null);
                self.non_fact_stmt(
                    "DefThmStmt",
                    result.statement.to_string(),
                    &result.common,
                    vec![
                        string_field("source_fact_id", fact_id(result.source_fact_id)),
                        ("verification".to_string(), verification),
                    ],
                )
            }
            SuccessDefinitionStmtResult::AxiomStmt(result) => {
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
            SuccessDefinitionStmtResult::DefStrategyStmt(result) => {
                let verification = result
                    .verification
                    .as_ref()
                    .map(|verification| {
                        object(vec![
                            string_field("kind", "SuccessVerifyStrategyDefinitionResult"),
                            string_field("name", verification.name.clone()),
                            string_field("forall_fact", verification.forall_fact.to_string()),
                            (
                                "well_definedness".to_string(),
                                self.fact_well_definedness(&verification.well_definedness),
                            ),
                            (
                                "proof_scope".to_string(),
                                self.local_proof_scope(&verification.proof_scope),
                            ),
                            (
                                "proof_steps".to_string(),
                                self.stmt_results(&verification.proof_steps),
                            ),
                            (
                                "conclusion_checks".to_string(),
                                self.verify_fact_results(&verification.conclusion_checks),
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
        }
    }
}
