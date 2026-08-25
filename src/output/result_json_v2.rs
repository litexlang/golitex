use crate::common::json_value::{render_json_value, JsonValue};
use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

mod helpers;
use helpers::*;

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
            SuccessStmtResult::Definition(result) => self.definition_stmt(result),
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

    fn def_struct_stmt(&mut self, result: &SuccessDefStructStmtResult) -> JsonValue {
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

    fn def_algo_stmt(&mut self, result: &SuccessDefAlgoStmtResult) -> JsonValue {
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

    fn have_fn_by_induc_stmt(&mut self, result: &SuccessHaveFnByInducStmtResult) -> JsonValue {
        let verification = result
            .verification
            .as_ref()
            .map(|verification| self.have_fn_by_induc_verification(verification))
            .unwrap_or(JsonValue::Null);
        self.non_fact_stmt(
            "HaveFnByInducStmt",
            result.statement.to_string(),
            &result.common,
            vec![("verification".to_string(), verification)],
        )
    }

    fn have_fn_by_induc_verification(
        &mut self,
        result: &SuccessVerifyHaveFnByInducResult,
    ) -> JsonValue {
        let well_definedness = &result.well_definedness_run_in_local_env;
        let verification = &result.verification_run_in_local_env;
        object(vec![
            string_field("kind", "SuccessVerifyHaveFnByInducResult"),
            (
                "well_definedness_run_in_local_env".to_string(),
                object(vec![
                    string_field("function_binding", well_definedness.function_binding.name()),
                    string_field("function_set", well_definedness.function_set.to_string()),
                    (
                        "function_set_well_definedness".to_string(),
                        self.shared_wd_obj(&well_definedness.function_set_well_definedness),
                    ),
                    (
                        "parameters_and_domain".to_string(),
                        self.have_fn_by_induc_parameters_and_domain(
                            &well_definedness.parameters_and_domain,
                        ),
                    ),
                    (
                        "measure_well_definedness".to_string(),
                        self.shared_wd_obj(&well_definedness.measure_well_definedness),
                    ),
                    (
                        "lower_bound_well_definedness".to_string(),
                        self.shared_wd_obj(&well_definedness.lower_bound_well_definedness),
                    ),
                ]),
            ),
            (
                "verification_run_in_local_env".to_string(),
                object(vec![
                    (
                        "parameters_and_domain".to_string(),
                        self.have_fn_by_induc_parameters_and_domain(
                            &verification.parameters_and_domain,
                        ),
                    ),
                    (
                        "measure".to_string(),
                        object(vec![
                            (
                                "measure_well_definedness".to_string(),
                                self.shared_wd_obj(&verification.measure.measure_well_definedness),
                            ),
                            (
                                "lower_bound_well_definedness".to_string(),
                                self.shared_wd_obj(
                                    &verification.measure.lower_bound_well_definedness,
                                ),
                            ),
                            (
                                "measure_integer_check".to_string(),
                                self.stmt_result(&verification.measure.measure_integer_check),
                            ),
                            (
                                "lower_bound_integer_check".to_string(),
                                self.stmt_result(&verification.measure.lower_bound_integer_check),
                            ),
                            (
                                "lower_bound_check".to_string(),
                                self.stmt_result(&verification.measure.lower_bound_check),
                            ),
                        ]),
                    ),
                    (
                        "recursive_function".to_string(),
                        object(vec![
                            string_field(
                                "function_set",
                                verification.recursive_function.function_set.to_string(),
                            ),
                            (
                                "membership_store".to_string(),
                                self.store_fact(&verification.recursive_function.membership_store),
                            ),
                        ]),
                    ),
                    (
                        "cases".to_string(),
                        self.have_fn_by_induc_case_list(&verification.cases),
                    ),
                ]),
            ),
        ])
    }

    fn have_fn_by_induc_parameters_and_domain(
        &mut self,
        result: &SuccessVerifyHaveFnByInducParametersAndDomainResult,
    ) -> JsonValue {
        object(vec![
            (
                "parameter_groups".to_string(),
                array(
                    result
                        .parameter_groups
                        .iter()
                        .map(|group| {
                            object(vec![
                                number_field("group_index", group.group_index),
                                string_field("definition", group.definition.to_string()),
                                ("infers".to_string(), infer_result_value(&group.infers)),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "domain_facts".to_string(),
                array(
                    result
                        .domain_facts
                        .iter()
                        .map(|domain| {
                            object(vec![
                                number_field("domain_index", domain.domain_index),
                                ("store".to_string(), self.store_fact(&domain.store)),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
    }

    fn have_fn_by_induc_case_list(
        &mut self,
        result: &SuccessVerifyHaveFnByInducCaseListResult,
    ) -> JsonValue {
        object(vec![
            string_field("coverage_fact", result.coverage_fact.to_string()),
            (
                "coverage_check".to_string(),
                self.stmt_result(&result.coverage_check),
            ),
            (
                "mutual_exclusions".to_string(),
                array(
                    result
                        .mutual_exclusions
                        .iter()
                        .map(|proof| {
                            object(vec![
                                number_field("left_case_index", proof.left_case_index),
                                number_field("right_case_index", proof.right_case_index),
                                string_field(
                                    "orientation",
                                    match proof.orientation {
                                        CaseDisjointnessOrientation::LeftImpliesNotRight => {
                                            "LeftImpliesNotRight"
                                        }
                                        CaseDisjointnessOrientation::RightImpliesNotLeft => {
                                            "RightImpliesNotLeft"
                                        }
                                    },
                                ),
                                string_field("assumed_case", proof.assumed_case.to_string()),
                                (
                                    "assumption_store".to_string(),
                                    self.store_fact(&proof.assumption_store),
                                ),
                                string_field(
                                    "contradicted_atom",
                                    proof.contradicted_atom.to_string(),
                                ),
                                string_field("negated_atom", proof.negated_atom.to_string()),
                                (
                                    "negated_atom_check".to_string(),
                                    self.stmt_result(&proof.negated_atom_check),
                                ),
                            ])
                        })
                        .collect(),
                ),
            ),
            (
                "cases".to_string(),
                array(
                    result
                        .cases
                        .iter()
                        .map(|case| {
                            let body = match &case.body {
                                SuccessVerifyHaveFnByInducCaseBodyResult::EqualTo(body) => {
                                    object(vec![
                                        string_field("kind", "EqualTo"),
                                        string_field("value", body.value.to_string()),
                                        (
                                            "well_definedness".to_string(),
                                            self.shared_wd_obj(&body.well_definedness),
                                        ),
                                        string_field(
                                            "return_membership_fact",
                                            body.return_membership_fact.to_string(),
                                        ),
                                        (
                                            "return_membership_check".to_string(),
                                            self.stmt_result(&body.return_membership_check),
                                        ),
                                    ])
                                }
                                SuccessVerifyHaveFnByInducCaseBodyResult::NestedCases(nested) => {
                                    object(vec![
                                        string_field("kind", "NestedCases"),
                                        (
                                            "cases".to_string(),
                                            self.have_fn_by_induc_case_list(nested),
                                        ),
                                    ])
                                }
                            };
                            object(vec![
                                number_field("case_index", case.case_index),
                                string_field("case_fact", case.case_fact.to_string()),
                                (
                                    "assumption_store".to_string(),
                                    self.store_fact(&case.assumption_store),
                                ),
                                ("body".to_string(), body),
                            ])
                        })
                        .collect(),
                ),
            ),
        ])
    }

    fn import_stmt(&mut self, result: &SuccessImportStmtResult) -> JsonValue {
        let execution = match &result.execution {
            SuccessImportExecutionResult::Executed(executed) => object(vec![
                string_field("kind", "Executed"),
                number_field("module_id", executed.module_id.0),
                string_field(
                    "execution_mode",
                    match executed.execution_mode {
                        ExecutionMode::Verified => "Verified",
                        ExecutionMode::Trusted => "Trusted",
                    },
                ),
                (
                    "statement_results".to_string(),
                    self.stmt_results(&executed.statement_results),
                ),
            ]),
            SuccessImportExecutionResult::Reused(reused) => object(vec![
                string_field("kind", "Reused"),
                number_field("module_id", reused.module_id.0),
                string_field(
                    "execution_mode",
                    match reused.execution_mode {
                        ExecutionMode::Verified => "Verified",
                        ExecutionMode::Trusted => "Trusted",
                    },
                ),
            ]),
        };
        self.non_fact_stmt(
            "ImportStmt",
            result.statement.to_string(),
            &result.common,
            vec![("execution".to_string(), execution)],
        )
    }

    fn definition_stmt(&mut self, result: &SuccessDefinitionStmtResult) -> JsonValue {
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
            SuccessDefinitionStmtResult::HaveTupleStmt(result) => self.tuple_or_cart_stmt(
                "HaveTupleStmt",
                result.statement.to_string(),
                &result.common,
                result.verification.as_ref(),
            ),
            SuccessDefinitionStmtResult::HaveCartStmt(result) => self.tuple_or_cart_stmt(
                "HaveCartStmt",
                result.statement.to_string(),
                &result.common,
                result.verification.as_ref(),
            ),
            SuccessDefinitionStmtResult::HaveSeqStmt(result) => self.indexed_function_stmt(
                "HaveSeqStmt",
                result.statement.to_string(),
                &result.common,
                result.verification.as_ref(),
            ),
            SuccessDefinitionStmtResult::HaveFiniteSeqStmt(result) => self.indexed_function_stmt(
                "HaveFiniteSeqStmt",
                result.statement.to_string(),
                &result.common,
                result.verification.as_ref(),
            ),
            SuccessDefinitionStmtResult::HaveMatrixStmt(result) => self.indexed_function_stmt(
                "HaveMatrixStmt",
                result.statement.to_string(),
                &result.common,
                result.verification.as_ref(),
            ),
            SuccessDefinitionStmtResult::DefPropStmt(result) => self.non_fact_stmt(
                "DefPropStmt",
                result.statement.to_string(),
                &result.common,
                vec![],
            ),
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
                    vec![("verification".to_string(), verification)],
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
            SuccessCommandStmtResult::ImportStmt(result) => self.import_stmt(result),
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
                vec![
                    (
                        "execution".to_string(),
                        eval_stmt_execution_result_value(&result.execution),
                    ),
                    (
                        "reported_store_facts".to_string(),
                        array(
                            result
                                .common
                                .infers
                                .store_fact_outputs
                                .iter()
                                .map(store_fact_output_value)
                                .collect(),
                        ),
                    ),
                ],
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
                self.fact_parameter_groups(&result.parameter_groups),
            ),
        ])
    }

    fn fact_parameter_groups(
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
                    "template_instantiation".to_string(),
                    result
                        .steps
                        .template_instantiation
                        .as_ref()
                        .map(|instantiation| self.template_instantiation(instantiation))
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

    fn template_instantiation(&mut self, result: &SuccessTemplateInstantiationResult) -> JsonValue {
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
            SuccessFactProofResult::StoredFactCitation(result) => object(vec![
                string_field("kind", "StoredFactCitation"),
                optional_string_field("detail", result.detail.as_deref()),
                string_field("source_fact", result.source_fact.to_string()),
                string_field("source_fact_id", fact_id(result.source_fact_id)),
            ]),
            SuccessFactProofResult::Strategy(result) => object(vec![
                string_field("kind", "Strategy"),
                optional_string_field("detail", result.detail.as_deref()),
                string_field("strategy", result.strategy.to_string()),
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

    fn builtin_proof(&mut self, kind: &str, result: &SuccessBuiltinFactProofResult) -> JsonValue {
        object(vec![
            string_field("kind", kind),
            string_field("diagnostic_label", result.msg.clone()),
            (
                "evidence".to_string(),
                match &result.evidence {
                    SuccessBuiltinFactProofEvidenceResult::Typed(evidence) => object(vec![
                        string_field("kind", "Typed"),
                        ("value".to_string(), self.builtin_evidence(evidence)),
                    ]),
                    SuccessBuiltinFactProofEvidenceResult::DiagnosticOnly => {
                        object(vec![string_field("kind", "DiagnosticOnly")])
                    }
                },
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

    fn known_forall(&mut self, result: &SuccessInstantiateKnownForallResult) -> JsonValue {
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
                (
                    "left_evaluation".to_string(),
                    evaluation_value(&result.left_evaluation),
                ),
                (
                    "right_evaluation".to_string(),
                    evaluation_value(&result.right_evaluation),
                ),
            ]),
            BuiltinRuleEvidence::OrderReflexivity(result) => object(vec![
                string_field("kind", "OrderReflexivity"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("repeated_object", result.repeated_object.to_string()),
            ]),
            BuiltinRuleEvidence::RuntimeResolvedNumericComparison(result) => object(vec![
                string_field("kind", "RuntimeResolvedNumericComparison"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("normalized_left", result.normalized_left.to_string()),
                string_field("normalized_right", result.normalized_right.to_string()),
            ]),
            BuiltinRuleEvidence::RegisteredReflexivePredicate(result) => object(vec![
                string_field("kind", "RegisteredReflexivePredicate"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("predicate_name", result.predicate_name.clone()),
            ]),
            BuiltinRuleEvidence::RegisteredSymmetricPredicate(result) => object(vec![
                string_field("kind", "RegisteredSymmetricPredicate"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("predicate_name", result.predicate_name.clone()),
                (
                    "gather".to_string(),
                    JsonValue::Array(
                        result
                            .gather
                            .iter()
                            .map(|index| JsonValue::Number(*index))
                            .collect(),
                    ),
                ),
                string_field("expected_alternate", result.expected_alternate.to_string()),
            ]),
            BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(result) => object(vec![
                string_field("kind", "RegisteredAntisymmetricPredicate"),
                string_field("expected_target", result.expected_target.to_string()),
                string_field("predicate_name", result.predicate_name.clone()),
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
            BuiltinRuleEvidence::ComplexAlgebraicNormalization(result) => object(vec![
                string_field("kind", "ComplexAlgebraicNormalization"),
                string_field("expected_target", result.expected_target.to_string()),
                (
                    "expected_nonzero_premises".to_string(),
                    array(
                        result
                            .expected_nonzero_premises
                            .iter()
                            .map(|fact| JsonValue::JsonString(fact.to_string()))
                            .collect(),
                    ),
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
