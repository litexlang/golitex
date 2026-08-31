//! Inductively defined function verification and cases.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn have_fn_by_induc_stmt(
        &mut self,
        result: &SuccessHaveFnByInducStmtResult,
    ) -> JsonValue {
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

    pub(in super::super) fn have_fn_by_induc_verification(
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

    pub(in super::super) fn have_fn_by_induc_parameters_and_domain(
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

    pub(in super::super) fn have_fn_by_induc_case_list(
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
}
