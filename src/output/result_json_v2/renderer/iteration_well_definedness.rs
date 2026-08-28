//! Reduction, aggregate, iteration, interval, and coverage results.

use super::*;

impl StmtResultJsonV2 {
    pub(in super::super) fn finite_reduce_operation_laws(
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

    pub(in super::super) fn reduce_mode(
        &mut self,
        result: &SuccessVerifyReduceModeResult,
    ) -> JsonValue {
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

    pub(in super::super) fn finite_aggregate_mode(
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

    pub(in super::super) fn iteration_scalar_return(
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

    pub(in super::super) fn iteration_interval(
        &mut self,
        result: &SuccessVerifyIterationIntervalResult,
    ) -> JsonValue {
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

    pub(in super::super) fn iteration_coverage(
        &mut self,
        result: &SuccessVerifyIterationCoverageResult,
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
}
