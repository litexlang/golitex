//! Cases, contradiction, and local proof scopes.

use super::*;

impl StatementResultRenderer {
    pub(in super::super) fn by_cases_verification(
        &mut self,
        result: &SuccessVerifyByCasesResult,
    ) -> JsonValue {
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
                self.verify_fact_result(&result.coverage_check),
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

    pub(in super::super) fn by_case_branch(
        &mut self,
        result: &SuccessVerifyByCaseBranchResult,
    ) -> JsonValue {
        let exit = match &result.exit {
            SuccessVerifyByCaseBranchExitResult::Conclusions(conclusions) => object(vec![
                string_field("kind", "SuccessVerifyByCaseConclusionsResult"),
                (
                    "checks".to_string(),
                    self.verify_fact_results(&conclusions.checks),
                ),
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

    pub(in super::super) fn by_contra_verification(
        &mut self,
        result: &SuccessVerifyByContraResult,
    ) -> JsonValue {
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

    pub(in super::super) fn contradiction_verification(
        &mut self,
        result: &SuccessVerifyContradictionResult,
    ) -> JsonValue {
        object(vec![
            string_field("kind", "SuccessVerifyContradictionResult"),
            (
                "impossible_check".to_string(),
                self.verify_fact_result(&result.impossible_check),
            ),
            (
                "negated_impossible_check".to_string(),
                self.verify_fact_result(&result.negated_impossible_check),
            ),
        ])
    }

    pub(in super::super) fn local_proof_scope(
        &mut self,
        result: &SuccessVerifyLocalProofScopeResult,
    ) -> JsonValue {
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
}
