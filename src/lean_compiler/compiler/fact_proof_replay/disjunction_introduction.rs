//! Disjunction introduction.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn construct_lean_disjunction_introduction_from_result(
        &mut self,
        target: &Fact,
        evidence: &DisjunctionIntroductionBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("disjunction-introduction evidence changed its target".into());
        }
        let branches = disjunction_components(target)?;
        let Some(selected) = branches.get(evidence.selected_index) else {
            return Err("disjunction-introduction evidence selected no target branch".into());
        };
        if selected.to_string() != evidence.expected_selected.to_string() {
            return Err("disjunction-introduction evidence changed its selected branch".into());
        }
        let [selected_result] = subgoals else {
            return Err(
                "disjunction-introduction evidence must retain one selected child Result".into(),
            );
        };
        let selected_result = selected_result
            .factual_success()
            .ok_or_else(|| "disjunction selected child is not factual".to_string())?;
        if selected_result.fact().to_string() != selected.to_string()
            || !selected_result.store.infers.is_empty()
        {
            return Err("disjunction selected child changed its proposition or effects".into());
        }
        let Some(selected_proof) =
            self.construct_lean_proof_from_direct_fact_result(selected_result)?
        else {
            return Ok(None);
        };
        Ok(Some(right_associated_disjunction_injection(
            selected_proof,
            evidence.selected_index,
            branches.len(),
        )?))
    }
}
