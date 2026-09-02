//! Set-relation duality replay.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `PassThrough`: subset/superset dual spellings lower to the same Lean
    /// proposition. The one exact child Result therefore supplies the proof,
    /// while the typed rule fixes which source-level conversion occurred.
    pub(in super::super) fn construct_lean_set_relation_duality_from_result(
        &mut self,
        target: &Fact,
        rule: SetRelationDualityBuiltinRule,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        let [child] = subgoals else {
            return Err("set-relation duality requires one child Result".into());
        };
        let child = child
            .verified()
            .ok_or_else(|| "set-relation duality child is not factual".to_string())?;
        let (target_left, target_right, target_negated, target_is_subset_spelling) =
            normalized_set_relation_parts(target)?;
        let child_fact = child.fact();
        let (child_left, child_right, child_negated, child_is_subset_spelling) =
            normalized_set_relation_parts(&child_fact)?;
        let expected_target_subset_spelling = match rule {
            SetRelationDualityBuiltinRule::SubsetFromSuperset
            | SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset => true,
            SetRelationDualityBuiltinRule::SupersetFromSubset
            | SetRelationDualityBuiltinRule::NotSupersetFromNotSubset => false,
        };
        let expected_negated = matches!(
            rule,
            SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset
                | SetRelationDualityBuiltinRule::NotSupersetFromNotSubset
        );
        if target_is_subset_spelling != expected_target_subset_spelling
            || child_is_subset_spelling == target_is_subset_spelling
            || target_negated != expected_negated
            || child_negated != expected_negated
            || obj_equality_key(target_left) != obj_equality_key(child_left)
            || obj_equality_key(target_right) != obj_equality_key(child_right)
        {
            return Err("set-relation duality changed its orientation or endpoints".into());
        }
        if render_fact(target, &self.environment_stack)?
            != render_fact(&child_fact, &self.environment_stack)?
        {
            return Err("set-relation duality no longer lowers to one Lean proposition".into());
        }
        self.construct_lean_proof_from_direct_fact_result(child)
    }
}
