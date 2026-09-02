//! Standard-set membership projection.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Wrap`: compile the one exact source-membership child first and then
    /// apply the fixed standard-set inclusion chain selected by the retained
    /// source and target sets. This consumes the recursive Result directly;
    /// no diagnostic label or compatibility proof IR participates.
    pub(in super::super) fn construct_lean_standard_set_membership_projection_from_result(
        &mut self,
        target: &Fact,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        let [source_result] = subgoals else {
            return Err(
                "standard-set membership projection requires exactly one child Result".into(),
            );
        };
        let source_result = source_result
            .verified()
            .ok_or_else(|| "standard-set membership projection child is not factual".to_string())?;
        let source = source_result.fact();
        let (target_element, target_set) = membership_parts(target)?;
        let (source_element, source_set) = membership_parts(&source)?;
        if obj_equality_key(target_element) != obj_equality_key(source_element) {
            return Err("standard-set membership projection changed its source element".into());
        }
        let (Obj::StandardSet(source_set), Obj::StandardSet(target_set)) = (source_set, target_set)
        else {
            return Err("standard-set membership projection retained a nonstandard set".into());
        };
        let Some(mut proof) = self.construct_lean_proof_from_direct_fact_result(source_result)?
        else {
            return Ok(None);
        };
        for theorem in standard_set_membership_projection_theorem_chain(*source_set, *target_set)? {
            proof = format!("Litex.Rules.{theorem} ({proof})");
        }
        Ok(Some(proof))
    }
}
