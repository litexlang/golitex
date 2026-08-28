//! Known equality path replay.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Reuse` / `Combine`: every edge cites the exact previously stored
    /// equality FactId retained by the verifier. No proposition lookup or
    /// equality-graph search is repeated in the compiler.
    pub(in super::super) fn construct_lean_known_equality_path_from_result(
        &self,
        target: &Fact,
        evidence: &KnownEqualityBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<String, String> {
        if evidence.expected_target.to_string() != target.to_string() || !subgoals.is_empty() {
            return Err("known-equality path changed its target or gained child Results".into());
        }
        let (target_left, target_right) = equality_parts(target)?;
        if evidence.steps.is_empty() {
            return Err("known-equality path retained no steps".into());
        }
        let mut current_key = obj_equality_key(target_left);
        let target_key = obj_equality_key(target_right);
        let mut accumulated: Option<String> = None;
        for (index, step) in evidence.steps.iter().enumerate() {
            if current_key != obj_equality_key(&step.from) {
                return Err(format!("known-equality path step {index} is disconnected"));
            }
            let left_key = obj_equality_key(&step.equality.left);
            let right_key = obj_equality_key(&step.equality.right);
            let from_key = obj_equality_key(&step.from);
            let to_key = obj_equality_key(&step.to);
            let reverse = if from_key == left_key && to_key == right_key {
                false
            } else if from_key == right_key && to_key == left_key {
                true
            } else {
                return Err(format!(
                    "known-equality path step {index} has invalid orientation"
                ));
            };
            let equality_fact: Fact = AtomicFact::EqualFact(step.equality.clone()).into();
            let cited = resolve_fact_citation(
                &step.source_fact_id,
                &equality_fact,
                &self.environment_stack,
            )?;
            let oriented = if reverse {
                format!("Litex.Same.symm ({cited})")
            } else {
                cited
            };
            accumulated = Some(match accumulated {
                None => oriented,
                Some(previous) => format!("Litex.Same.trans ({previous}) ({oriented})"),
            });
            current_key = to_key;
        }
        if current_key != target_key {
            return Err("known-equality path does not end at its target".into());
        }
        render_fact(target, &self.environment_stack)?;
        accumulated.ok_or_else(|| "known-equality path retained no proof".into())
    }
}
