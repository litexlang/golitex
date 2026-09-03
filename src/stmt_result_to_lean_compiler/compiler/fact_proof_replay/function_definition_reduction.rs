//! Checked function-definition reduction.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Leaf`: replay the verifier-selected one-step unfolding of a checked
    /// named function. The defining equality is resolved by exact `FactId`;
    /// the application orientation and reduced body come from the Result.
    pub(in super::super) fn construct_lean_checked_function_definition_reduction_from_result(
        &mut self,
        target: &Fact,
        reduction: &CheckedFunctionDefinitionReductionEvidence,
    ) -> Result<String, String> {
        let (target_left, target_right) = equality_parts(target)?;
        let (expected_application, expected_other) = if reduction.application_is_left {
            (target_left, target_right)
        } else {
            (target_right, target_left)
        };
        if obj_equality_key(expected_application) != obj_equality_key(&reduction.application_side)
            || obj_equality_key(expected_other) != obj_equality_key(&reduction.other_side)
        {
            return Err(
                "checked function-definition reduction changed its goal orientation".into(),
            );
        }
        let reduced_equality = reduction.reduced_equality.verified().ok_or_else(|| {
            "checked function-definition reduction retained an unproved reduced equality"
                .to_string()
        })?;
        let Fact::AtomicFact(AtomicFact::EqualFact(reduced_comparison)) = reduced_equality.fact()
        else {
            return Err("checked function-definition reduction child is not an equality".into());
        };
        if obj_equality_key(&reduced_comparison.left) != obj_equality_key(&reduction.reduced)
            || obj_equality_key(&reduced_comparison.right)
                != obj_equality_key(&reduction.other_side)
        {
            return Err(
                "checked function-definition reduction changed its reduced-equality child".into(),
            );
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(defining_equality)) =
            &reduction.defining_equality
        else {
            return Err("checked function-definition source is not an equality".into());
        };
        if obj_equality_key(&defining_equality.left)
            != obj_equality_key(&reduction.definition_object)
            || !matches!(&defining_equality.right, Obj::AnonymousFn(_))
        {
            return Err(
                "checked function-definition source changed its named-function definition".into(),
            );
        }
        resolve_fact_citation(
            &reduction.defining_equality_fact_id,
            &reduction.defining_equality,
            &self.environment_stack,
        )?;
        let binding = self
            .environment_stack
            .named_function_definitions
            .get(&reduction.defining_equality_fact_id)
            .ok_or_else(|| {
                format!(
                    "checked function-definition reduction references unavailable defining FactId `{}`",
                    reduction.defining_equality_fact_id
                )
            })?;
        if !object_is_symbol(&reduction.definition_object, binding.symbol_id) {
            return Err(
                "checked function-definition reduction changed its named function symbol".into(),
            );
        }
        let reduced_proof = self
            .construct_lean_proof_from_direct_fact_result(reduced_equality)?
            .ok_or_else(|| {
                "checked function-definition reduction child has no direct Lean proof constructor"
                    .to_string()
            })?;
        let unfolding_target: Fact = EqualFact::new(
            reduction.application_side.clone(),
            reduction.reduced.clone(),
            target.line_file(),
        )
        .into();
        let unfolding_proof = render_checked_identity_function_reduction_from_fact(
            &unfolding_target,
            reduction.defining_equality_fact_id,
            &self.environment_stack,
        )?;
        let no_observation = unfolding_proof.contains("NoObservation");
        if reduction.application_is_left {
            if no_observation {
                Ok(format!(
                    "Litex.Same.transNoObservation ({unfolding_proof}) (Litex.Same.withoutObservation ({reduced_proof}))"
                ))
            } else {
                Ok(format!(
                    "Litex.Same.trans ({unfolding_proof}) ({reduced_proof})"
                ))
            }
        } else {
            if no_observation {
                Ok(format!(
                    "Litex.Same.transNoObservation (Litex.Same.symmNoObservation (Litex.Same.withoutObservation ({reduced_proof}))) (Litex.Same.symmNoObservation ({unfolding_proof}))"
                ))
            } else {
                Ok(format!(
                    "Litex.Same.trans (Litex.Same.symm ({reduced_proof})) (Litex.Same.symm ({unfolding_proof}))"
                ))
            }
        }
    }
}
