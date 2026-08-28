//! Checked function-definition reduction.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Leaf`: replay the verifier-selected one-step unfolding of a checked
    /// named function. The defining equality is resolved by exact `FactId`;
    /// the application orientation and reduced body come from the Result.
    pub(in super::super) fn construct_lean_checked_function_definition_reduction_from_result(
        &self,
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
        if !reduction.reduced_matches_other_by_alpha
            || !objs_equal_with_nested_binder_alpha_equivalence(
                &reduction.reduced,
                &reduction.other_side,
            )
        {
            return Err("checked function-definition reduction changed its reduced result".into());
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
        let application_side = if reduction.application_is_left {
            LeanEqualityApplicationSide::Left
        } else {
            LeanEqualityApplicationSide::Right
        };
        render_checked_identity_function_reduction_from_fact(
            target,
            reduction.defining_equality_fact_id,
            application_side,
            &self.environment_stack,
        )
    }
}
