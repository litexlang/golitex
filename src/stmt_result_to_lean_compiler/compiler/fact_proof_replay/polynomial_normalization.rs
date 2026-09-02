//! Integral polynomial normalization replay.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn construct_lean_integral_polynomial_normalization_from_result(
        &self,
        target: &Fact,
        evidence: &IntegralPolynomialNormalizationBuiltinRuleEvidence,
        subgoals: &[VerifyFactResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("integral-polynomial evidence changed its target".into());
        }
        if !subgoals.is_empty() {
            return Err("integral-polynomial evidence unexpectedly gained child Results".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = target else {
            return Err("integral-polynomial evidence targets a non-equality fact".into());
        };
        if !objs_form_verified_integral_polynomial_congruence_identity(
            &equality.left,
            &equality.right,
        ) {
            return Err(
                "integral-polynomial evidence does not reproduce its exact identity".into(),
            );
        }
        let source_to_numeric = |object: &Obj| -> Result<(String, String, String), String> {
            let source = render_obj(object, &self.environment_stack)?;
            let numeric = render_numeric_obj(object, &self.environment_stack)?;
            if source == numeric {
                return Ok((
                    source.clone(),
                    numeric,
                    format!("Litex.Same.refl ({source})"),
                ));
            }
            let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
                LeanTargetObjectRepresentation::lower(object)?
            else {
                return Err(format!(
                    "integral-polynomial endpoint `{source}` changed to `{numeric}` without a structural Same bridge"
                ));
            };
            let bridge = self
                .environment_stack
                .numeric_representation_equalities
                .get(&symbol_id)
                .cloned()
                .ok_or_else(|| {
                    format!(
                        "integral-polynomial endpoint `{source}` has no exact numeric Same bridge"
                    )
                })?;
            Ok((source, numeric, bridge))
        };
        let (_source_left, numeric_left, left_bridge) = source_to_numeric(&equality.left)?;
        let (_source_right, numeric_right, right_bridge) = source_to_numeric(&equality.right)?;
        let native =
            format!("(show {numeric_left} = {numeric_right} from (by norm_cast <;> ring_nf))");
        Ok(Some(format!(
            "Litex.Same.trans ({left_bridge}) (Litex.Same.trans (Litex.Same.ofEq ({native})) (Litex.Same.symm ({right_bridge})))"
        )))
    }
}
