//! Modulo remainder order bounds.

use super::*;

impl Runtime {
    /// Euclidean remainders modulo a positive integer lie in the standard interval.
    /// Example: from `a $in Z` and `b $in N+`, prove `0 <= a % b < b`.
    pub(in crate::verification) fn try_verify_mod_remainder_bounds(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
            return Ok(None);
        };
        let (mod_obj, line_file, strict_upper_bound) = match &norm {
            AtomicFact::LessEqualFact(f) => {
                let Some(zero) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_normalized_number_str_to_zero(&zero.normalized_value),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                let Obj::Mod(m) = &f.right else {
                    return Ok(None);
                };
                (m, f.line_file.clone(), false)
            }
            AtomicFact::LessFact(f) => {
                let Obj::Mod(m) = &f.left else {
                    return Ok(None);
                };
                if m.right.to_string() != f.right.to_string() {
                    return Ok(None);
                }
                (m, f.line_file.clone(), true)
            }
            _ => return Ok(None),
        };

        let dividend_in_z: AtomicFact = self
            .new_in_fact(
                mod_obj.left.as_ref().clone(),
                StandardSet::Z.into(),
                line_file.clone(),
            )
            .into();
        let Some(dividend_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&dividend_in_z, builtin_state)?
        else {
            return Ok(None);
        };

        let modulus_in_n_pos: AtomicFact = self
            .new_in_fact(
                mod_obj.right.as_ref().clone(),
                StandardSet::NPos.into(),
                line_file,
            )
            .into();
        let Some(modulus_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&modulus_in_n_pos, builtin_state)?
        else {
            return Ok(None);
        };

        let reason = if strict_upper_bound {
            "mod remainder upper bound: a % b < b for a in Z and b in N+"
        } else {
            "mod remainder nonnegative: 0 <= a % b for a in Z and b in N+"
        };
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                reason.to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyModRemainderBounds,
                ),
                vec![dividend_result, modulus_result],
            ),
        )))
    }
}
