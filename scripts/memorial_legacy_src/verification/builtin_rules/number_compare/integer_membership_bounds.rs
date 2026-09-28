//! Natural and integer membership lower bounds.

use super::*;

impl Runtime {
    /// `n >= 0` / `0 <= n` from known `n $in N` (e.g. `forall n N:` domain).
    pub(in crate::verification) fn try_verify_order_nonnegative_from_membership_in_n(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (n, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                let Some(z) = self.resolve_obj_to_number(&f.right) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_normalized_number_str_to_zero(&z.normalized_value),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.left.clone(), f.line_file.clone())
            }
            AtomicFact::LessEqualFact(f) => {
                let Some(z) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_normalized_number_str_to_zero(&z.normalized_value),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let in_n: AtomicFact = self
            .new_in_fact(n, StandardSet::N.into(), line_file.clone())
            .into();
        let in_n_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_n, builtin_state)?;
        if let Some(in_n_result) = in_n_result {
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "n >= 0 from n $in N".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyOrderNonnegativeFromMembershipInN,
                    ),
                    vec![in_n_result],
                ),
            )));
        }
        Ok(None)
    }

    /// `n >= 1` / `1 <= n` from known `n $in N+`.
    pub(in crate::verification) fn try_verify_order_one_le_from_membership_in_n_pos(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (n, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.right) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.left.clone(), f.line_file.clone())
            }
            AtomicFact::LessEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let in_n_pos: AtomicFact = self
            .new_in_fact(n, StandardSet::NPos.into(), line_file.clone())
            .into();
        let in_n_pos_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_n_pos, builtin_state)?;
        if let Some(in_n_pos_result) = in_n_pos_result {
            return Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "n >= 1 from n $in N+".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyOrderOneLeFromMembershipInNPos,
                    ),
                    vec![in_n_pos_result],
                ),
            )));
        }
        Ok(None)
    }

    /// `n >= 1` / `1 <= n` from known `n $in N` and `n != 0` (nonzero naturals are at least 1).
    /// Example: `forall x N: x != 0 =>: 1 <= x`.
    pub(in crate::verification) fn try_verify_order_one_le_from_membership_in_n_and_nonzero(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (n, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.right) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.left.clone(), f.line_file.clone())
            }
            AtomicFact::LessEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let in_n: AtomicFact = self
            .new_in_fact(n.clone(), StandardSet::N.into(), line_file.clone())
            .into();
        let nonzero: AtomicFact = self
            .new_not_equal_fact(n.clone(), zero_obj, line_file.clone())
            .into();
        let mut in_n_result =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_n, builtin_state)?;
        if in_n_result.is_none() {
            if let Obj::FiniteSetSize(finite_set_size) = &n {
                let in_n_fact =
                    self.new_in_fact(n.clone(), StandardSet::N.into(), line_file.clone());
                let proof = self.verify_finite_set_size_in_standard_number_set(
                    &in_n_fact,
                    finite_set_size,
                    builtin_state,
                )?;
                in_n_result = Some(self.complete_atomic_fact_proof_result(
                    &in_n,
                    proof,
                    builtin_state.verify_state(),
                )?);
            }
        }
        let Some(in_n_result) = in_n_result else {
            return Ok(None);
        };
        let nonzero_result =
            self.verify_atomic_except_equality_with_known_atomic_facts(&nonzero)?;
        if !nonzero_result.is_success() {
            return Ok(None);
        }
        let nonzero_result = self.complete_atomic_fact_proof_result(
            &nonzero,
            nonzero_result,
            builtin_state.verify_state(),
        )?;
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "1 <= n from n $in N and n != 0".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyOrderOneLeFromMembershipInNAndNonzero,
                ),
                vec![in_n_result, nonzero_result],
            ),
        )))
    }

    /// `n >= 1` / `1 <= n` from known `n $in Z` and `0 < n`.
    pub(in crate::verification) fn try_verify_order_one_le_from_membership_in_z_and_positive(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (n, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.right) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.left.clone(), f.line_file.clone())
            }
            AtomicFact::LessEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let in_z: AtomicFact = self
            .new_in_fact(n.clone(), StandardSet::Z.into(), line_file.clone())
            .into();
        let positive: AtomicFact = self.new_less_fact(zero_obj, n, line_file.clone()).into();
        let Some(in_z_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_z, builtin_state)?
        else {
            return Ok(None);
        };
        let Some(positive_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&positive, builtin_state)?
        else {
            return Ok(None);
        };
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "1 <= n from n $in Z and 0 < n".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyOrderOneLeFromMembershipInZAndPositive,
                ),
                vec![in_z_result, positive_result],
            ),
        )))
    }
}
