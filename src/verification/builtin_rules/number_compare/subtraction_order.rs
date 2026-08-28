//! Order facts bridged through subtraction.

use super::*;

impl Runtime {
    pub(in crate::verification) fn verify_zero_order_on_sub_expr(
        &mut self,
        zero: &Obj,
        sub_expr: &Obj,
        weak: bool,
        parent_weak: bool,
        line_file: &LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        let fact: AtomicFact = if weak {
            LessEqualFact::new(zero.clone(), sub_expr.clone(), line_file.clone()).into()
        } else {
            LessFact::new(zero.clone(), sub_expr.clone(), line_file.clone()).into()
        };
        if weak == parent_weak {
            self.verify_atomic_fact_as_builtin_rule_premise(&fact, builtin_state)
        } else {
            self.verify_atomic_fact_as_builtin_rule_premise(&fact, builtin_state)
        }
    }

    // Moves a known difference bound back to the corresponding order fact.
    // Examples: from `a - b <= 0` or `0 <= b - a`, prove `a <= b`.
    pub(in crate::verification) fn verify_order_from_known_zero_order_on_sub_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let (left, right, is_weak, line_file) = match normalized_fact {
            AtomicFact::LessEqualFact(f) => (f.left, f.right, true, f.line_file),
            AtomicFact::LessFact(f) => (f.left, f.right, false, f.line_file),
            _ => return Ok(None),
        };

        let zero = Self::literal_zero_obj();
        let direct_difference: Obj = Sub::new(left.clone(), right.clone()).into();
        let direct_difference_order: AtomicFact = if is_weak {
            LessEqualFact::new(direct_difference, zero.clone(), line_file.clone()).into()
        } else {
            LessFact::new(direct_difference, zero.clone(), line_file.clone()).into()
        };
        let direct_difference_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&direct_difference_order)?;
        if direct_difference_result.is_success() {
            let reason = if is_weak {
                "a <= b from a - b <= 0"
            } else {
                "a < b from a - b < 0"
            };
            return Ok(Some(
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    reason.to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyOrderFromKnownZeroOrderOnSubBuiltinRule01,
                    ),
                    vec![direct_difference_result],
                )
                .into(),
            ));
        }

        let difference: Obj = Sub::new(right, left).into();
        let difference_order: AtomicFact = if is_weak {
            LessEqualFact::new(zero, difference, line_file.clone()).into()
        } else {
            LessFact::new(zero, difference, line_file.clone()).into()
        };
        let difference_result =
            self.verify_non_equational_atomic_fact_with_known_atomic_facts(&difference_order)?;
        if difference_result.is_success() {
            let reason = if is_weak {
                "a <= b from 0 <= b - a"
            } else {
                "a < b from 0 < b - a"
            };
            return Ok(Some(
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    reason.to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyOrderFromKnownZeroOrderOnSubBuiltinRule02,
                    ),
                    vec![difference_result],
                )
                .into(),
            ));
        }

        let premise_result = self.verify_builtin_rule_premise_alternatives(
            vec![vec![direct_difference_order], vec![difference_order]],
            line_file,
            builtin_state,
        )?;
        if premise_result.is_success() {
            return Ok(Some(
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "order from complete zero-difference-bound disjunction".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyOrderFromKnownZeroOrderOnSubBuiltinRule03,
                    ),
                    vec![premise_result],
                )
                .into(),
            ));
        }

        Ok(None)
    }

    // Matches Lit `a <= b` <=> `0 <= b - a` (and strict): `0 <= u - v` iff `v <= u`, `0 < u - v` iff `v < u`.
    pub(in crate::verification) fn verify_zero_order_on_sub_from_two_sided_order_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        match &norm {
            AtomicFact::LessEqualFact(f) if f.left.to_string() == "0" => {
                let Obj::Sub(sub) = &f.right else {
                    return Ok(None);
                };
                let derived: AtomicFact = LessEqualFact::new(
                    sub.right.as_ref().clone(),
                    sub.left.as_ref().clone(),
                    f.line_file.clone(),
                )
                .into();
                let result =
                    self.verify_atomic_fact_as_builtin_rule_premise(&derived, builtin_state)?;
                if result.is_success() {
                    Ok(Some(StmtResult::from(
                        SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "0 <= u - v from v <= u".to_string(),
                            BuiltinRuleEvidence::Arithmetic(
                                ArithmeticBuiltinRule::SubNonnegativeFromLessEqual,
                            ),
                            vec![result],
                        ),
                    )))
                } else {
                    Ok(None)
                }
            }
            AtomicFact::LessFact(f) if f.left.to_string() == "0" => {
                let Obj::Sub(sub) = &f.right else {
                    return Ok(None);
                };
                let derived: AtomicFact = LessFact::new(
                    sub.right.as_ref().clone(),
                    sub.left.as_ref().clone(),
                    f.line_file.clone(),
                )
                .into();
                let result =
                    self.verify_atomic_fact_as_builtin_rule_premise(&derived, builtin_state)?;
                if result.is_success() {
                    Ok(Some(StmtResult::from(
                        SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "0 < u - v from v < u".to_string(),
                            BuiltinRuleEvidence::Arithmetic(
                                ArithmeticBuiltinRule::SubPositiveFromLess,
                            ),
                            vec![result],
                        ),
                    )))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }
}
