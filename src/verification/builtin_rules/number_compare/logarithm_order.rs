//! Logarithm order rules.

use super::*;

impl Runtime {
    // Logarithm order rules:
    // - base > 1 preserves order on positive arguments
    // - 0 < base < 1 reverses order on positive arguments
    // - with base > 1, log_a(x) is positive for x > 1 and negative for 0 < x < 1
    // Examples:
    // `forall a, x, y R+: a > 1, x < y =>: log(a, x) < log(a, y)`
    // `forall a, x R+: a > 1, x < 1 =>: log(a, x) < 0`
    pub(in crate::verification) fn verify_log_order_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
            return Ok(None);
        };
        let one = Self::literal_one_obj();
        let zero = Self::literal_zero_obj();

        if let AtomicFact::LessFact(f) = &norm {
            match (&f.left, &f.right) {
                (Obj::Log(left_log), Obj::Log(right_log)) => {
                    let same_base_fact = self.new_equal_fact_from_refs(
                        left_log.base.as_ref(),
                        right_log.base.as_ref(),
                        f.line_file.clone(),
                    );
                    let same_base = self.verify_equal_fact_by_known_equality(&same_base_fact);
                    if !same_base.is_success() {
                        return Ok(None);
                    }
                    let same_base = self.complete_fact_proof_result(
                        &same_base_fact.into(),
                        same_base,
                        builtin_state.verify_state(),
                    )?;

                    let base_gt_one: AtomicFact = self
                        .new_less_fact(
                            one.clone(),
                            left_log.base.as_ref().clone(),
                            f.line_file.clone(),
                        )
                        .into();
                    let base_lt_one: AtomicFact = self
                        .new_less_fact(
                            left_log.base.as_ref().clone(),
                            one.clone(),
                            f.line_file.clone(),
                        )
                        .into();
                    let forward_args: AtomicFact = self
                        .new_less_fact(
                            left_log.arg.as_ref().clone(),
                            right_log.arg.as_ref().clone(),
                            f.line_file.clone(),
                        )
                        .into();
                    let reversed_args: AtomicFact = self
                        .new_less_fact(
                            right_log.arg.as_ref().clone(),
                            left_log.arg.as_ref().clone(),
                            f.line_file.clone(),
                        )
                        .into();

                    let base_gt_one_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                        &base_gt_one,
                        builtin_state,
                    )?;
                    if let Some(base_gt_one_result) = base_gt_one_result {
                        let args_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                            &forward_args,
                            builtin_state,
                        )?;
                        if let Some(args_result) = args_result {
                            return Ok(Some(ProveFactResult::from(
                                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                    atomic_fact.clone().into(),
                                    "log order: base > 1 preserves strict order".to_string(),
                                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyLogOrderBuiltinRule01),
                                    vec![same_base, base_gt_one_result, args_result],
                                ),
                            )));
                        }
                    }

                    let base_lt_one_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                        &base_lt_one,
                        builtin_state,
                    )?;
                    if let Some(base_lt_one_result) = base_lt_one_result {
                        let args_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                            &reversed_args,
                            builtin_state,
                        )?;
                        if let Some(args_result) = args_result {
                            return Ok(Some(ProveFactResult::from(
                                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                                    atomic_fact.clone().into(),
                                    "log order: 0 < base < 1 reverses strict order".to_string(),
                                    BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyLogOrderBuiltinRule02),
                                    vec![same_base, base_lt_one_result, args_result],
                                ),
                            )));
                        }
                    }
                }
                (Obj::Number(left_number), Obj::Log(log))
                    if left_number.normalized_value == "0" =>
                {
                    let base_gt_one: AtomicFact = self
                        .new_less_fact(one.clone(), log.base.as_ref().clone(), f.line_file.clone())
                        .into();
                    let arg_gt_one: AtomicFact = self
                        .new_less_fact(one.clone(), log.arg.as_ref().clone(), f.line_file.clone())
                        .into();
                    let Some(base_gt_one_result) = self
                        .try_verify_atomic_fact_as_builtin_rule_premise(
                            &base_gt_one,
                            builtin_state,
                        )?
                    else {
                        return Ok(None);
                    };
                    let arg_gt_one_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                        &arg_gt_one,
                        builtin_state,
                    )?;
                    let Some(arg_gt_one_result) = arg_gt_one_result else {
                        return Ok(None);
                    };
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "log sign: 0 < log(a, x) from 1 < a and 1 < x".to_string(),
                            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyLogOrderBuiltinRule03),
                            vec![base_gt_one_result, arg_gt_one_result],
                        ),
                    )));
                }
                (Obj::Log(log), Obj::Number(right_number))
                    if right_number.normalized_value == "0" =>
                {
                    let base_gt_one: AtomicFact = self
                        .new_less_fact(one, log.base.as_ref().clone(), f.line_file.clone())
                        .into();
                    let arg_lt_one: AtomicFact = self
                        .new_less_fact(
                            log.arg.as_ref().clone(),
                            Self::literal_one_obj(),
                            f.line_file.clone(),
                        )
                        .into();
                    let arg_positive: AtomicFact = self
                        .new_less_fact(zero, log.arg.as_ref().clone(), f.line_file.clone())
                        .into();
                    let Some(base_gt_one_result) = self
                        .try_verify_atomic_fact_as_builtin_rule_premise(
                            &base_gt_one,
                            builtin_state,
                        )?
                    else {
                        return Ok(None);
                    };
                    let arg_lt_one_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                        &arg_lt_one,
                        builtin_state,
                    )?;
                    let Some(arg_lt_one_result) = arg_lt_one_result else {
                        return Ok(None);
                    };
                    let arg_positive_result = self.try_verify_atomic_fact_as_builtin_rule_premise(
                        &arg_positive,
                        builtin_state,
                    )?;
                    let Some(arg_positive_result) = arg_positive_result else {
                        return Ok(None);
                    };
                    return Ok(Some(ProveFactResult::from(
                        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                            atomic_fact.clone().into(),
                            "log sign: log(a, x) < 0 from 1 < a and 0 < x < 1".to_string(),
                            BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyLogOrderBuiltinRule04),
                            vec![base_gt_one_result, arg_lt_one_result, arg_positive_result],
                        ),
                    )));
                }
                _ => {}
            }
        }

        Ok(None)
    }
}
