//! Sign reversal and equivalent negated order facts.

use super::*;

impl Runtime {
    // Negation reverses order; it also specializes to sign facts at zero.
    // Example: `x < -5` implies `-x > 5`.
    pub(in crate::verification) fn try_verify_order_opposite_sign_mul_minus_one(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let z: Obj = Number::new("0".to_string()).into();
        let success = |msg: &'static str, premise: VerifyFactResult| {
            Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    msg.to_string(),
                    BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::NegateOrder),
                    vec![premise],
                ),
            )))
        };
        match atomic_fact {
            AtomicFact::GreaterFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact = self
                        .new_less_fact(x, negative_right, f.line_file.clone())
                        .into();
                    if let Some(premise) = self
                        .try_verify_atomic_fact_as_builtin_rule_premise(&reverse, builtin_state)?
                    {
                        return success("order: -x > y from x < -y", premise);
                    }
                }
            }
            AtomicFact::GreaterEqualFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact = self
                        .new_less_equal_fact(x, negative_right, f.line_file.clone())
                        .into();
                    if let Some(premise) = self
                        .try_verify_atomic_fact_as_builtin_rule_premise(&reverse, builtin_state)?
                    {
                        return success("order: -x >= y from x <= -y", premise);
                    }
                }
            }
            AtomicFact::LessFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact = self
                        .new_greater_fact(x, negative_right, f.line_file.clone())
                        .into();
                    if let Some(premise) = self
                        .try_verify_atomic_fact_as_builtin_rule_premise(&reverse, builtin_state)?
                    {
                        return success("order: -x < y from x > -y", premise);
                    }
                }
            }
            AtomicFact::LessEqualFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact = self
                        .new_greater_equal_fact(x, negative_right, f.line_file.clone())
                        .into();
                    if let Some(premise) = self
                        .try_verify_atomic_fact_as_builtin_rule_premise(&reverse, builtin_state)?
                    {
                        return success("order: -x <= y from x >= -y", premise);
                    }
                }
            }
            _ => {}
        }
        match atomic_fact {
            AtomicFact::GreaterEqualFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let le: AtomicFact = self
                        .new_less_equal_fact(x.clone(), z.clone(), f.line_file.clone())
                        .into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&le, builtin_state)?
                    {
                        return success("order: (-1)*x >= 0 from x <= 0", premise);
                    }
                    let lt: AtomicFact =
                        self.new_less_fact(x, z.clone(), f.line_file.clone()).into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&lt, builtin_state)?
                    {
                        return success("order: (-1)*x >= 0 from x < 0", premise);
                    }
                }
                Ok(None)
            }
            AtomicFact::GreaterFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let lt: AtomicFact =
                        self.new_less_fact(x, z.clone(), f.line_file.clone()).into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&lt, builtin_state)?
                    {
                        return success("order: (-1)*x > 0 from x < 0", premise);
                    }
                }
                Ok(None)
            }
            AtomicFact::LessEqualFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let ge: AtomicFact = self
                        .new_greater_equal_fact(x.clone(), z.clone(), f.line_file.clone())
                        .into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&ge, builtin_state)?
                    {
                        return success("order: (-1)*x <= 0 from x >= 0", premise);
                    }
                    let gt: AtomicFact = self
                        .new_greater_fact(x, z.clone(), f.line_file.clone())
                        .into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&gt, builtin_state)?
                    {
                        return success("order: (-1)*x <= 0 from x > 0", premise);
                    }
                }
                Ok(None)
            }
            AtomicFact::LessFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let gt: AtomicFact = self
                        .new_greater_fact(x, z.clone(), f.line_file.clone())
                        .into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&gt, builtin_state)?
                    {
                        return success("order: (-1)*x < 0 from x > 0", premise);
                    }
                }
                Ok(None)
            }
            AtomicFact::LessEqualFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let le: AtomicFact = self
                        .new_less_equal_fact(x.clone(), z.clone(), f.line_file.clone())
                        .into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&le, builtin_state)?
                    {
                        return success("order: 0 <= (-1)*x from x <= 0", premise);
                    }
                    let lt: AtomicFact =
                        self.new_less_fact(x, z.clone(), f.line_file.clone()).into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&lt, builtin_state)?
                    {
                        return success("order: 0 <= (-1)*x from x < 0", premise);
                    }
                }
                Ok(None)
            }
            AtomicFact::LessFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let lt: AtomicFact =
                        self.new_less_fact(x, z.clone(), f.line_file.clone()).into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&lt, builtin_state)?
                    {
                        return success("order: 0 < (-1)*x from x < 0", premise);
                    }
                }
                Ok(None)
            }
            AtomicFact::GreaterEqualFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let ge: AtomicFact = self
                        .new_greater_equal_fact(x.clone(), z.clone(), f.line_file.clone())
                        .into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&ge, builtin_state)?
                    {
                        return success("order: 0 >= (-1)*x from x >= 0", premise);
                    }
                    let gt: AtomicFact = self
                        .new_greater_fact(x, z.clone(), f.line_file.clone())
                        .into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&gt, builtin_state)?
                    {
                        return success("order: 0 >= (-1)*x from x > 0", premise);
                    }
                }
                Ok(None)
            }
            AtomicFact::GreaterFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let gt: AtomicFact = self
                        .new_greater_fact(x, z.clone(), f.line_file.clone())
                        .into();
                    if let Some(premise) =
                        self.try_verify_atomic_fact_as_builtin_rule_premise(&gt, builtin_state)?
                    {
                        return success("order: 0 > (-1)*x from x > 0", premise);
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    // `a > b` from known `not (a <= b)`, `a < b` from `not (a >= b)`, etc. (total order duality).
    pub(in crate::verification) fn verify_order_from_known_negated_complement(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (neg, left, right, line_file) = match atomic_fact {
            AtomicFact::GreaterFact(f) => (
                self.new_not_less_equal_fact(f.left.clone(), f.right.clone(), f.line_file.clone())
                    .into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            AtomicFact::LessFact(f) => (
                self.new_not_greater_equal_fact(
                    f.left.clone(),
                    f.right.clone(),
                    f.line_file.clone(),
                )
                .into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            AtomicFact::GreaterEqualFact(f) => (
                self.new_not_less_fact(f.left.clone(), f.right.clone(), f.line_file.clone())
                    .into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            AtomicFact::LessEqualFact(f) => (
                self.new_not_greater_fact(f.left.clone(), f.right.clone(), f.line_file.clone())
                    .into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            _ => return Ok(None),
        };
        let Some(mut steps) = self.verify_objects_are_known_reals_in_builtin(
            &[&left, &right],
            &line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        if let Some(sub) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&neg, builtin_state)?
        {
            steps.push(sub);
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    atomic_fact.clone().into(),
                    SuccessInferResult::new(),
                    "order_from_known_negated_complement".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyOrderFromKnownNegatedComplement,
                    ),
                    steps,
                )
                .into(),
            ));
        }
        Ok(None)
    }

    // `not (a < b)` etc.: only consult known atomic facts for the equivalent weak/strict order.
    pub(in crate::verification) fn verify_negated_order_from_known_equivalent_order(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (left, right, line_file) = match atomic_fact {
            AtomicFact::NotLessFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::NotGreaterFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::NotLessEqualFact(f) => {
                (f.left.clone(), f.right.clone(), f.line_file.clone())
            }
            AtomicFact::NotGreaterEqualFact(f) => {
                (f.left.clone(), f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let Some(mut steps) = self.verify_objects_are_known_reals_in_builtin(
            &[&left, &right],
            &line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let candidates: Vec<AtomicFact> = match atomic_fact {
            AtomicFact::NotLessFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    self.new_less_equal_fact(f.right.clone(), f.left.clone(), lf.clone())
                        .into(),
                    self.new_greater_equal_fact(f.left.clone(), f.right.clone(), lf)
                        .into(),
                ]
            }
            AtomicFact::NotGreaterFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    self.new_less_equal_fact(f.left.clone(), f.right.clone(), lf.clone())
                        .into(),
                    self.new_greater_equal_fact(f.right.clone(), f.left.clone(), lf)
                        .into(),
                ]
            }
            AtomicFact::NotLessEqualFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    self.new_less_fact(f.right.clone(), f.left.clone(), lf.clone())
                        .into(),
                    self.new_greater_fact(f.left.clone(), f.right.clone(), lf)
                        .into(),
                ]
            }
            AtomicFact::NotGreaterEqualFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    self.new_less_fact(f.left.clone(), f.right.clone(), lf.clone())
                        .into(),
                    self.new_greater_fact(f.right.clone(), f.left.clone(), lf)
                        .into(),
                ]
            }
            _ => return Ok(None),
        };
        for candidate in &candidates {
            if let Some(sub) =
                self.try_verify_atomic_fact_as_builtin_rule_premise(candidate, builtin_state)?
            {
                steps.push(sub);
                return Ok(Some(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                        atomic_fact.clone().into(),
                        SuccessInferResult::new(),
                        "negated_order_from_known_equivalent_order".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(
                            UncataloguedBuiltinRule::VerifyNegatedOrderFromKnownEquivalentOrder01,
                        ),
                        steps,
                    )
                    .into(),
                ));
            }
        }

        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            candidates
                .into_iter()
                .map(|candidate| vec![candidate])
                .collect(),
            line_file,
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            steps.push(premise_result);
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_and_steps(
                    atomic_fact.clone().into(),
                    SuccessInferResult::new(),
                    "negated_order_from_complete_equivalent_order_disjunction".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::VerifyNegatedOrderFromKnownEquivalentOrder02,
                    ),
                    steps,
                )
                .into(),
            ));
        }
        Ok(None)
    }
}
