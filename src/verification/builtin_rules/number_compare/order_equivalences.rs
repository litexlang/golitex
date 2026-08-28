//! Sign reversal and equivalent negated order facts.

use super::*;

impl Runtime {
    // Negation reverses order; it also specializes to sign facts at zero.
    // Example: `x < -5` implies `-x > 5`.
    pub(in crate::verification) fn try_verify_order_opposite_sign_mul_minus_one(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z: Obj = Number::new("0".to_string()).into();
        let success = |msg: &'static str| {
            Ok(Some(StmtResult::from(
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    msg.to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyOrderOppositeSignMulMinusOne,
                    ),
                    Vec::new(),
                ),
            )))
        };
        match atomic_fact {
            AtomicFact::GreaterFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact =
                        LessFact::new(x, negative_right, f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&reverse, builtin_state)?
                        .is_success()
                    {
                        return success("order: -x > y from x < -y");
                    }
                }
            }
            AtomicFact::GreaterEqualFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact =
                        LessEqualFact::new(x, negative_right, f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&reverse, builtin_state)?
                        .is_success()
                    {
                        return success("order: -x >= y from x <= -y");
                    }
                }
            }
            AtomicFact::LessFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact =
                        GreaterFact::new(x, negative_right, f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&reverse, builtin_state)?
                        .is_success()
                    {
                        return success("order: -x < y from x > -y");
                    }
                }
            }
            AtomicFact::LessEqualFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact =
                        GreaterEqualFact::new(x, negative_right, f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&reverse, builtin_state)?
                        .is_success()
                    {
                        return success("order: -x <= y from x >= -y");
                    }
                }
            }
            _ => {}
        }
        match atomic_fact {
            AtomicFact::GreaterEqualFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let le: AtomicFact =
                        LessEqualFact::new(x.clone(), z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&le, builtin_state)?
                        .is_success()
                    {
                        return success("order: (-1)*x >= 0 from x <= 0");
                    }
                    let lt: AtomicFact = LessFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&lt, builtin_state)?
                        .is_success()
                    {
                        return success("order: (-1)*x >= 0 from x < 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::GreaterFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let lt: AtomicFact = LessFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&lt, builtin_state)?
                        .is_success()
                    {
                        return success("order: (-1)*x > 0 from x < 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::LessEqualFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let ge: AtomicFact =
                        GreaterEqualFact::new(x.clone(), z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&ge, builtin_state)?
                        .is_success()
                    {
                        return success("order: (-1)*x <= 0 from x >= 0");
                    }
                    let gt: AtomicFact = GreaterFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&gt, builtin_state)?
                        .is_success()
                    {
                        return success("order: (-1)*x <= 0 from x > 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::LessFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let gt: AtomicFact = GreaterFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&gt, builtin_state)?
                        .is_success()
                    {
                        return success("order: (-1)*x < 0 from x > 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::LessEqualFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let le: AtomicFact =
                        LessEqualFact::new(x.clone(), z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&le, builtin_state)?
                        .is_success()
                    {
                        return success("order: 0 <= (-1)*x from x <= 0");
                    }
                    let lt: AtomicFact = LessFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&lt, builtin_state)?
                        .is_success()
                    {
                        return success("order: 0 <= (-1)*x from x < 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::LessFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let lt: AtomicFact = LessFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&lt, builtin_state)?
                        .is_success()
                    {
                        return success("order: 0 < (-1)*x from x < 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::GreaterEqualFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let ge: AtomicFact =
                        GreaterEqualFact::new(x.clone(), z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&ge, builtin_state)?
                        .is_success()
                    {
                        return success("order: 0 >= (-1)*x from x >= 0");
                    }
                    let gt: AtomicFact = GreaterFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&gt, builtin_state)?
                        .is_success()
                    {
                        return success("order: 0 >= (-1)*x from x > 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::GreaterFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let gt: AtomicFact = GreaterFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_atomic_fact_as_builtin_rule_premise(&gt, builtin_state)?
                        .is_success()
                    {
                        return success("order: 0 > (-1)*x from x > 0");
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
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (neg, left, right, line_file) = match atomic_fact {
            AtomicFact::GreaterFact(f) => (
                NotLessEqualFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            AtomicFact::LessFact(f) => (
                NotGreaterEqualFact::new(f.left.clone(), f.right.clone(), f.line_file.clone())
                    .into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            AtomicFact::GreaterEqualFact(f) => (
                NotLessFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            AtomicFact::LessEqualFact(f) => (
                NotGreaterFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into(),
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
        let sub = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&neg)?;
        if sub.is_success() {
            steps.push(sub);
            return Ok(Some(
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_and_steps(
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
    ) -> Result<Option<StmtResult>, RuntimeError> {
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
                    LessEqualFact::new(f.right.clone(), f.left.clone(), lf.clone()).into(),
                    GreaterEqualFact::new(f.left.clone(), f.right.clone(), lf).into(),
                ]
            }
            AtomicFact::NotGreaterFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    LessEqualFact::new(f.left.clone(), f.right.clone(), lf.clone()).into(),
                    GreaterEqualFact::new(f.right.clone(), f.left.clone(), lf).into(),
                ]
            }
            AtomicFact::NotLessEqualFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    LessFact::new(f.right.clone(), f.left.clone(), lf.clone()).into(),
                    GreaterFact::new(f.left.clone(), f.right.clone(), lf).into(),
                ]
            }
            AtomicFact::NotGreaterEqualFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    LessFact::new(f.left.clone(), f.right.clone(), lf.clone()).into(),
                    GreaterFact::new(f.right.clone(), f.left.clone(), lf).into(),
                ]
            }
            _ => return Ok(None),
        };
        for candidate in &candidates {
            let sub = self.verify_non_equational_atomic_fact_with_known_atomic_facts(candidate)?;
            if sub.is_success() {
                steps.push(sub);
                return Ok(Some(
                    SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_and_steps(
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

        let premise_result = self.verify_builtin_rule_premise_alternatives(
            candidates
                .into_iter()
                .map(|candidate| vec![candidate])
                .collect(),
            line_file,
            builtin_state,
        )?;
        if premise_result.is_success() {
            steps.push(premise_result);
            return Ok(Some(
                SuccessFactStmtResult::new_with_verified_by_builtin_rule_evidence_and_steps(
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
