use crate::prelude::*;
use crate::verify::verify_builtin_rules::normalize_positive_order_atomic_fact;

impl Runtime {
    // Descends through nested additions while preserving weak or strict positivity.
    // Example: from nonnegative `a, b, c, d`, prove `0 <= (a + b) + (c + d)`.
    pub(crate) fn verify_additive_sign_with_builtin_strategy(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let Some(normalized) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(StmtUnknown::new().into());
        };
        if normalized.to_string() != atomic_fact.to_string() {
            let normalized_result = self
                .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                    &normalized,
                )?;
            if normalized_result.is_true() {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                        atomic_fact.clone().into(),
                        "additive sign strategy: normalized order goal".to_string(),
                        vec![normalized_result],
                    )
                    .into(),
                );
            }
        }
        if let Some(children) = self.verify_structural_order_strategy(&normalized)? {
            return Ok(
                FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                    atomic_fact.clone().into(),
                    "numeric-order strategy: structurally smaller order goals".to_string(),
                    children,
                )
                .into(),
            );
        }
        match normalized {
            AtomicFact::LessEqualFact(fact) if fact.left.to_string() == "0" => {
                let Obj::Add(add) = &fact.right else {
                    return Ok(StmtUnknown::new().into());
                };
                let left = self.verify_additive_sign_strategy_child(
                    add.left.as_ref(),
                    true,
                    &fact.line_file,
                )?;
                if !left.is_true() {
                    return Ok(StmtUnknown::new().into());
                }
                let right = self.verify_additive_sign_strategy_child(
                    add.right.as_ref(),
                    true,
                    &fact.line_file,
                )?;
                if !right.is_true() {
                    return Ok(StmtUnknown::new().into());
                }
                Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                        atomic_fact.clone().into(),
                        "additive sign strategy: nonnegative summands".to_string(),
                        vec![left, right],
                    )
                    .into(),
                )
            }
            AtomicFact::LessFact(fact) if fact.left.to_string() == "0" => {
                let Obj::Add(add) = &fact.right else {
                    return Ok(StmtUnknown::new().into());
                };
                if let Some(children) = self.verify_strict_additive_strategy_children(
                    add.left.as_ref(),
                    add.right.as_ref(),
                    &fact.line_file,
                )? {
                    return Ok(
                        FactualStmtSuccess::new_with_verified_by_builtin_strategy_recording_stmt(
                            atomic_fact.clone().into(),
                            "additive sign strategy: one positive and one nonnegative summand"
                                .to_string(),
                            children,
                        )
                        .into(),
                    );
                }
                Ok(StmtUnknown::new().into())
            }
            _ => Ok(StmtUnknown::new().into()),
        }
    }

    fn verify_strict_additive_strategy_children(
        &mut self,
        left: &Obj,
        right: &Obj,
        line_file: &LineFile,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let left_strict = self.verify_additive_sign_strategy_child(left, false, line_file)?;
        if left_strict.is_true() {
            let right_weak = self.verify_additive_sign_strategy_child(right, true, line_file)?;
            if right_weak.is_true() {
                return Ok(Some(vec![left_strict, right_weak]));
            }
        }

        let left_weak = self.verify_additive_sign_strategy_child(left, true, line_file)?;
        if !left_weak.is_true() {
            return Ok(None);
        }
        let right_strict = self.verify_additive_sign_strategy_child(right, false, line_file)?;
        if right_strict.is_true() {
            Ok(Some(vec![left_weak, right_strict]))
        } else {
            Ok(None)
        }
    }

    fn verify_additive_sign_strategy_child(
        &mut self,
        obj: &Obj,
        weak: bool,
        line_file: &LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        let zero: Obj = Number::new("0".to_string()).into();
        let child: AtomicFact = if weak {
            LessEqualFact::new(zero, obj.clone(), line_file.clone()).into()
        } else {
            LessFact::new(zero, obj.clone(), line_file.clone()).into()
        };
        let direct =
            self.verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(&child)?;
        if direct.is_true() {
            return Ok(direct);
        }
        self.verify_additive_sign_with_builtin_strategy(&child)
    }

    fn verify_structural_order_strategy(
        &mut self,
        normalized: &AtomicFact,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        match normalized {
            AtomicFact::LessEqualFact(fact) => self.verify_weak_structural_order_strategy(fact),
            AtomicFact::LessFact(fact) => self.verify_strict_structural_order_strategy(fact),
            _ => Ok(None),
        }
    }

    fn verify_weak_structural_order_strategy(
        &mut self,
        fact: &LessEqualFact,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let zero: Obj = Number::new("0".to_string()).into();
        let one: Obj = Number::new("1".to_string()).into();
        let lf = fact.line_file.clone();
        let mut alternatives: Vec<Vec<AtomicFact>> = Vec::new();

        if fact.left.to_string() == "0" {
            if let Obj::Mul(product) = &fact.right {
                alternatives.push(vec![
                    LessEqualFact::new(zero.clone(), product.left.as_ref().clone(), lf.clone())
                        .into(),
                    LessEqualFact::new(zero.clone(), product.right.as_ref().clone(), lf.clone())
                        .into(),
                ]);
                alternatives.push(vec![
                    LessEqualFact::new(product.left.as_ref().clone(), zero.clone(), lf.clone())
                        .into(),
                    LessEqualFact::new(product.right.as_ref().clone(), zero.clone(), lf.clone())
                        .into(),
                ]);
            }
        }

        if let (Obj::Add(left), Obj::Add(right)) = (&fact.left, &fact.right) {
            alternatives.push(vec![
                LessEqualFact::new(
                    left.left.as_ref().clone(),
                    right.left.as_ref().clone(),
                    lf.clone(),
                )
                .into(),
                LessEqualFact::new(
                    left.right.as_ref().clone(),
                    right.right.as_ref().clone(),
                    lf.clone(),
                )
                .into(),
            ]);
            alternatives.push(vec![
                LessEqualFact::new(
                    left.left.as_ref().clone(),
                    right.right.as_ref().clone(),
                    lf.clone(),
                )
                .into(),
                LessEqualFact::new(
                    left.right.as_ref().clone(),
                    right.left.as_ref().clone(),
                    lf.clone(),
                )
                .into(),
            ]);
        }
        // Subtracting the same real term preserves weak order.
        // Example: from `a <= b`, prove `a - c <= b - c`.
        if let (Obj::Sub(left), Obj::Sub(right)) = (&fact.left, &fact.right) {
            if left.right.to_string() == right.right.to_string() {
                alternatives.push(vec![LessEqualFact::new(
                    left.left.as_ref().clone(),
                    right.left.as_ref().clone(),
                    lf.clone(),
                )
                .into()]);
            }
            // With a shared minuend, subtraction reverses weak order in the subtractor.
            // Example: from `c <= d`, prove `a - d <= a - c`.
            if left.left.to_string() == right.left.to_string() {
                alternatives.push(vec![LessEqualFact::new(
                    right.right.as_ref().clone(),
                    left.right.as_ref().clone(),
                    lf.clone(),
                )
                .into()]);
            }
        }
        // Division by a shared positive term preserves weak order; division by a
        // shared negative term reverses it. Example: `a <= b, 0 < c => a/c <= b/c`.
        if let (Obj::Div(left), Obj::Div(right)) = (&fact.left, &fact.right) {
            if left.right.to_string() == right.right.to_string() {
                alternatives.push(vec![
                    LessFact::new(zero.clone(), left.right.as_ref().clone(), lf.clone()).into(),
                    LessEqualFact::new(
                        left.left.as_ref().clone(),
                        right.left.as_ref().clone(),
                        lf.clone(),
                    )
                    .into(),
                ]);
                alternatives.push(vec![
                    LessFact::new(left.right.as_ref().clone(), zero.clone(), lf.clone()).into(),
                    LessEqualFact::new(
                        right.left.as_ref().clone(),
                        left.left.as_ref().clone(),
                        lf.clone(),
                    )
                    .into(),
                ]);
            }
        }
        // Positive-integer powers preserve weak order on nonnegative bases.
        // This is a strategy, rather than a direct-rule chain, so a normalized
        // base comparison such as `2 <= n` may use one fresh direct rule.
        // Example: from `n >= 1 + 1`, prove `n^2 >= 2^2`.
        if let (Obj::Pow(left), Obj::Pow(right)) = (&fact.left, &fact.right) {
            if left.exponent.to_string() == right.exponent.to_string() {
                alternatives.push(vec![
                    InFact::new(
                        left.exponent.as_ref().clone(),
                        StandardSet::NPos.into(),
                        lf.clone(),
                    )
                    .into(),
                    LessEqualFact::new(zero.clone(), left.base.as_ref().clone(), lf.clone()).into(),
                    LessEqualFact::new(
                        left.base.as_ref().clone(),
                        right.base.as_ref().clone(),
                        lf.clone(),
                    )
                    .into(),
                ]);
            }
        }
        // Absolute-value order is equivalent to square order on real operands.
        // This belongs to the structural strategy layer: the outer `abs`
        // constructors disappear, and each generated child receives one fresh
        // direct-rule attempt. Example: from `x^2 <= y^2`, prove
        // `abs(x) <= abs(y)`.
        if let (Obj::Abs(left), Obj::Abs(right)) = (&fact.left, &fact.right) {
            let two: Obj = Number::new("2".to_string()).into();
            alternatives.push(vec![
                InFact::new(left.arg.as_ref().clone(), StandardSet::R.into(), lf.clone()).into(),
                InFact::new(
                    right.arg.as_ref().clone(),
                    StandardSet::R.into(),
                    lf.clone(),
                )
                .into(),
                LessEqualFact::new(
                    Pow::new(left.arg.as_ref().clone(), two.clone()).into(),
                    Pow::new(right.arg.as_ref().clone(), two).into(),
                    lf.clone(),
                )
                .into(),
            ]);
        }
        if let Obj::Add(add) = &fact.right {
            alternatives.push(vec![
                LessEqualFact::new(fact.left.clone(), add.left.as_ref().clone(), lf.clone()).into(),
                LessEqualFact::new(zero.clone(), add.right.as_ref().clone(), lf.clone()).into(),
            ]);
            alternatives.push(vec![
                LessEqualFact::new(fact.left.clone(), add.right.as_ref().clone(), lf.clone())
                    .into(),
                LessEqualFact::new(zero.clone(), add.left.as_ref().clone(), lf.clone()).into(),
            ]);
        }
        if let Obj::Add(add) = &fact.left {
            alternatives.push(vec![
                LessEqualFact::new(add.left.as_ref().clone(), fact.right.clone(), lf.clone())
                    .into(),
                LessEqualFact::new(add.right.as_ref().clone(), zero.clone(), lf.clone()).into(),
            ]);
            alternatives.push(vec![
                LessEqualFact::new(add.right.as_ref().clone(), fact.right.clone(), lf.clone())
                    .into(),
                LessEqualFact::new(add.left.as_ref().clone(), zero.clone(), lf.clone()).into(),
            ]);
        }
        if let Obj::Sub(sub) = &fact.left {
            if fact.right.to_string() == "0" {
                alternatives.push(vec![LessEqualFact::new(
                    sub.left.as_ref().clone(),
                    sub.right.as_ref().clone(),
                    lf.clone(),
                )
                .into()]);
            }
        }
        if let Obj::Sub(sub) = &fact.right {
            if fact.left.to_string() == "0" {
                alternatives.push(vec![LessEqualFact::new(
                    sub.right.as_ref().clone(),
                    sub.left.as_ref().clone(),
                    lf.clone(),
                )
                .into()]);
            }
        }
        // Treat a bare factor as `1 * factor`.  This is the structural
        // product-monotonicity strategy behind everyday goals such as
        // `b <= a*b` from `0 <= b` and `1 <= a`.
        if let Obj::Mul(product) = &fact.right {
            for (factor, scale) in [
                (product.left.as_ref(), product.right.as_ref()),
                (product.right.as_ref(), product.left.as_ref()),
            ] {
                if factor.to_string() == fact.left.to_string() {
                    alternatives.push(vec![
                        LessEqualFact::new(zero.clone(), factor.clone(), lf.clone()).into(),
                        LessEqualFact::new(one.clone(), scale.clone(), lf.clone()).into(),
                    ]);
                }
            }
        }
        if let Obj::Mul(product) = &fact.left {
            for (factor, scale) in [
                (product.left.as_ref(), product.right.as_ref()),
                (product.right.as_ref(), product.left.as_ref()),
            ] {
                if factor.to_string() == fact.right.to_string() {
                    alternatives.push(vec![
                        LessEqualFact::new(zero.clone(), factor.clone(), lf.clone()).into(),
                        LessEqualFact::new(scale.clone(), one.clone(), lf.clone()).into(),
                    ]);
                }
            }
        }
        // Componentwise multiplication is a constructor-removing strategy on
        // nonnegative lower factors. If `0 <= a <= c` and `0 <= b <= d`, then
        // `a*b <= c*d`. Try both deterministic pairings because multiplication
        // may be written in either factor order.
        if let (Obj::Mul(lower), Obj::Mul(upper)) = (&fact.left, &fact.right) {
            for (upper_left, upper_right) in [
                (upper.left.as_ref(), upper.right.as_ref()),
                (upper.right.as_ref(), upper.left.as_ref()),
            ] {
                alternatives.push(vec![
                    LessEqualFact::new(zero.clone(), lower.left.as_ref().clone(), lf.clone())
                        .into(),
                    LessEqualFact::new(zero.clone(), lower.right.as_ref().clone(), lf.clone())
                        .into(),
                    LessEqualFact::new(lower.left.as_ref().clone(), upper_left.clone(), lf.clone())
                        .into(),
                    LessEqualFact::new(
                        lower.right.as_ref().clone(),
                        upper_right.clone(),
                        lf.clone(),
                    )
                    .into(),
                ]);
            }
        }
        self.push_common_nonnegative_factor_alternatives(
            &fact.left,
            &fact.right,
            false,
            &lf,
            &mut alternatives,
        );
        self.verify_order_strategy_alternatives(alternatives)
    }

    fn verify_strict_structural_order_strategy(
        &mut self,
        fact: &LessFact,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        let zero: Obj = Number::new("0".to_string()).into();
        let lf = fact.line_file.clone();
        let mut alternatives: Vec<Vec<AtomicFact>> = Vec::new();

        if fact.left.to_string() == "0" {
            if let Obj::Mul(product) = &fact.right {
                alternatives.push(vec![
                    LessFact::new(zero.clone(), product.left.as_ref().clone(), lf.clone()).into(),
                    LessFact::new(zero.clone(), product.right.as_ref().clone(), lf.clone()).into(),
                ]);
                alternatives.push(vec![
                    LessFact::new(product.left.as_ref().clone(), zero.clone(), lf.clone()).into(),
                    LessFact::new(product.right.as_ref().clone(), zero.clone(), lf.clone()).into(),
                ]);
            }
        }

        if let (Obj::Add(left), Obj::Add(right)) = (&fact.left, &fact.right) {
            for (strict_left, strict_right) in [(true, false), (false, true)] {
                let left_order: AtomicFact = if strict_left {
                    LessFact::new(
                        left.left.as_ref().clone(),
                        right.left.as_ref().clone(),
                        lf.clone(),
                    )
                    .into()
                } else {
                    LessEqualFact::new(
                        left.left.as_ref().clone(),
                        right.left.as_ref().clone(),
                        lf.clone(),
                    )
                    .into()
                };
                let right_order: AtomicFact = if strict_right {
                    LessFact::new(
                        left.right.as_ref().clone(),
                        right.right.as_ref().clone(),
                        lf.clone(),
                    )
                    .into()
                } else {
                    LessEqualFact::new(
                        left.right.as_ref().clone(),
                        right.right.as_ref().clone(),
                        lf.clone(),
                    )
                    .into()
                };
                alternatives.push(vec![left_order, right_order]);
            }
        }
        // Subtracting the same real term preserves strict order.
        // Example: from `a < b`, prove `a - c < b - c`.
        if let (Obj::Sub(left), Obj::Sub(right)) = (&fact.left, &fact.right) {
            if left.right.to_string() == right.right.to_string() {
                alternatives.push(vec![LessFact::new(
                    left.left.as_ref().clone(),
                    right.left.as_ref().clone(),
                    lf.clone(),
                )
                .into()]);
            }
            // With a shared minuend, subtraction reverses strict order in the subtractor.
            // Example: from `c < d`, prove `a - d < a - c`.
            if left.left.to_string() == right.left.to_string() {
                alternatives.push(vec![LessFact::new(
                    right.right.as_ref().clone(),
                    left.right.as_ref().clone(),
                    lf.clone(),
                )
                .into()]);
            }
        }
        // Division by a shared positive term preserves strict order; division by a
        // shared negative term reverses it. Example: `a < b, 0 < c => a/c < b/c`.
        if let (Obj::Div(left), Obj::Div(right)) = (&fact.left, &fact.right) {
            if left.right.to_string() == right.right.to_string() {
                alternatives.push(vec![
                    LessFact::new(zero.clone(), left.right.as_ref().clone(), lf.clone()).into(),
                    LessFact::new(
                        left.left.as_ref().clone(),
                        right.left.as_ref().clone(),
                        lf.clone(),
                    )
                    .into(),
                ]);
                alternatives.push(vec![
                    LessFact::new(left.right.as_ref().clone(), zero.clone(), lf.clone()).into(),
                    LessFact::new(
                        right.left.as_ref().clone(),
                        left.left.as_ref().clone(),
                        lf.clone(),
                    )
                    .into(),
                ]);
            }
        }
        // Positive-integer powers preserve strict order on nonnegative bases.
        if let (Obj::Pow(left), Obj::Pow(right)) = (&fact.left, &fact.right) {
            if left.exponent.to_string() == right.exponent.to_string() {
                alternatives.push(vec![
                    InFact::new(
                        left.exponent.as_ref().clone(),
                        StandardSet::NPos.into(),
                        lf.clone(),
                    )
                    .into(),
                    LessEqualFact::new(zero.clone(), left.base.as_ref().clone(), lf.clone()).into(),
                    LessFact::new(
                        left.base.as_ref().clone(),
                        right.base.as_ref().clone(),
                        lf.clone(),
                    )
                    .into(),
                ]);
            }
        }
        // Strict absolute-value order uses the same constructor-removing square
        // comparison as the weak form.
        if let (Obj::Abs(left), Obj::Abs(right)) = (&fact.left, &fact.right) {
            let two: Obj = Number::new("2".to_string()).into();
            alternatives.push(vec![
                InFact::new(left.arg.as_ref().clone(), StandardSet::R.into(), lf.clone()).into(),
                InFact::new(
                    right.arg.as_ref().clone(),
                    StandardSet::R.into(),
                    lf.clone(),
                )
                .into(),
                LessFact::new(
                    Pow::new(left.arg.as_ref().clone(), two.clone()).into(),
                    Pow::new(right.arg.as_ref().clone(), two).into(),
                    lf.clone(),
                )
                .into(),
            ]);
        }
        if let Obj::Add(add) = &fact.right {
            alternatives.push(vec![
                LessFact::new(fact.left.clone(), add.left.as_ref().clone(), lf.clone()).into(),
                LessEqualFact::new(zero.clone(), add.right.as_ref().clone(), lf.clone()).into(),
            ]);
            alternatives.push(vec![
                LessEqualFact::new(fact.left.clone(), add.left.as_ref().clone(), lf.clone()).into(),
                LessFact::new(zero.clone(), add.right.as_ref().clone(), lf.clone()).into(),
            ]);
            alternatives.push(vec![
                LessFact::new(fact.left.clone(), add.right.as_ref().clone(), lf.clone()).into(),
                LessEqualFact::new(zero.clone(), add.left.as_ref().clone(), lf.clone()).into(),
            ]);
            alternatives.push(vec![
                LessEqualFact::new(fact.left.clone(), add.right.as_ref().clone(), lf.clone())
                    .into(),
                LessFact::new(zero.clone(), add.left.as_ref().clone(), lf.clone()).into(),
            ]);
        }
        if let Obj::Sub(sub) = &fact.left {
            if fact.right.to_string() == "0" {
                alternatives.push(vec![LessFact::new(
                    sub.left.as_ref().clone(),
                    sub.right.as_ref().clone(),
                    lf.clone(),
                )
                .into()]);
            }
        }
        if let Obj::Sub(sub) = &fact.right {
            if fact.left.to_string() == "0" {
                alternatives.push(vec![LessFact::new(
                    sub.right.as_ref().clone(),
                    sub.left.as_ref().clone(),
                    lf.clone(),
                )
                .into()]);
            }
        }
        self.push_common_nonnegative_factor_alternatives(
            &fact.left,
            &fact.right,
            true,
            &lf,
            &mut alternatives,
        );
        self.verify_order_strategy_alternatives(alternatives)
    }

    fn push_common_nonnegative_factor_alternatives(
        &self,
        left: &Obj,
        right: &Obj,
        strict: bool,
        lf: &LineFile,
        alternatives: &mut Vec<Vec<AtomicFact>>,
    ) {
        let (Obj::Mul(left_mul), Obj::Mul(right_mul)) = (left, right) else {
            return;
        };
        let left_factors = [left_mul.left.as_ref(), left_mul.right.as_ref()];
        let right_factors = [right_mul.left.as_ref(), right_mul.right.as_ref()];
        let zero: Obj = Number::new("0".to_string()).into();
        for (left_index, left_factor) in left_factors.iter().enumerate() {
            for (right_index, right_factor) in right_factors.iter().enumerate() {
                if left_factor.to_string() != right_factor.to_string() {
                    continue;
                }
                let left_other = left_factors[1 - left_index].clone();
                let right_other = right_factors[1 - right_index].clone();
                let factor_sign: AtomicFact = if strict {
                    LessFact::new(zero.clone(), (*left_factor).clone(), lf.clone()).into()
                } else {
                    LessEqualFact::new(zero.clone(), (*left_factor).clone(), lf.clone()).into()
                };
                let other_order: AtomicFact = if strict {
                    LessFact::new(left_other, right_other, lf.clone()).into()
                } else {
                    LessEqualFact::new(left_other, right_other, lf.clone()).into()
                };
                alternatives.push(vec![factor_sign, other_order]);
            }
        }
    }

    fn verify_order_strategy_alternatives(
        &mut self,
        alternatives: Vec<Vec<AtomicFact>>,
    ) -> Result<Option<Vec<StmtResult>>, RuntimeError> {
        for required in alternatives {
            let mut results = Vec::with_capacity(required.len());
            let mut complete = true;
            for child in required {
                let direct = self
                    .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                        &child,
                    )?;
                let result = if direct.is_true() {
                    direct
                } else {
                    self.verify_additive_sign_with_builtin_strategy(&child)?
                };
                if !result.is_true() {
                    complete = false;
                    break;
                }
                results.push(result);
            }
            if complete {
                return Ok(Some(results));
            }
        }
        Ok(None)
    }
}
