use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;

// Angle addition duplicates sine/cosine branches, so keep the symbolic
// expansion depth deliberately bounded. Unsupported deeper shapes remain
// unknown instead of causing unbounded verifier work.
const MAX_TRIG_EXPANSION_DEPTH: usize = 12;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TrigLemma {
    CoreValues,
    Addition,
    UnitCircle,
    Orientation,
    QuotientDefinition,
    Parity,
    Difference,
    DoubleAngle,
    SpecialPiValues,
    Cofunction,
    ShiftAndPeriod,
    Bounds,
    TanCotRelations,
}

impl TrigLemma {
    fn level(self) -> u8 {
        match self {
            TrigLemma::CoreValues
            | TrigLemma::Addition
            | TrigLemma::UnitCircle
            | TrigLemma::Orientation
            | TrigLemma::QuotientDefinition => 0,
            TrigLemma::Parity
            | TrigLemma::Difference
            | TrigLemma::DoubleAngle
            | TrigLemma::Bounds => 1,
            TrigLemma::SpecialPiValues | TrigLemma::Cofunction => 2,
            TrigLemma::ShiftAndPeriod => 3,
            TrigLemma::TanCotRelations => 4,
        }
    }

    fn name(self) -> &'static str {
        match self {
            TrigLemma::CoreValues => "core values at zero",
            TrigLemma::Addition => "addition formulas",
            TrigLemma::UnitCircle => "unit-circle identity",
            TrigLemma::Orientation => "values at pi / 2",
            TrigLemma::QuotientDefinition => "tan/cot quotient definitions",
            TrigLemma::Parity => "parity",
            TrigLemma::Difference => "difference formulas",
            TrigLemma::DoubleAngle => "double-angle formulas",
            TrigLemma::SpecialPiValues => "derived pi values",
            TrigLemma::Cofunction => "cofunction formulas",
            TrigLemma::ShiftAndPeriod => "pi shifts and periodicity",
            TrigLemma::Bounds => "unit-circle bounds",
            TrigLemma::TanCotRelations => "tan/cot derived relations",
        }
    }
}

struct TrigExpansion {
    obj: Obj,
    lemmas: Vec<TrigLemma>,
}

impl TrigExpansion {
    fn unchanged(obj: &Obj) -> Self {
        TrigExpansion {
            obj: obj.clone(),
            lemmas: Vec::new(),
        }
    }

    fn add_lemma(&mut self, lemma: TrigLemma) {
        if !self.lemmas.contains(&lemma) {
            self.lemmas.push(lemma);
        }
    }

    fn extend_lemmas(&mut self, other: Vec<TrigLemma>) {
        for lemma in other {
            self.add_lemma(lemma);
        }
    }
}

impl Runtime {
    // Native real trigonometric equalities are normalized from one small interface.
    // Example: `sin(x + y) = sin(x) * cos(y) + cos(x) * sin(y)`.
    pub(crate) fn try_verify_trigonometric_equality(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        if first_trig_arg(left).is_none() && first_trig_arg(right).is_none() {
            return Ok(None);
        }

        if let Some(result) = try_trig_quotient_definition(left, right, line_file.clone()) {
            return Ok(Some(result));
        }
        if let Some(result) = try_trig_quotient_definition(right, left, line_file.clone()) {
            return Ok(Some(result));
        }

        let mut left_expansion = expand_trig_obj(left, 0);
        let right_expansion = expand_trig_obj(right, 0);
        let mut used_unit_circle = false;

        let equal_after_expansion =
            objs_equal_by_rational_expression_evaluation(&left_expansion.obj, &right_expansion.obj);
        let equal_after_unit_circle = if equal_after_expansion {
            false
        } else {
            let (left_in_sin, left_changed) =
                rewrite_pythagorean_squares(&left_expansion.obj, true);
            let (right_in_sin, right_changed) =
                rewrite_pythagorean_squares(&right_expansion.obj, true);
            if (left_changed || right_changed)
                && objs_equal_by_rational_expression_evaluation(&left_in_sin, &right_in_sin)
            {
                used_unit_circle = true;
                true
            } else {
                let (left_in_cos, left_changed) =
                    rewrite_pythagorean_squares(&left_expansion.obj, false);
                let (right_in_cos, right_changed) =
                    rewrite_pythagorean_squares(&right_expansion.obj, false);
                if (left_changed || right_changed)
                    && objs_equal_by_rational_expression_evaluation(&left_in_cos, &right_in_cos)
                {
                    used_unit_circle = true;
                    true
                } else {
                    false
                }
            }
        };

        if !equal_after_expansion && !equal_after_unit_circle {
            return Ok(None);
        }

        if used_unit_circle {
            left_expansion.add_lemma(TrigLemma::UnitCircle);
        }
        left_expansion.extend_lemmas(right_expansion.lemmas);
        let reason = trig_reason(&left_expansion.lemmas);
        let dependencies =
            trig_core_dependency_results(left, right, &line_file, &left_expansion.lemmas);
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(left.clone(), right.clone(), line_file).into(),
                reason,
                dependencies,
            )
            .into(),
        ))
    }

    // Trigonometric range bounds come only from sin²+cos²=1 and square non-negativity.
    // Example: `forall x R: -1 <= sin(x) <= 1`.
    pub(crate) fn try_verify_trigonometric_order_bound(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if let Some(result) =
            self.try_verify_trigonometric_interval_order(atomic_fact, builtin_state)?
        {
            return Ok(Some(result));
        }
        let Some(AtomicFact::LessEqualFact(f)) = normalize_positive_order_atomic_fact(atomic_fact)
        else {
            return Ok(None);
        };

        if let Some((trig, other)) = square_trig_upper_bound_target(&f.left, &f.right) {
            let pythagorean = pythagorean_core_result(&trig, &other, &f.line_file);
            let other_square: Obj =
                Pow::new(other.clone(), Number::new("2".to_string()).into()).into();
            let nonnegative: AtomicFact = LessEqualFact::new(
                Number::new("0".to_string()).into(),
                other_square,
                f.line_file.clone(),
            )
            .into();
            let Some(nonnegative_result) =
                self.verify_zero_le_even_integer_pow_builtin_rule(&nonnegative, builtin_state)?
            else {
                return Ok(None);
            };
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    format!(
                        "trigonometry layer {}: {} derived from the unit-circle identity",
                        TrigLemma::Bounds.level(),
                        TrigLemma::Bounds.name()
                    ),
                    vec![pythagorean, nonnegative_result],
                )
                .into(),
            ));
        }

        let Some(trig) = bounded_trig_target(&f.left, &f.right) else {
            return Ok(None);
        };
        let square_bound: AtomicFact = LessEqualFact::new(
            Pow::new(trig.clone(), Number::new("2".to_string()).into()).into(),
            Number::new("1".to_string()).into(),
            f.line_file.clone(),
        )
        .into();
        let Some(square_bound_result) =
            self.try_verify_trigonometric_order_bound(&square_bound, builtin_state)?
        else {
            return Ok(None);
        };
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "trigonometry: -1 <= sin/cos <= 1 from the unit-circle square bound".to_string(),
                vec![square_bound_result],
            )
            .into(),
        ))
    }

    fn try_verify_trigonometric_interval_order(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        // Canonical interval facts connect trigonometric objects to real order.
        // Examples: `0 < x < pi => 0 < sin(x)`, sine is increasing on
        // `[-pi/2, pi/2]`, and cosine is decreasing on `[0, pi]`.
        let Some(normalized) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let pi: Obj = Pi::new().into();
        let zero: Obj = Number::new("0".to_string()).into();
        let two: Obj = Number::new("2".to_string()).into();
        let half_pi: Obj = Div::new(pi.clone(), two.clone()).into();
        let negative_half_pi: Obj =
            Mul::new(Number::new("-1".to_string()).into(), half_pi.clone()).into();
        let negative_pi: Obj = Mul::new(Number::new("-1".to_string()).into(), pi.clone()).into();

        let (premises, reason) = match &normalized {
            AtomicFact::LessFact(f) if obj_is_number(&f.left, "0") => match &f.right {
                Obj::Sin(sin) => (
                    vec![
                        LessFact::new(zero.clone(), sin.arg.as_ref().clone(), f.line_file.clone())
                            .into(),
                        LessFact::new(sin.arg.as_ref().clone(), pi.clone(), f.line_file.clone())
                            .into(),
                    ],
                    "sine is positive on (0, pi)",
                ),
                Obj::Cos(cos) => (
                    vec![
                        LessFact::new(
                            negative_half_pi.clone(),
                            cos.arg.as_ref().clone(),
                            f.line_file.clone(),
                        )
                        .into(),
                        LessFact::new(
                            cos.arg.as_ref().clone(),
                            half_pi.clone(),
                            f.line_file.clone(),
                        )
                        .into(),
                    ],
                    "cosine is positive on (-pi/2, pi/2)",
                ),
                Obj::Tan(tan) => (
                    vec![
                        LessFact::new(zero.clone(), tan.arg.as_ref().clone(), f.line_file.clone())
                            .into(),
                        LessFact::new(
                            tan.arg.as_ref().clone(),
                            half_pi.clone(),
                            f.line_file.clone(),
                        )
                        .into(),
                    ],
                    "tangent is positive on (0, pi/2)",
                ),
                Obj::Cot(cot) => (
                    vec![
                        LessFact::new(zero.clone(), cot.arg.as_ref().clone(), f.line_file.clone())
                            .into(),
                        LessFact::new(
                            cot.arg.as_ref().clone(),
                            half_pi.clone(),
                            f.line_file.clone(),
                        )
                        .into(),
                    ],
                    "cotangent is positive on (0, pi/2)",
                ),
                _ => return Ok(None),
            },
            AtomicFact::LessFact(f) if obj_is_number(&f.right, "0") => match &f.left {
                Obj::Sin(sin) => (
                    vec![
                        LessFact::new(
                            negative_pi.clone(),
                            sin.arg.as_ref().clone(),
                            f.line_file.clone(),
                        )
                        .into(),
                        LessFact::new(sin.arg.as_ref().clone(), zero.clone(), f.line_file.clone())
                            .into(),
                    ],
                    "sine is negative on (-pi, 0)",
                ),
                Obj::Tan(tan) => (
                    vec![
                        LessFact::new(
                            negative_half_pi.clone(),
                            tan.arg.as_ref().clone(),
                            f.line_file.clone(),
                        )
                        .into(),
                        LessFact::new(tan.arg.as_ref().clone(), zero.clone(), f.line_file.clone())
                            .into(),
                    ],
                    "tangent is negative on (-pi/2, 0)",
                ),
                Obj::Cot(cot) => (
                    vec![
                        LessFact::new(
                            half_pi.clone(),
                            cot.arg.as_ref().clone(),
                            f.line_file.clone(),
                        )
                        .into(),
                        LessFact::new(cot.arg.as_ref().clone(), pi.clone(), f.line_file.clone())
                            .into(),
                    ],
                    "cotangent is negative on (pi/2, pi)",
                ),
                _ => return Ok(None),
            },
            AtomicFact::LessFact(f) => {
                if let (Obj::Sin(left), Obj::Sin(right)) = (&f.left, &f.right) {
                    (
                        vec![
                            LessEqualFact::new(
                                negative_half_pi.clone(),
                                left.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessEqualFact::new(
                                right.arg.as_ref().clone(),
                                half_pi.clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessFact::new(
                                left.arg.as_ref().clone(),
                                right.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                        ],
                        "sine preserves strict order on [-pi/2, pi/2]",
                    )
                } else if let (Obj::Cos(right), Obj::Cos(left)) = (&f.left, &f.right) {
                    (
                        vec![
                            LessEqualFact::new(
                                zero.clone(),
                                left.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessEqualFact::new(
                                right.arg.as_ref().clone(),
                                pi.clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessFact::new(
                                left.arg.as_ref().clone(),
                                right.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                        ],
                        "cosine reverses strict order on [0, pi]",
                    )
                } else if let (Obj::Tan(left), Obj::Tan(right)) = (&f.left, &f.right) {
                    (
                        vec![
                            LessFact::new(
                                negative_half_pi.clone(),
                                left.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessFact::new(
                                right.arg.as_ref().clone(),
                                half_pi.clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessFact::new(
                                left.arg.as_ref().clone(),
                                right.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                        ],
                        "tangent preserves strict order on (-pi/2, pi/2)",
                    )
                } else if let (Obj::Cot(right), Obj::Cot(left)) = (&f.left, &f.right) {
                    (
                        vec![
                            LessFact::new(
                                zero.clone(),
                                left.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessFact::new(
                                right.arg.as_ref().clone(),
                                pi.clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessFact::new(
                                left.arg.as_ref().clone(),
                                right.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                        ],
                        "cotangent reverses strict order on (0, pi)",
                    )
                } else {
                    return Ok(None);
                }
            }
            AtomicFact::LessEqualFact(f) => {
                if let (Obj::Sin(left), Obj::Sin(right)) = (&f.left, &f.right) {
                    (
                        vec![
                            LessEqualFact::new(
                                negative_half_pi,
                                left.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessEqualFact::new(
                                right.arg.as_ref().clone(),
                                half_pi,
                                f.line_file.clone(),
                            )
                            .into(),
                            LessEqualFact::new(
                                left.arg.as_ref().clone(),
                                right.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                        ],
                        "sine preserves weak order on [-pi/2, pi/2]",
                    )
                } else if let (Obj::Cos(right), Obj::Cos(left)) = (&f.left, &f.right) {
                    (
                        vec![
                            LessEqualFact::new(
                                zero,
                                left.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessEqualFact::new(right.arg.as_ref().clone(), pi, f.line_file.clone())
                                .into(),
                            LessEqualFact::new(
                                left.arg.as_ref().clone(),
                                right.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                        ],
                        "cosine reverses weak order on [0, pi]",
                    )
                } else if let (Obj::Tan(left), Obj::Tan(right)) = (&f.left, &f.right) {
                    (
                        vec![
                            LessFact::new(
                                negative_half_pi.clone(),
                                left.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessFact::new(
                                right.arg.as_ref().clone(),
                                half_pi.clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessEqualFact::new(
                                left.arg.as_ref().clone(),
                                right.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                        ],
                        "tangent preserves weak order on (-pi/2, pi/2)",
                    )
                } else if let (Obj::Cot(right), Obj::Cot(left)) = (&f.left, &f.right) {
                    (
                        vec![
                            LessFact::new(
                                zero.clone(),
                                left.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessFact::new(
                                right.arg.as_ref().clone(),
                                pi.clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                            LessEqualFact::new(
                                left.arg.as_ref().clone(),
                                right.arg.as_ref().clone(),
                                f.line_file.clone(),
                            )
                            .into(),
                        ],
                        "cotangent reverses weak order on (0, pi)",
                    )
                } else {
                    return Ok(None);
                }
            }
            _ => return Ok(None),
        };

        let mut results = Vec::new();
        for premise in premises {
            let result = self.verify_builtin_rule_premise(&premise, builtin_state)?;
            if !result.is_true() {
                return Ok(None);
            }
            results.push(result);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                format!("trigonometry: {reason}"),
                results,
            )
            .into(),
        ))
    }

    // Transfer non-zero goals through the same canonical trigonometric expansion.
    // Example: `cos(x) != 0` implies `cos(x + pi) != 0`.
    pub(crate) fn try_verify_trigonometric_not_equal(
        &mut self,
        not_equal_fact: &NotEqualFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if first_trig_arg(&not_equal_fact.left).is_none()
            && first_trig_arg(&not_equal_fact.right).is_none()
        {
            return Ok(None);
        }
        let trig = if obj_is_number(&not_equal_fact.right, "0") {
            Some(&not_equal_fact.left)
        } else if obj_is_number(&not_equal_fact.left, "0") {
            Some(&not_equal_fact.right)
        } else {
            None
        };
        let pi: Obj = Pi::new().into();
        let half_pi: Obj = Div::new(pi.clone(), Number::new("2".to_string()).into()).into();
        let negative_half_pi: Obj =
            Mul::new(Number::new("-1".to_string()).into(), half_pi.clone()).into();
        let zero: Obj = Number::new("0".to_string()).into();
        let interval_candidates: Vec<Vec<AtomicFact>> = match trig {
            Some(Obj::Sin(sin)) => vec![
                vec![
                    LessFact::new(
                        zero.clone(),
                        sin.arg.as_ref().clone(),
                        not_equal_fact.line_file.clone(),
                    )
                    .into(),
                    LessFact::new(
                        sin.arg.as_ref().clone(),
                        pi.clone(),
                        not_equal_fact.line_file.clone(),
                    )
                    .into(),
                ],
                vec![
                    LessFact::new(
                        zero.clone(),
                        sin.arg.as_ref().clone(),
                        not_equal_fact.line_file.clone(),
                    )
                    .into(),
                    LessFact::new(
                        sin.arg.as_ref().clone(),
                        half_pi.clone(),
                        not_equal_fact.line_file.clone(),
                    )
                    .into(),
                ],
            ],
            Some(Obj::Cos(cos)) => vec![
                vec![
                    LessFact::new(
                        negative_half_pi.clone(),
                        cos.arg.as_ref().clone(),
                        not_equal_fact.line_file.clone(),
                    )
                    .into(),
                    LessFact::new(
                        cos.arg.as_ref().clone(),
                        half_pi.clone(),
                        not_equal_fact.line_file.clone(),
                    )
                    .into(),
                ],
                vec![
                    LessFact::new(
                        zero.clone(),
                        cos.arg.as_ref().clone(),
                        not_equal_fact.line_file.clone(),
                    )
                    .into(),
                    LessFact::new(
                        cos.arg.as_ref().clone(),
                        half_pi.clone(),
                        not_equal_fact.line_file.clone(),
                    )
                    .into(),
                ],
            ],
            _ => Vec::new(),
        };
        for premises in interval_candidates {
            let mut results = Vec::new();
            for premise in premises {
                let result = self.verify_builtin_rule_premise(&premise, builtin_state)?;
                if !result.is_true() {
                    results.clear();
                    break;
                }
                results.push(result);
            }
            if results.len() == 2 {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        not_equal_fact.clone().into(),
                        "trigonometry: sine/cosine is nonzero on a canonical sign interval"
                            .to_string(),
                        results,
                    )
                    .into(),
                ));
            }
        }
        if let Some(reduced_left) = shifted_trig_nonzero_reduction(&not_equal_fact.left) {
            let reduced: AtomicFact = NotEqualFact::new(
                reduced_left,
                not_equal_fact.right.clone(),
                not_equal_fact.line_file.clone(),
            )
            .into();
            let reduced_result = self.verify_builtin_rule_premise(&reduced, builtin_state)?;
            if reduced_result.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        not_equal_fact.clone().into(),
                        "trigonometry: pi shift changes only sign, preserving non-zero".to_string(),
                        vec![reduced_result],
                    )
                    .into(),
                ));
            }
        }
        let left = expand_trig_obj(&not_equal_fact.left, 0);
        let right = expand_trig_obj(&not_equal_fact.right, 0);
        if left.obj.to_string() == not_equal_fact.left.to_string()
            && right.obj.to_string() == not_equal_fact.right.to_string()
        {
            return Ok(None);
        }
        let expanded: AtomicFact =
            NotEqualFact::new(left.obj, right.obj, not_equal_fact.line_file.clone()).into();
        let expanded_result = self.verify_builtin_rule_premise(&expanded, builtin_state)?;
        if !expanded_result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                not_equal_fact.clone().into(),
                "trigonometry: non-zero transfer through canonical expansion".to_string(),
                vec![expanded_result],
            )
            .into(),
        ))
    }
}

fn expand_trig_obj(obj: &Obj, depth: usize) -> TrigExpansion {
    if depth >= MAX_TRIG_EXPANSION_DEPTH {
        return TrigExpansion::unchanged(obj);
    }
    match obj {
        Obj::Add(x) => expand_binary_obj(&x.left, &x.right, depth, ADD),
        Obj::Sub(x) => expand_binary_obj(&x.left, &x.right, depth, SUB),
        Obj::Mul(x) => expand_binary_obj(&x.left, &x.right, depth, MUL),
        Obj::Div(x) => expand_binary_obj(&x.left, &x.right, depth, DIV),
        Obj::Pow(x) => expand_binary_obj(&x.base, &x.exponent, depth, POW),
        Obj::Abs(x) => {
            let inner = expand_trig_obj(&x.arg, depth + 1);
            TrigExpansion {
                obj: Abs::new(inner.obj).into(),
                lemmas: inner.lemmas,
            }
        }
        Obj::Sin(x) => expand_sin_or_cos(&x.arg, true, depth + 1),
        Obj::Cos(x) => expand_sin_or_cos(&x.arg, false, depth + 1),
        Obj::Tan(x) => {
            let quotient: Obj = Div::new(
                Sin::new((*x.arg).clone()).into(),
                Cos::new((*x.arg).clone()).into(),
            )
            .into();
            let mut result = expand_trig_obj(&quotient, depth + 1);
            result.add_lemma(TrigLemma::QuotientDefinition);
            result.add_lemma(TrigLemma::TanCotRelations);
            result
        }
        Obj::Cot(x) => {
            let quotient: Obj = Div::new(
                Cos::new((*x.arg).clone()).into(),
                Sin::new((*x.arg).clone()).into(),
            )
            .into();
            let mut result = expand_trig_obj(&quotient, depth + 1);
            result.add_lemma(TrigLemma::QuotientDefinition);
            result.add_lemma(TrigLemma::TanCotRelations);
            result
        }
        _ => TrigExpansion::unchanged(obj),
    }
}

fn expand_binary_obj(left: &Obj, right: &Obj, depth: usize, operator: &str) -> TrigExpansion {
    let left_expansion = expand_trig_obj(left, depth + 1);
    let right_expansion = expand_trig_obj(right, depth + 1);
    let obj = match operator {
        ADD => Add::new(left_expansion.obj, right_expansion.obj).into(),
        SUB => Sub::new(left_expansion.obj, right_expansion.obj).into(),
        MUL => Mul::new(left_expansion.obj, right_expansion.obj).into(),
        DIV => Div::new(left_expansion.obj, right_expansion.obj).into(),
        POW => {
            if obj_is_number(&right_expansion.obj, "2") {
                if let Obj::Div(div) = &left_expansion.obj {
                    Div::new(
                        Pow::new((*div.left).clone(), Number::new("2".to_string()).into()).into(),
                        Pow::new((*div.right).clone(), Number::new("2".to_string()).into()).into(),
                    )
                    .into()
                } else {
                    Pow::new(left_expansion.obj, right_expansion.obj).into()
                }
            } else {
                Pow::new(left_expansion.obj, right_expansion.obj).into()
            }
        }
        _ => unreachable!(),
    };
    let mut result = TrigExpansion {
        obj,
        lemmas: left_expansion.lemmas,
    };
    result.extend_lemmas(right_expansion.lemmas);
    result
}

fn expand_sin_or_cos(arg: &Obj, is_sin: bool, depth: usize) -> TrigExpansion {
    let arg_expansion = expand_trig_obj(arg, depth + 1);
    let arg = arg_expansion.obj;
    let mut inherited_lemmas = arg_expansion.lemmas;

    if let Some((value, lemma)) = special_trig_value(&arg, is_sin) {
        if !inherited_lemmas.contains(&lemma) {
            inherited_lemmas.push(lemma);
        }
        return TrigExpansion {
            obj: value,
            lemmas: inherited_lemmas,
        };
    }

    if let Some(mut result) = derived_special_pi_expansion(&arg, is_sin, depth + 1) {
        result.extend_lemmas(inherited_lemmas);
        return result;
    }

    if let Some(inner) = negated_arg(&arg) {
        let mut result = if is_sin {
            let expanded = expand_sin_or_cos(&inner, true, depth + 1);
            TrigExpansion {
                obj: Mul::new(Number::new("-1".to_string()).into(), expanded.obj).into(),
                lemmas: expanded.lemmas,
            }
        } else {
            expand_sin_or_cos(&inner, false, depth + 1)
        };
        result.extend_lemmas(inherited_lemmas);
        result.add_lemma(TrigLemma::Parity);
        return result;
    }

    if let Some(inner) = doubled_arg(&arg) {
        let mut result = expand_addition_angle(&inner, &inner, is_sin, depth + 1);
        result.extend_lemmas(inherited_lemmas);
        result.add_lemma(TrigLemma::Addition);
        result.add_lemma(TrigLemma::DoubleAngle);
        return result;
    }

    match &arg {
        Obj::Add(x) => {
            let mut result = expand_addition_angle(&x.left, &x.right, is_sin, depth);
            result.extend_lemmas(inherited_lemmas);
            result.add_lemma(TrigLemma::Addition);
            add_shift_kind_lemma(&mut result, &x.left, &x.right);
            result
        }
        Obj::Sub(x) => {
            let negated_right: Obj =
                Mul::new(Number::new("-1".to_string()).into(), (*x.right).clone()).into();
            let mut result = expand_addition_angle(&x.left, &negated_right, is_sin, depth);
            result.extend_lemmas(inherited_lemmas);
            result.add_lemma(TrigLemma::Addition);
            result.add_lemma(TrigLemma::Difference);
            add_shift_kind_lemma(&mut result, &x.left, &x.right);
            result
        }
        _ => TrigExpansion {
            obj: if is_sin {
                Sin::new(arg).into()
            } else {
                Cos::new(arg).into()
            },
            lemmas: inherited_lemmas,
        },
    }
}

fn expand_addition_angle(left: &Obj, right: &Obj, is_sin: bool, depth: usize) -> TrigExpansion {
    let sin_left = expand_sin_or_cos(left, true, depth + 1);
    let cos_left = expand_sin_or_cos(left, false, depth + 1);
    let sin_right = expand_sin_or_cos(right, true, depth + 1);
    let cos_right = expand_sin_or_cos(right, false, depth + 1);

    let first: Obj = if is_sin {
        Mul::new(sin_left.obj.clone(), cos_right.obj.clone()).into()
    } else {
        Mul::new(cos_left.obj.clone(), cos_right.obj.clone()).into()
    };
    let second: Obj = if is_sin {
        Mul::new(cos_left.obj.clone(), sin_right.obj.clone()).into()
    } else {
        Mul::new(sin_left.obj.clone(), sin_right.obj.clone()).into()
    };
    let obj = if is_sin {
        Add::new(first, second).into()
    } else {
        Sub::new(first, second).into()
    };

    let mut result = TrigExpansion {
        obj,
        lemmas: sin_left.lemmas,
    };
    result.extend_lemmas(cos_left.lemmas);
    result.extend_lemmas(sin_right.lemmas);
    result.extend_lemmas(cos_right.lemmas);
    result
}

fn special_trig_value(arg: &Obj, is_sin: bool) -> Option<(Obj, TrigLemma)> {
    if obj_is_number(arg, "0") {
        let value = if is_sin { "0" } else { "1" };
        return Some((Number::new(value.to_string()).into(), TrigLemma::CoreValues));
    }
    if obj_matches_scaled_pi(arg, 1, 2) {
        let value = if is_sin { "1" } else { "0" };
        return Some((
            Number::new(value.to_string()).into(),
            TrigLemma::Orientation,
        ));
    }
    None
}

fn derived_special_pi_expansion(arg: &Obj, is_sin: bool, depth: usize) -> Option<TrigExpansion> {
    let (numerator, denominator) = [(-1, 2), (1, 1), (-1, 1), (3, 2), (-3, 2), (2, 1), (-2, 1)]
        .into_iter()
        .find(|(numerator, denominator)| obj_matches_scaled_pi(arg, *numerator, *denominator))?;

    let half_pi: Obj = Div::new(Pi::new().into(), Number::new("2".to_string()).into()).into();
    let pi: Obj = Pi::new().into();
    let (left, right, negate_result) = match (numerator, denominator) {
        (-1, 2) => (half_pi.clone(), None, true),
        (1, 1) => (half_pi.clone(), Some(half_pi.clone()), false),
        (-1, 1) => (half_pi.clone(), Some(half_pi.clone()), true),
        (3, 2) => (pi.clone(), Some(half_pi.clone()), false),
        (-3, 2) => (pi.clone(), Some(half_pi.clone()), true),
        (2, 1) => (pi.clone(), Some(pi), false),
        (-2, 1) => (pi.clone(), Some(pi), true),
        _ => unreachable!(),
    };

    let mut result = if let Some(right) = right {
        expand_addition_angle(&left, &right, is_sin, depth + 1)
    } else {
        expand_sin_or_cos(&left, is_sin, depth + 1)
    };
    if negate_result && is_sin {
        result.obj = Mul::new(Number::new("-1".to_string()).into(), result.obj).into();
    }
    if negate_result {
        result.add_lemma(TrigLemma::Parity);
    }
    if denominator == 1 || numerator.abs() > 1 {
        result.add_lemma(TrigLemma::Addition);
        result.add_lemma(TrigLemma::SpecialPiValues);
    }
    Some(result)
}

fn rewrite_pythagorean_squares(obj: &Obj, prefer_sin: bool) -> (Obj, bool) {
    if let Obj::Mul(mul) = obj {
        let repeated_arg = if prefer_sin {
            match (mul.left.as_ref(), mul.right.as_ref()) {
                (Obj::Cos(left), Obj::Cos(right))
                    if objs_equal_by_rational_expression_evaluation(&left.arg, &right.arg) =>
                {
                    Some((*left.arg).clone())
                }
                _ => None,
            }
        } else {
            match (mul.left.as_ref(), mul.right.as_ref()) {
                (Obj::Sin(left), Obj::Sin(right))
                    if objs_equal_by_rational_expression_evaluation(&left.arg, &right.arg) =>
                {
                    Some((*left.arg).clone())
                }
                _ => None,
            }
        };
        if let Some(arg) = repeated_arg {
            let complementary: Obj = if prefer_sin {
                Sin::new(arg).into()
            } else {
                Cos::new(arg).into()
            };
            return (
                Sub::new(
                    Number::new("1".to_string()).into(),
                    Pow::new(complementary, Number::new("2".to_string()).into()).into(),
                )
                .into(),
                true,
            );
        }
    }
    if let Obj::Pow(pow) = obj {
        if obj_is_number(&pow.exponent, "2") {
            if prefer_sin {
                if let Obj::Cos(cos) = pow.base.as_ref() {
                    let replacement: Obj = Sub::new(
                        Number::new("1".to_string()).into(),
                        Pow::new(
                            Sin::new((*cos.arg).clone()).into(),
                            Number::new("2".to_string()).into(),
                        )
                        .into(),
                    )
                    .into();
                    return (replacement, true);
                }
            } else if let Obj::Sin(sin) = pow.base.as_ref() {
                let replacement: Obj = Sub::new(
                    Number::new("1".to_string()).into(),
                    Pow::new(
                        Cos::new((*sin.arg).clone()).into(),
                        Number::new("2".to_string()).into(),
                    )
                    .into(),
                )
                .into();
                return (replacement, true);
            }
        }
    }
    match obj {
        Obj::Add(x) => rewrite_pythagorean_binary(&x.left, &x.right, prefer_sin, ADD),
        Obj::Sub(x) => rewrite_pythagorean_binary(&x.left, &x.right, prefer_sin, SUB),
        Obj::Mul(x) => rewrite_pythagorean_binary(&x.left, &x.right, prefer_sin, MUL),
        Obj::Div(x) => rewrite_pythagorean_binary(&x.left, &x.right, prefer_sin, DIV),
        Obj::Pow(x) => rewrite_pythagorean_binary(&x.base, &x.exponent, prefer_sin, POW),
        _ => (obj.clone(), false),
    }
}

fn rewrite_pythagorean_binary(
    left: &Obj,
    right: &Obj,
    prefer_sin: bool,
    operator: &str,
) -> (Obj, bool) {
    let (left, left_changed) = rewrite_pythagorean_squares(left, prefer_sin);
    let (right, right_changed) = rewrite_pythagorean_squares(right, prefer_sin);
    let result = match operator {
        ADD => Add::new(left, right).into(),
        SUB => Sub::new(left, right).into(),
        MUL => Mul::new(left, right).into(),
        DIV => Div::new(left, right).into(),
        POW => Pow::new(left, right).into(),
        _ => unreachable!(),
    };
    (result, left_changed || right_changed)
}

fn try_trig_quotient_definition(
    trig_side: &Obj,
    quotient_side: &Obj,
    line_file: LineFile,
) -> Option<StmtResult> {
    let expected: Obj = match trig_side {
        Obj::Tan(x) => Div::new(
            Sin::new((*x.arg).clone()).into(),
            Cos::new((*x.arg).clone()).into(),
        )
        .into(),
        Obj::Cot(x) => Div::new(
            Cos::new((*x.arg).clone()).into(),
            Sin::new((*x.arg).clone()).into(),
        )
        .into(),
        _ => return None,
    };
    if !objs_equal_by_rational_expression_evaluation(&expected, quotient_side) {
        return None;
    }
    Some(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            EqualFact::new(trig_side.clone(), quotient_side.clone(), line_file).into(),
            "trigonometry core: tan/cot quotient definition".to_string(),
            Vec::new(),
        )
        .into(),
    )
}

fn pythagorean_core_result(sin_or_cos: &Obj, other: &Obj, line_file: &LineFile) -> StmtResult {
    let (sin, cos) = match sin_or_cos {
        Obj::Sin(_) => (sin_or_cos.clone(), other.clone()),
        Obj::Cos(_) => (other.clone(), sin_or_cos.clone()),
        _ => unreachable!(),
    };
    let left: Obj = Add::new(
        Pow::new(sin, Number::new("2".to_string()).into()).into(),
        Pow::new(cos, Number::new("2".to_string()).into()).into(),
    )
    .into();
    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
        EqualFact::new(left, Number::new("1".to_string()).into(), line_file.clone()).into(),
        "trigonometry core: sin(x)^2 + cos(x)^2 = 1".to_string(),
        Vec::new(),
    )
    .into()
}

fn square_trig_upper_bound_target(left: &Obj, right: &Obj) -> Option<(Obj, Obj)> {
    if !obj_is_number(right, "1") {
        return None;
    }
    let Obj::Pow(pow) = left else {
        return None;
    };
    if !obj_is_number(&pow.exponent, "2") {
        return None;
    }
    match pow.base.as_ref() {
        Obj::Sin(x) => Some((
            Sin::new((*x.arg).clone()).into(),
            Cos::new((*x.arg).clone()).into(),
        )),
        Obj::Cos(x) => Some((
            Cos::new((*x.arg).clone()).into(),
            Sin::new((*x.arg).clone()).into(),
        )),
        _ => None,
    }
}

fn bounded_trig_target(left: &Obj, right: &Obj) -> Option<Obj> {
    if obj_is_number(left, "-1") {
        return match right {
            Obj::Sin(_) | Obj::Cos(_) => Some(right.clone()),
            _ => None,
        };
    }
    if obj_is_number(right, "1") {
        match left {
            Obj::Sin(_) | Obj::Cos(_) => return Some(left.clone()),
            Obj::Abs(abs) if matches!(abs.arg.as_ref(), Obj::Sin(_) | Obj::Cos(_)) => {
                return Some((*abs.arg).clone())
            }
            _ => {}
        }
    }
    None
}

fn trig_reason(lemmas: &[TrigLemma]) -> String {
    if lemmas.is_empty() {
        return "trigonometry core: canonical symbolic equality".to_string();
    }
    let mut ordered = lemmas.to_vec();
    ordered.sort_by_key(|lemma| lemma.level());
    let level = ordered.iter().map(|lemma| lemma.level()).max().unwrap_or(0);
    let names = ordered
        .iter()
        .map(|lemma| lemma.name())
        .collect::<Vec<&str>>()
        .join(", ");
    format!(
        "trigonometry layer {}: canonical expansion from {}",
        level, names
    )
}

fn trig_core_dependency_results(
    left: &Obj,
    right: &Obj,
    line_file: &LineFile,
    lemmas: &[TrigLemma],
) -> Vec<StmtResult> {
    if !lemmas.iter().any(|lemma| lemma.level() > 0) {
        return Vec::new();
    }
    let Some(arg) = first_trig_arg(left).or_else(|| first_trig_arg(right)) else {
        return Vec::new();
    };
    let sin: Obj = Sin::new(arg.clone()).into();
    let cos: Obj = Cos::new(arg.clone()).into();
    let mut results = vec![pythagorean_core_result(&sin, &cos, line_file)];
    if lemmas.iter().any(|lemma| {
        matches!(
            lemma,
            TrigLemma::Parity
                | TrigLemma::Difference
                | TrigLemma::DoubleAngle
                | TrigLemma::Cofunction
                | TrigLemma::ShiftAndPeriod
                | TrigLemma::TanCotRelations
        )
    }) {
        let zero: Obj = Number::new("0".to_string()).into();
        let source: Obj = Sin::new(Add::new(arg.clone(), zero.clone()).into()).into();
        let expanded: Obj = Add::new(
            Mul::new(Sin::new(arg.clone()).into(), Cos::new(zero.clone()).into()).into(),
            Mul::new(Cos::new(arg).into(), Sin::new(zero).into()).into(),
        )
        .into();
        results.push(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                EqualFact::new(source, expanded, line_file.clone()).into(),
                "trigonometry core: sine addition formula".to_string(),
                Vec::new(),
            )
            .into(),
        );
    }
    results
}

fn add_shift_kind_lemma(result: &mut TrigExpansion, left: &Obj, right: &Obj) {
    if is_half_pi(left) || is_half_pi(right) {
        result.add_lemma(TrigLemma::Cofunction);
    }
    if is_pi_or_two_pi(left) || is_pi_or_two_pi(right) {
        result.add_lemma(TrigLemma::ShiftAndPeriod);
    }
}

fn is_half_pi(obj: &Obj) -> bool {
    obj_matches_scaled_pi(obj, 1, 2) || obj_matches_scaled_pi(obj, -1, 2)
}

fn is_pi_or_two_pi(obj: &Obj) -> bool {
    obj_matches_scaled_pi(obj, 1, 1)
        || obj_matches_scaled_pi(obj, -1, 1)
        || obj_matches_scaled_pi(obj, 2, 1)
        || obj_matches_scaled_pi(obj, -2, 1)
}

fn shifted_trig_nonzero_reduction(obj: &Obj) -> Option<Obj> {
    let (arg, is_sin) = match obj {
        Obj::Sin(x) => (x.arg.as_ref(), true),
        Obj::Cos(x) => (x.arg.as_ref(), false),
        _ => return None,
    };
    if let Some(base) = negated_arg(arg) {
        // sin(-x) only changes sign and cos(-x) does not; either way nonzeroness is unchanged.
        return Some(if is_sin {
            Sin::new(base).into()
        } else {
            Cos::new(base).into()
        });
    }
    let base = match arg {
        Obj::Add(add) => {
            if obj_matches_scaled_pi(&add.right, 1, 1) || obj_matches_scaled_pi(&add.right, -1, 1) {
                (*add.left).clone()
            } else if obj_matches_scaled_pi(&add.left, 1, 1)
                || obj_matches_scaled_pi(&add.left, -1, 1)
            {
                (*add.right).clone()
            } else if obj_matches_scaled_pi(&add.right, 2, 1)
                || obj_matches_scaled_pi(&add.right, -2, 1)
            {
                (*add.left).clone()
            } else if obj_matches_scaled_pi(&add.left, 2, 1)
                || obj_matches_scaled_pi(&add.left, -2, 1)
            {
                (*add.right).clone()
            } else {
                return None;
            }
        }
        Obj::Sub(sub) => {
            if obj_matches_scaled_pi(&sub.right, 1, 1) || obj_matches_scaled_pi(&sub.right, -1, 1) {
                (*sub.left).clone()
            } else if obj_matches_scaled_pi(&sub.right, 2, 1)
                || obj_matches_scaled_pi(&sub.right, -2, 1)
            {
                (*sub.left).clone()
            } else {
                return None;
            }
        }
        _ => return None,
    };
    // For a nonzero goal, the sign introduced by a pi shift is irrelevant.
    Some(if is_sin {
        Sin::new(base).into()
    } else {
        Cos::new(base).into()
    })
}

fn obj_matches_scaled_pi(obj: &Obj, numerator: i64, denominator: i64) -> bool {
    let coefficient: Obj = if denominator == 1 {
        Number::new(numerator.to_string()).into()
    } else {
        Div::new(
            Number::new(numerator.to_string()).into(),
            Number::new(denominator.to_string()).into(),
        )
        .into()
    };
    let expected: Obj = Mul::new(coefficient, Pi::new().into()).into();
    objs_equal_by_rational_expression_evaluation(obj, &expected)
}

fn negated_arg(obj: &Obj) -> Option<Obj> {
    let Obj::Mul(mul) = obj else {
        return None;
    };
    if obj_is_number(&mul.left, "-1") {
        return Some((*mul.right).clone());
    }
    if obj_is_number(&mul.right, "-1") {
        return Some((*mul.left).clone());
    }
    None
}

fn doubled_arg(obj: &Obj) -> Option<Obj> {
    let Obj::Mul(mul) = obj else {
        return None;
    };
    if obj_is_number(&mul.left, "2") {
        return Some((*mul.right).clone());
    }
    if obj_is_number(&mul.right, "2") {
        return Some((*mul.left).clone());
    }
    None
}

fn obj_is_number(obj: &Obj, expected: &str) -> bool {
    obj.evaluate_to_normalized_decimal_number()
        .is_some_and(|number| number.normalized_value == expected)
}

fn first_trig_arg(obj: &Obj) -> Option<Obj> {
    match obj {
        Obj::Sin(x) => Some((*x.arg).clone()),
        Obj::Cos(x) => Some((*x.arg).clone()),
        Obj::Tan(x) => Some((*x.arg).clone()),
        Obj::Cot(x) => Some((*x.arg).clone()),
        Obj::Add(x) => first_trig_arg(&x.left).or_else(|| first_trig_arg(&x.right)),
        Obj::Sub(x) => first_trig_arg(&x.left).or_else(|| first_trig_arg(&x.right)),
        Obj::Mul(x) => first_trig_arg(&x.left).or_else(|| first_trig_arg(&x.right)),
        Obj::Div(x) => first_trig_arg(&x.left).or_else(|| first_trig_arg(&x.right)),
        Obj::Pow(x) => first_trig_arg(&x.base).or_else(|| first_trig_arg(&x.exponent)),
        Obj::Abs(x) => first_trig_arg(&x.arg),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn derived_trig_lemmas_are_strictly_above_their_core_dependencies() {
        for lemma in [
            TrigLemma::Parity,
            TrigLemma::Difference,
            TrigLemma::DoubleAngle,
            TrigLemma::SpecialPiValues,
            TrigLemma::Cofunction,
            TrigLemma::ShiftAndPeriod,
            TrigLemma::Bounds,
            TrigLemma::TanCotRelations,
        ] {
            assert!(lemma.level() > 0);
        }
        for lemma in [
            TrigLemma::CoreValues,
            TrigLemma::Addition,
            TrigLemma::UnitCircle,
            TrigLemma::Orientation,
            TrigLemma::QuotientDefinition,
        ] {
            assert_eq!(lemma.level(), 0);
        }
    }
}
