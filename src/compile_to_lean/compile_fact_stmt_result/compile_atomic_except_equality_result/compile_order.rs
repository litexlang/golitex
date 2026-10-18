use crate::compile_to_lean::{LitexToLeanCompiler, LeanCompileError};
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rewrite::AtomicExceptEqualityFactSearchProofByBuiltinOrderDual;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater::GreaterFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::GreaterEqualFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::LessFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::NotEqualFactSearchProofByBuiltinRule;
use crate::rational_expression::NumberCompareResult;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_order_proposition(
        &self,
        fact: &AtomicFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(fact)?;
        Ok(format!(
            "Litex.{} {} {}",
            if strict { "Lt" } else { "Le" },
            self.compile_object_reference(low, position)?,
            self.compile_object_reference(high, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_closed_order(
        &self,
        goal: &AtomicFact,
        proof: &ClosedAtomicExceptEqualityCalculationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match (goal, proof) {
            (AtomicFact::LessFact(_), ClosedAtomicExceptEqualityCalculationProof::Less(p))
            | (
                AtomicFact::GreaterFact(_),
                ClosedAtomicExceptEqualityCalculationProof::Greater(p),
            )
            | (
                AtomicFact::LessEqualFact(_),
                ClosedAtomicExceptEqualityCalculationProof::LessEqual(p),
            )
            | (
                AtomicFact::GreaterEqualFact(_),
                ClosedAtomicExceptEqualityCalculationProof::GreaterEqual(p),
            ) => self.compile_closed_comparison(goal, p, false, position),
            (
                AtomicFact::NotLessFact(_),
                ClosedAtomicExceptEqualityCalculationProof::NotLess(p),
            )
            | (
                AtomicFact::NotGreaterFact(_),
                ClosedAtomicExceptEqualityCalculationProof::NotGreater(p),
            )
            | (
                AtomicFact::NotLessEqualFact(_),
                ClosedAtomicExceptEqualityCalculationProof::NotLessEqual(p),
            )
            | (
                AtomicFact::NotGreaterEqualFact(_),
                ClosedAtomicExceptEqualityCalculationProof::NotGreaterEqual(p),
            ) => {
                // A polarity view reuses the original subject and ID. The
                // actual negative certificate is checked below, not replaced
                // by a newly calculated positive proof.
                let positive = crate::ast::fact::negate_atomic_fact(goal, goal.fact_id())
                    .ok_or_else(|| LeanCompileError::unsupported("Order/ClosedNegation"))?;
                self.compile_closed_comparison(&positive, p, true, position)
            }
            _ => Err(LeanCompileError::new(
                "Order/ClosedFamily",
                "The typed closed comparison variant has another source predicate family.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_closed_comparison(
        &self,
        goal: &AtomicFact,
        proof: &ClosedComparisonCalculationProof,
        negative: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (kind, left, right) = source_order_parts(goal)?;
        let x = self.compile_numeric_observation(left, position)?;
        let y = self.compile_numeric_observation(right, position)?;
        let a =
            x.3.as_ref()
                .ok_or_else(|| LeanCompileError::unsupported("Order/ClosedExpression"))?;
        let b =
            y.3.as_ref()
                .ok_or_else(|| LeanCompileError::unsupported("Order/ClosedExpression"))?;
        // Exact typed values are the certificate owner. The normal strings are
        // presentation fields, never proof subjects or evaluation instructions.
        let values_match = match &proof.values {
            ClosedValuePair::Decimal { left, right } => {
                scalar_decimal(left)? == *a && scalar_decimal(right)? == *b
            }
            ClosedValuePair::Rational { left, right } => left == a && right == b,
            ClosedValuePair::Complex {
                left_real,
                left_imaginary,
                right_real,
                right_imaginary,
            } => {
                left_real == a
                    && right_real == b
                    && left_imaginary.is_zero()
                    && right_imaginary.is_zero()
            }
            ClosedValuePair::Radical { .. } => {
                return Err(LeanCompileError::unsupported("Order/ClosedRadical"))
            }
        };
        let comparison = a
            .compare(b)
            .ok_or_else(|| LeanCompileError::unsupported("Order/ClosedEvaluationBound"))?;
        let true_order = match kind {
            SourceOrderKind::Less => comparison == NumberCompareResult::Less,
            SourceOrderKind::Greater => comparison == NumberCompareResult::Greater,
            SourceOrderKind::LessEqual => comparison != NumberCompareResult::Greater,
            SourceOrderKind::GreaterEqual => comparison != NumberCompareResult::Less,
        };
        if !values_match || comparison != proof.comparison || true_order == negative {
            return Err(LeanCompileError::new(
                "Order/ClosedValues",
                "Typed comparison values, comparison tag or source orientation do not agree.",
            ));
        }
        let r = exact_rational_literal(a, "ℝ")?;
        let s = exact_rational_literal(b, "ℝ")?;
        // These are the actual real-domain facts replayed before truth. A
        // numeric view alone does not classify an arbitrary complex as real.
        let ha = self.compile_real_membership_certificate(left, position)?;
        let hb = self.compile_real_membership_certificate(right, position)?;
        let lhs = self.compile_object_reference(left, position)?;
        let rhs = self.compile_object_reference(right, position)?;
        let (low, high, strict) = source_order_oriented(goal)?;
        let (low_r, high_r, low_value, high_value) = match kind {
            SourceOrderKind::Less | SourceOrderKind::LessEqual => {
                (&ha, &hb, "_litex_left_value", "_litex_right_value")
            }
            SourceOrderKind::Greater | SourceOrderKind::GreaterEqual => {
                (&hb, &ha, "_litex_right_value", "_litex_left_value")
            }
        };
        let observation = if strict {
            "lt_iff_asReal"
        } else {
            "le_iff_asReal"
        };
        let relation = if strict { "<" } else { "≤" };
        let equivalence = format!(
            "(Litex.NativeBridge.{observation} {} {} {low_r} {high_r})",
            self.compile_object_reference(low, position)?,
            self.compile_object_reference(high, position)?,
        );
        let equivalence = if negative {
            format!("(not_congr {equivalence})")
        } else {
            equivalence
        };
        let native_relation = if negative {
            format!("¬ (_litex_r {relation} _litex_s)")
        } else {
            format!("_litex_r {relation} _litex_s")
        };
        Ok(format!(
            "({equivalence}.mpr (by\n  have _litex_left_value : Litex.NativeBridge.asReal {lhs} {ha} = {r} := by\n    apply Complex.ofReal_injective\n    exact M.number_injective ((Litex.NativeBridge.asReal_spec {lhs} {ha}).symm.trans (({}).trans (congrArg M.number (by norm_num))))\n  have _litex_right_value : Litex.NativeBridge.asReal {rhs} {hb} = {s} := by\n    apply Complex.ofReal_injective\n    exact M.number_injective ((Litex.NativeBridge.asReal_spec {rhs} {hb}).symm.trans (({}).trans (congrArg M.number (by norm_num))))\n  exact Eq.mpr (congrArg₂ (fun _litex_r _litex_s : ℝ => {native_relation}) {low_value} {high_value}) (by norm_num)))",
            x.1, y.1,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_order_builtin(
        &self,
        goal: &AtomicFact,
        rule: &AtomicExceptEqualityFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match (goal, rule) {
            (
                AtomicFact::LessEqualFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(rule),
            ) => match rule {
                LessEqualFactSearchProofByBuiltinRule::OrderReflexivity(p) => {
                    self.compile_order_reflexivity(goal, &p.repeated_object, position)
                }
                LessEqualFactSearchProofByBuiltinRule::NumericLowerBoundFromStrictPredecessorLe(
                    p,
                ) => self.compile_integer_successor_lower_bound(
                    goal,
                    p.cite_fact_id,
                    &p.in_z_proof,
                    position,
                ),
                LessEqualFactSearchProofByBuiltinRule::MulLeftNonnegativeMonotone(p) => self
                    .compile_selected_mul_monotone(
                        goal,
                        &p.nonnegative_factor_proof,
                        &p.order_premise_proof,
                        true,
                        position,
                    ),
                LessEqualFactSearchProofByBuiltinRule::MulRightNonnegativeMonotone(p) => self
                    .compile_selected_mul_monotone(
                        goal,
                        &p.nonnegative_factor_proof,
                        &p.order_premise_proof,
                        false,
                        position,
                    ),
                LessEqualFactSearchProofByBuiltinRule::DivMonotoneWeakSamePosDivisor(p) => self
                    .compile_selected_div_monotone(
                        goal,
                        &p.divisor_pos_proof,
                        &p.numerators_order_proof,
                        position,
                    ),
                LessEqualFactSearchProofByBuiltinRule::LessEqualFromNonnegDifference(p) => {
                    self.compile_order_from_difference(goal, &p.premise_proof, false, position)
                }
                LessEqualFactSearchProofByBuiltinRule::LessEqualFromPosDivProductBound(p) => self
                    .compile_positive_div_product_bound(
                        goal,
                        &p.divisor_pos_proof,
                        &p.product_bound_proof,
                        position,
                    ),
                LessEqualFactSearchProofByBuiltinRule::FromKnownGreaterEqual(p) => self
                    .compile_order_known_conversion(
                        goal,
                        &p.premise_proof,
                        SourceOrderKind::GreaterEqual,
                        false,
                        position,
                    ),
                LessEqualFactSearchProofByBuiltinRule::FromKnownLess(p) => self
                    .compile_order_known_conversion(
                        goal,
                        &p.premise_proof,
                        SourceOrderKind::Less,
                        true,
                        position,
                    ),
                LessEqualFactSearchProofByBuiltinRule::EvenPowNonnegative(p) => {
                    self.compile_even_power_nonnegative(goal, &p.base_in_real_proof, position)
                }
                LessEqualFactSearchProofByBuiltinRule::AbsNonnegative(_) => {
                    let (zero, value, strict) = source_order_oriented(goal)?;
                    if strict
                        || !is_exact_zero(zero)
                        || !matches!(value, Obj::ArithmeticOperator(ArithmeticOperator::Abs(_)))
                    {
                        return Err(LeanCompileError::new("AbsNonnegative/OrderSubject", "The selected builtin must conclude the owned absolute value is nonnegative."));
                    }
                    let term = self.compile_object_reference(value, position)?;
                    Ok(format!("(by\n  let _litex_abs := {term}\n  exact Litex.absNonnegative _litex_abs.val.arg _litex_abs.wd\n)"))
                }
                LessEqualFactSearchProofByBuiltinRule::AddRightCongruence(p) => {
                    self.compile_weak_add_congruence(goal, &p.premise_proof, false, position)
                }
                LessEqualFactSearchProofByBuiltinRule::AddLeftCongruence(p) => {
                    self.compile_weak_add_congruence(goal, &p.premise_proof, true, position)
                }
                LessEqualFactSearchProofByBuiltinRule::LessEqualTransitivity(p) => self
                    .compile_weak_order_transitivity(
                        goal,
                        p.left_to_mid_cite_fact_id,
                        p.mid_to_right_cite_fact_id,
                        position,
                    ),
                _ => Err(LeanCompileError::unsupported("Order/LessEqualBuiltin")),
            },
            (
                AtomicFact::GreaterEqualFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(rule),
            ) => match rule {
                GreaterEqualFactSearchProofByBuiltinRule::OrderReflexivity(p) => {
                    self.compile_order_reflexivity(goal, &p.repeated_object, position)
                }
                GreaterEqualFactSearchProofByBuiltinRule::FromKnownLessEqual(p) => self
                    .compile_order_known_conversion(
                        goal,
                        &p.premise_proof,
                        SourceOrderKind::LessEqual,
                        false,
                        position,
                    ),
                GreaterEqualFactSearchProofByBuiltinRule::FromKnownGreater(p) => self
                    .compile_order_known_conversion(
                        goal,
                        &p.premise_proof,
                        SourceOrderKind::Greater,
                        true,
                        position,
                    ),
                GreaterEqualFactSearchProofByBuiltinRule::PredecessorNonNegFromAtLeastOne(p) => {
                    self.compile_predecessor_nonnegative_known(
                        goal,
                        &p.at_least_one_proof,
                        position,
                    )
                }
                _ => Err(LeanCompileError::unsupported("Order/GreaterEqualBuiltin")),
            },
            (
                AtomicFact::LessFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                    LessFactSearchProofByBuiltinRule::LessFromPosDifference(p),
                ),
            ) => self.compile_order_from_difference(goal, &p.premise_proof, true, position),
            (
                AtomicFact::LessFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                    LessFactSearchProofByBuiltinRule::SubtractOneLess(p),
                ),
            ) => self.compile_subtract_one_less(goal, &p.minuend, position),
            (
                AtomicFact::LessFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                    LessFactSearchProofByBuiltinRule::PowPositiveFromPositiveBase(p),
                ),
            ) => self.compile_power_positive(goal, &p.base_positive_proof, position),
            (
                AtomicFact::LessFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                    LessFactSearchProofByBuiltinRule::EvenPowPositiveFromNonzero(p),
                ),
            ) => self.compile_even_power_positive(
                goal,
                &p.base_in_real_proof,
                &p.base_nonzero_proof,
                position,
            ),
            (
                AtomicFact::LessFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                    LessFactSearchProofByBuiltinRule::SumBothPositive(proof),
                ),
            ) => self.compile_positive_sum_builtin(goal, proof, position),
            (
                AtomicFact::LessFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact(
                    LessFactSearchProofByBuiltinRule::FromKnownGreater(p),
                ),
            ) => self.compile_order_known_conversion(
                goal,
                &p.premise_proof,
                SourceOrderKind::Greater,
                false,
                position,
            ),
            (
                AtomicFact::GreaterFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(
                    GreaterFactSearchProofByBuiltinRule::FromPositiveRealMembership(p),
                ),
            ) => {
                let (zero, value, strict) = source_order_oriented(goal)?;
                if !strict
                    || !is_exact_zero(zero)
                    || membership_subject(&source_subject(&p.membership_proof)?, value)?
                        != StandardSet::RPos
                {
                    return Err(LeanCompileError::new("PositiveMembershipOrder/Subject", "The selected original R+ membership must describe the exact strictly positive goal object."));
                }
                Ok(format!(
                    "(Litex.inRPos_positive {} {})",
                    self.compile_object_reference(value, position)?,
                    self.compile_verify(&p.membership_proof, position)?.1
                ))
            }
            (
                AtomicFact::GreaterFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact(
                    GreaterFactSearchProofByBuiltinRule::FromKnownLess(p),
                ),
            ) => self.compile_order_known_conversion(
                goal,
                &p.premise_proof,
                SourceOrderKind::Less,
                false,
                position,
            ),
            (
                AtomicFact::NotEqualFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
                    NotEqualFactSearchProofByBuiltinRule::FromKnownStrictOrder(p),
                ),
            ) => self.compile_not_equal_from_known_strict_order(goal, &p.premise_proof, position),
            (
                AtomicFact::NotEqualFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
                    NotEqualFactSearchProofByBuiltinRule::DiffNonzeroFromInequality(p),
                ),
            ) => self.compile_difference_nonzero(goal, &p.operands_unequal_proof, position),
            (
                AtomicFact::NotEqualFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
                    NotEqualFactSearchProofByBuiltinRule::DivNonzeroFromFactors(p),
                ),
            ) => self.compile_quotient_nonzero(goal, &p.proof_of_requirement_facts, position),
            (
                AtomicFact::NotEqualFact(_),
                AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
                    NotEqualFactSearchProofByBuiltinRule::InequalityFromDifferenceNonzero(p),
                ),
            ) => self.compile_inequality_from_difference_nonzero(goal, &p.premise_proof, position),
            _ => Err(LeanCompileError::unsupported("Order/BuiltinFamilyOrRule")),
        }
    }

    pub(in crate::compile_to_lean) fn compile_order_reflexivity(
        &self,
        goal: &AtomicFact,
        repeated: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if strict || low.ir() != high.ir() || repeated.ir() != low.ir() {
            return Err(LeanCompileError::new(
                "Order/ReflexivitySubject",
                "Reflexivity must repeat the exact weak-order source object.",
            ));
        }
        Ok(format!(
            "(Litex.leRefl {} {})",
            self.compile_object_reference(low, position)?,
            self.compile_real_membership_certificate(low, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_order_known_premise(
        &self,
        premise: &AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        source_order_parts(&premise.fact)?;
        let proof = match premise.searched_proof.as_ref() {
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) => {
                self.compile_known_atomic(p, &premise.fact, position)?
            }
            _ => return Err(LeanCompileError::unsupported("Order/KnownPremiseRoute")),
        };
        Ok((
            self.compile_order_proposition(&premise.fact, position)?,
            proof,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_order_known_conversion(
        &self,
        goal: &AtomicFact,
        premise: &AtomicExceptEqualityFactKnownProof,
        expected_kind: SourceOrderKind,
        weaken: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (kind, _, _) = source_order_parts(&premise.fact)?;
        let (low, high, strict) = source_order_oriented(goal)?;
        let (known_low, known_high, known_strict) = source_order_oriented(&premise.fact)?;
        if kind != expected_kind
            || low.ir() != known_low.ir()
            || high.ir() != known_high.ir()
            || if weaken {
                strict || !known_strict
            } else {
                strict != known_strict
            }
        {
            return Err(LeanCompileError::new(
                "Order/KnownPremiseSubject",
                "The exact recorded converse or strict premise does not justify this source order.",
            ));
        }
        let proved = self.compile_order_known_premise(premise, position)?;
        if weaken {
            Ok(format!(
                "(Litex.ltToLe {} {} {})",
                self.compile_object_reference(low, position)?,
                self.compile_object_reference(high, position)?,
                proved.1
            ))
        } else {
            Ok(proved.1)
        }
    }

    pub(in crate::compile_to_lean) fn compile_even_power_nonnegative(
        &self,
        goal: &AtomicFact,
        base_proof: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (zero, value, strict) = source_order_oriented(goal)?;
        if strict || !is_zero(zero) {
            return Err(LeanCompileError::new(
                "Order/EvenPowerSubject",
                "The selected certificate must prove the weak lower bound zero.",
            ));
        }
        let base = match value {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) if p.left.ir() == p.right.ir() => {
                p.left.as_ref()
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => p.base.as_ref(),
            _ => return Err(LeanCompileError::unsupported("Order/EvenPowerConstructor")),
        };
        let proved = self.compile_verify(base_proof, position)?;
        if membership_subject(&source_subject(base_proof)?, base)? != StandardSet::R {
            return Err(LeanCompileError::new(
                "Order/EvenPowerBase",
                "The recorded child must prove this exact base belongs to R.",
            ));
        }
        match value {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(_)) => Ok(format!(
                "(Litex.mulSelfNonnegative {} {})",
                self.compile_object_reference(base, position)?,
                proved.1
            )),
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) => {
                if !matches!(p.exponent.as_ref(), Obj::Literal(Literal::Number(_))) {
                    return Err(LeanCompileError::unsupported(
                        "Order/EvenPowerLiteralExponent",
                    ));
                }
                let n = closed_integer(&p.exponent)
                    .filter(|n| *n >= 0 && n % 2 == 0)
                    .ok_or_else(|| {
                        LeanCompileError::new(
                            "Order/EvenPowerExponent",
                            "The exact source literal must be an even natural integer.",
                        )
                    })?;
                let exponent = self.compile_numeric_observation(&p.exponent, position)?;
                let he = format!("(Litex.NativeBridge.sameOfDenoteNumber {} (Litex.number (M := M) (({n} : ℕ) : ℂ)) {} (({n} : ℕ) : ℂ) {} (Litex.NativeBridge.denoteNumber (M := M) (({n} : ℕ) : ℂ)) (by norm_num))",
                    self.compile_object_reference(&p.exponent, position)?, exponent.0, exponent.1);
                Ok(format!(
                    "(Litex.powStructuralNonnegativeOfEven {} {} ({n} : ℕ) {he} (by norm_num))",
                    self.compile_object_reference(value, position)?,
                    proved.1
                ))
            }
            _ => unreachable!("the supported constructor was checked before replaying its child"),
        }
    }

    pub(in crate::compile_to_lean) fn compile_weak_add_congruence(
        &self,
        goal: &AtomicFact,
        premise: &VerifyFactResult,
        common_left: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if strict {
            return Err(LeanCompileError::unsupported("Order/StrictAddCongruence"));
        }
        let (lhs, rhs) = match (low, high) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(lhs)),
                Obj::ArithmeticOperator(ArithmeticOperator::Add(rhs)),
            ) => (lhs, rhs),
            _ => {
                return Err(LeanCompileError::new(
                    "Order/AddConstructor",
                    "The selected add congruence requires two exact owned Add constructions.",
                ))
            }
        };
        let (a, b, c, d) = if common_left {
            (
                lhs.right.as_ref(),
                rhs.right.as_ref(),
                lhs.left.as_ref(),
                rhs.left.as_ref(),
            )
        } else {
            (
                lhs.left.as_ref(),
                rhs.left.as_ref(),
                lhs.right.as_ref(),
                rhs.right.as_ref(),
            )
        };
        if c.ir() != d.ir() {
            return Err(LeanCompileError::new(
                "Order/AddCommonArgument",
                "The exact common source addend differs between the two sums.",
            ));
        }
        let proved = self.compile_verify(premise, position)?;
        match &source_subject(premise)? {
            Fact::AtomicFact(AtomicFact::LessEqualFact(f)) if f.left.ir() == a.ir() && f.right.ir() == b.ir() =>
                {},
            _ => return Err(LeanCompileError::new("Order/AddPremise", "The recorded child must prove the exact ordered weak comparison between the noncommon addends.")),
        };
        // Parent predicate WD and its recursively replayed real membership
        // children provide this common addend's real classification. Each
        // complex certificate comes from an already certified operand object.
        let function = if common_left {
            "leAddLeft"
        } else {
            "leAddRight"
        };
        Ok(format!(
            "(Litex.{function} {} {} {} {} {} {} {} {})",
            self.compile_object_reference(a, position)?,
            self.compile_object_reference(b, position)?,
            self.compile_object_reference(c, position)?,
            self.compile_numeric_observation(a, position)?.2,
            self.compile_numeric_observation(b, position)?.2,
            self.compile_numeric_observation(c, position)?.2,
            self.compile_real_membership_certificate(c, position)?,
            proved.1
        ))
    }

    pub(in crate::compile_to_lean) fn order_real_members_from_known(
        &self,
        fact: &AtomicFact,
        order_proof: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        // Use only at the actual predicate-domain ByKnownFact stage after its
        // citation and argument transport have been replayed successfully.
        let (kind, _, _) = source_order_parts(fact)?;
        let (low, high, _) = source_order_oriented(fact)?;
        let low_member = format!("(by obtain ⟨_litex_real, _, _litex_value, _, _⟩ := {order_proof}; exact (M.real_members (Litex.denote {})).mpr ⟨_litex_real, _litex_value⟩)", self.compile_object_reference(low, position)?);
        let high_member = format!("(by obtain ⟨_, _litex_real, _, _litex_value, _⟩ := {order_proof}; exact (M.real_members (Litex.denote {})).mpr ⟨_litex_real, _litex_value⟩)", self.compile_object_reference(high, position)?);
        match kind {
            SourceOrderKind::Less | SourceOrderKind::LessEqual => Ok((low_member, high_member)),
            SourceOrderKind::Greater | SourceOrderKind::GreaterEqual => {
                Ok((high_member, low_member))
            }
        }
    }

    pub(in crate::compile_to_lean) fn compile_registered_order<'p>(
        &'p self,
        id: FactId,
        position: &SourcePosition<'p>,
    ) -> Result<(&'p AtomicFact, String), LeanCompileError> {
        let (fact, reference) = self.cited_fact_reference(id, position)?;
        let atomic = match fact {
            Fact::AtomicFact(fact) if fact.fact_id() == id => fact,
            _ => {
                return Err(LeanCompileError::new(
                    "Order/CitationFamily",
                    "The recorded order citation has another fact family or identity.",
                ))
            }
        };
        source_order_parts(atomic)?;
        Ok((atomic, reference))
    }

    pub(in crate::compile_to_lean) fn compile_weak_order_transitivity(
        &self,
        goal: &AtomicFact,
        first_id: FactId,
        second_id: FactId,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (left, right, strict) = source_order_oriented(goal)?;
        if strict {
            return Err(LeanCompileError::unsupported("Order/StrictTransitivity"));
        }
        let first = self.compile_registered_order(first_id, position)?;
        let second = self.compile_registered_order(second_id, position)?;
        let first_atomic = first.0;
        let second_atomic = second.0;
        let (a, b, first_strict) = source_order_oriented(first_atomic)?;
        let (b2, c, second_strict) = source_order_oriented(second_atomic)?;
        if a.ir() != left.ir() || b.ir() != b2.ir() || c.ir() != right.ir() {
            return Err(LeanCompileError::new("Order/TransitivitySubject", "The exact two recorded citations do not form this ordered left-middle-right chain."));
        }
        let first_proof = if first_strict {
            format!(
                "(Litex.ltToLe {} {} {})",
                self.compile_object_reference(a, position)?,
                self.compile_object_reference(b, position)?,
                first.1
            )
        } else {
            first.1
        };
        let second_proof = if second_strict {
            format!(
                "(Litex.ltToLe {} {} {})",
                self.compile_object_reference(b2, position)?,
                self.compile_object_reference(c, position)?,
                second.1
            )
        } else {
            second.1
        };
        Ok(format!(
            "(Litex.leTrans {} {} {} {first_proof} {second_proof})",
            self.compile_object_reference(a, position)?,
            self.compile_object_reference(b, position)?,
            self.compile_object_reference(c, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_order_dual(
        &self,
        goal: &AtomicFact,
        proof: &AtomicExceptEqualityFactSearchProofByBuiltinOrderDual,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (kind, left, right) = source_order_parts(goal)?;
        let alternate = match &proof.alternate_fact {
            Fact::AtomicFact(f) => f,
            _ => {
                return Err(LeanCompileError::new(
                    "Order/DualFamily",
                    "The recorded alternate is not an atomic order fact.",
                ))
            }
        };
        let (alternate_kind, alternate_left, alternate_right) = source_order_parts(alternate)?;
        let expected = match kind {
            SourceOrderKind::Less => SourceOrderKind::Greater,
            SourceOrderKind::Greater => SourceOrderKind::Less,
            SourceOrderKind::LessEqual => SourceOrderKind::GreaterEqual,
            SourceOrderKind::GreaterEqual => SourceOrderKind::LessEqual,
        };
        if alternate_kind != expected
            || left.ir() != alternate_right.ir()
            || right.ir() != alternate_left.ir()
        {
            return Err(LeanCompileError::new(
                "Order/DualSubject",
                "The recorded alternate changes the exact transposed family or source endpoints.",
            ));
        }
        let child = self.compile_verify(&proof.proof_of_alternate_fact, position)?;
        if source_subject(&proof.proof_of_alternate_fact)? != proof.alternate_fact {
            return Err(LeanCompileError::new(
                "Order/DualChild",
                "The successful child does not prove the exact recorded alternate fact.",
            ));
        }
        Ok(child.1)
    }

    pub(in crate::compile_to_lean) fn compile_not_equal_from_known_strict_order(
        &self,
        goal: &AtomicFact,
        premise: &AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (left, right) = match goal {
            AtomicFact::NotEqualFact(f) => (&f.left, &f.right),
            _ => {
                return Err(LeanCompileError::new(
                    "Order/NotEqualFamily",
                    "Strict-order inequality evidence has another target predicate.",
                ))
            }
        };
        let (low, high, strict) = source_order_oriented(&premise.fact)?;
        if !strict
            || !((low.ir() == left.ir() && high.ir() == right.ir())
                || (low.ir() == right.ir() && high.ir() == left.ir()))
        {
            return Err(LeanCompileError::new(
                "Order/NotEqualPremise",
                "The recorded strict-order premise must have exactly these two source endpoints.",
            ));
        }
        let child = self.compile_order_known_premise(premise, position)?;
        let inequality = format!(
            "(Litex.ltNotSame {} {} {})",
            self.compile_object_reference(low, position)?,
            self.compile_object_reference(high, position)?,
            child.1
        );
        if low.ir() == left.ir() && high.ir() == right.ir() {
            Ok(inequality)
        } else {
            Ok(format!(
                "(fun _litex_equal => {inequality} _litex_equal.symm)"
            ))
        }
    }

    pub(in crate::compile_to_lean) fn compile_difference_nonzero(
        &self,
        goal: &AtomicFact,
        premise: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotEqualFact(fact) = goal else {
            return Err(LeanCompileError::unsupported("NonzeroDifference/Family"));
        };
        let Fact::AtomicFact(AtomicFact::NotEqualFact(operands)) = source_subject(premise)? else {
            return Err(LeanCompileError::new(
                "NonzeroDifference/Premise",
                "The recorded child must prove inequality of the exact ordered subtraction operands.",
            ));
        };
        // The selected rule owns the route. Its exact child disambiguates the
        // subtraction endpoint when the closed zero is itself a subtraction.
        let matches_operands = |sub: &Sub| {
            operands.left.ir() == sub.left.ir() && operands.right.ir() == sub.right.ir()
        };
        let (difference, zero, reversed) = match (&fact.left, &fact.right) {
            (Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)), zero)
                if matches_operands(sub) =>
            {
                (sub, zero, false)
            }
            (zero, Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)))
                if matches_operands(sub) =>
            {
                (sub, zero, true)
            }
            _ => {
                return Err(LeanCompileError::new(
                    "NonzeroDifference/Premise",
                    "The recorded inequality has different or reordered subtraction operands.",
                ))
            }
        };
        let zero_value = self.compile_numeric_observation(zero, position)?;
        if !zero_value.3.as_ref().is_some_and(EvalRational::is_zero) {
            return Err(LeanCompileError::new(
                "NonzeroDifference/Zero",
                "The selected difference rule requires an exactly certified zero endpoint.",
            ));
        }
        let child = self.compile_verify(premise, position)?;
        let left = self.compile_numeric_observation(&difference.left, position)?;
        let right = self.compile_numeric_observation(&difference.right, position)?;
        let nonzero = format!(
            "(Litex.subNonzeroOfNotSame {} {} {} {} {})",
            self.compile_object_reference(&difference.left, position)?,
            self.compile_object_reference(&difference.right, position)?,
            left.2,
            right.2,
            child.1,
        );
        let equality = if reversed {
            "_litex_equal.symm"
        } else {
            "_litex_equal"
        };
        Ok(format!(
            "(fun _litex_equal => {nonzero} (({equality}).trans (({}).trans (congrArg M.number (by norm_num : {} = (0 : ℂ))))))",
            zero_value.1,
            zero_value.0,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_quotient_nonzero(
        &self,
        goal: &AtomicFact,
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotEqualFact(fact) = goal else {
            return Err(LeanCompileError::unsupported("NonzeroQuotient/Family"));
        };
        if proofs.len() != 2 {
            return Err(LeanCompileError::new(
                "NonzeroQuotient/Requirements",
                "The selected quotient rule requires exactly two ordered factor proofs.",
            ));
        }
        let numerator = source_subject(&proofs[0])?;
        let denominator = source_subject(&proofs[1])?;
        let matches_factors = |div: &Div| {
            ensure_nonzero_subject(&numerator, &div.left).is_ok()
                && ensure_nonzero_subject(&denominator, &div.right).is_ok()
        };
        let (quotient, zero, reversed) = match (&fact.left, &fact.right) {
            (Obj::ArithmeticOperator(ArithmeticOperator::Div(div)), zero) if matches_factors(div) => (div, zero, false),
            (zero, Obj::ArithmeticOperator(ArithmeticOperator::Div(div))) if matches_factors(div) => (div, zero, true),
            _ => return Err(LeanCompileError::new("NonzeroQuotient/Subjects", "The selected children must prove nonzero of the exact numerator and denominator, in that order.")),
        };
        let zero_value = self.compile_numeric_observation(zero, position)?;
        if !zero_value.3.as_ref().is_some_and(EvalRational::is_zero) {
            return Err(LeanCompileError::new(
                "NonzeroQuotient/Zero",
                "The selected quotient rule requires an exactly certified zero endpoint.",
            ));
        }
        let first = self.compile_verify(&proofs[0], position)?;
        let second = self.compile_verify(&proofs[1], position)?;
        let left = self.compile_numeric_observation(&quotient.left, position)?;
        let right = self.compile_numeric_observation(&quotient.right, position)?;
        let nonzero = format!(
            "(Litex.divNonzero {} {} {} {} {} {})",
            self.compile_object_reference(&quotient.left, position)?,
            self.compile_object_reference(&quotient.right, position)?,
            left.2,
            right.2,
            first.1,
            second.1
        );
        let equality = if reversed {
            "_litex_equal.symm"
        } else {
            "_litex_equal"
        };
        Ok(format!("(fun _litex_equal => {nonzero} (({equality}).trans (({}).trans (congrArg M.number (by norm_num : {} = (0 : ℂ))))))", zero_value.1, zero_value.0))
    }

    pub(in crate::compile_to_lean) fn compile_inequality_from_difference_nonzero(
        &self,
        goal: &AtomicFact,
        premise: &AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotEqualFact(fact) = goal else {
            return Err(LeanCompileError::unsupported("DifferenceInequality/Family"));
        };
        let AtomicFact::NotEqualFact(known) = &premise.fact else {
            return Err(LeanCompileError::unsupported(
                "DifferenceInequality/PremiseFamily",
            ));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = &known.left else {
            return Err(LeanCompileError::unsupported(
                "DifferenceInequality/Constructor",
            ));
        };
        if !is_zero(&known.right) {
            return Err(LeanCompileError::new(
                "DifferenceInequality/Zero",
                "The recorded known difference must be compared with literal zero.",
            ));
        }
        let forward = sub.left.ir() == fact.left.ir() && sub.right.ir() == fact.right.ir();
        let reverse = sub.left.ir() == fact.right.ir() && sub.right.ir() == fact.left.ir();
        if !forward && !reverse {
            return Err(LeanCompileError::new(
                "DifferenceInequality/Subjects",
                "The recorded difference has other source endpoints.",
            ));
        }
        let proof = match premise.searched_proof.as_ref() {
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) => {
                self.compile_known_atomic(p, &premise.fact, position)?
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "DifferenceInequality/KnownRoute",
                ))
            }
        };
        let left = self.compile_numeric_observation(&sub.left, position)?;
        let right = self.compile_numeric_observation(&sub.right, position)?;
        let inequality = format!(
            "(Litex.notSameOfSubNonzero {} {} {} {} {})",
            self.compile_object_reference(&sub.left, position)?,
            self.compile_object_reference(&sub.right, position)?,
            left.2,
            right.2,
            proof
        );
        Ok(if forward {
            inequality
        } else {
            format!("(fun h => {inequality} h.symm)")
        })
    }

    pub(in crate::compile_to_lean) fn compile_order_known_atomic_transport(
        &self,
        cited: &AtomicFact,
        goal: &AtomicFact,
        argument_equalities: &[String],
        citation_proof: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (kind, _, _) = source_order_parts(cited)?;
        let (goal_kind, _, _) = source_order_parts(goal)?;
        if kind != goal_kind || argument_equalities.len() != 2 {
            return Err(LeanCompileError::new(
                "Order/KnownTransportFamily",
                "Recorded order transport changes its source family or ordered argument arity.",
            ));
        }
        let (old_low, old_high, strict) = source_order_oriented(cited)?;
        let (new_low, new_high, _) = source_order_oriented(goal)?;
        let (low_equality, high_equality) = match kind {
            SourceOrderKind::Less | SourceOrderKind::LessEqual => {
                (&argument_equalities[0], &argument_equalities[1])
            }
            SourceOrderKind::Greater | SourceOrderKind::GreaterEqual => {
                (&argument_equalities[1], &argument_equalities[0])
            }
        };
        Ok(format!(
            "(Litex.{} {} {} {} {} {low_equality} {high_equality} {citation_proof})",
            if strict { "ltOfSame" } else { "leOfSame" },
            self.compile_object_reference(old_low, position)?,
            self.compile_object_reference(new_low, position)?,
            self.compile_object_reference(old_high, position)?,
            self.compile_object_reference(new_high, position)?
        ))
    }
}
