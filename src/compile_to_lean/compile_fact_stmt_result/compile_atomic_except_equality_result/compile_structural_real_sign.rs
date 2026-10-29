//! Replay the positive quotient certificate selected by the current verifier.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_real_sign_proof::{
    RealSign, StructuralRealSignProof, StructuralRealSignReason,
};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("StructuralPositive/{stage}"))
}

impl LitexToLeanCompiler {
    pub(super) fn compile_structural_positive_order(
        &self,
        goal: &AtomicFact,
        proof: &StructuralRealSignProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (zero, element, strict) = source_order_oriented(goal)?;
        if !strict || !is_zero(zero) || element.ir() != proof.element.ir() {
            return Err(invalid("Goal"));
        }
        self.compile_structural_positive(proof, position)
    }

    fn compile_structural_positive(
        &self,
        proof: &StructuralRealSignProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if proof.sign != RealSign::Positive {
            return Err(invalid("Sign"));
        }
        match &proof.reason {
            StructuralRealSignReason::WeakAndNonzero {
                real,
                weak,
                nonzero,
            } => {
                if real.element.ir() != proof.element.ir() || real.set != StandardSet::R {
                    return Err(invalid("KnownReal"));
                }
                let (zero, element, strict) = source_order_oriented(&weak.fact)?;
                if strict || !is_zero(zero) || element.ir() != proof.element.ir() {
                    return Err(invalid("KnownSubject"));
                }
                let real = self.compile_structural(real, position)?;
                let weak = self.compile_order_known_premise(weak, position)?.1;
                let nonzero =
                    self.compile_sign_nonzero_citation(&proof.element, nonzero, position)?;
                let object = self.compile_object_reference(&proof.element, position)?;
                Ok(format!("(by\n  have _sign_real := {real}\n  rcases Litex.leEqOrLt (Litex.number (M := M) 0) {object} ({weak}) with h | h\n  · exact False.elim (({nonzero}) h.symm)\n  · exact h\n)"))
            }
            StructuralRealSignReason::WeakSignAndNonzero { weak, nonzero } => {
                if weak.element.ir() != proof.element.ir()
                    || nonzero.element.ir() != proof.element.ir()
                {
                    return Err(invalid("StrengtheningSubject"));
                }
                let weak = self.compile_structural_nonnegative(weak, position)?;
                let nonzero = self.compile_structural_nonzero(nonzero, position)?;
                let object = self.compile_object_reference(&proof.element, position)?;
                Ok(format!("(by\n  rcases Litex.leEqOrLt (Litex.number (M := M) 0) {object} ({weak}) with h | h\n  · exact False.elim (({nonzero}) h.symm)\n  · exact h\n)"))
            }
            StructuralRealSignReason::PositiveSqrt { argument } => {
                let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root)) = &proof.element else {
                    return Err(invalid("SqrtConstructor"));
                };
                if root.arg.ir() != argument.element.ir() {
                    return Err(invalid("SqrtSubject"));
                }
                let positive = self.compile_structural_positive(argument, position)?;
                let object = self.compile_object_reference(&proof.element, position)?;
                Ok(format!("(by\n  let _sign_root := {object}\n  rcases Litex.leEqOrLt (Litex.number (M := M) 0) _sign_root (Litex.sqrtNonnegative _sign_root.val.arg _sign_root.wd.1 _sign_root.wd.2) with h | h\n  · exact False.elim (Litex.sqrtNonzeroOfPositive _sign_root ({positive}) h.symm)\n  · exact h\n)"))
            }
            StructuralRealSignReason::Known { real, source } => {
                if real.element.ir() != proof.element.ir() || real.set != StandardSet::R {
                    return Err(invalid("KnownReal"));
                }
                let (zero, element, strict) = source_order_oriented(&source.fact)?;
                if !strict || !is_zero(zero) || element.ir() != proof.element.ir() {
                    return Err(invalid("KnownSubject"));
                }
                let real = self.compile_structural(real, position)?;
                let cited = self.compile_order_known_premise(source, position)?.1;
                Ok(format!(
                    "(by\n  have _sign_real := {real}\n  exact {cited}\n)"
                ))
            }
            StructuralRealSignReason::Membership(member) => {
                if member.element.ir() != proof.element.ir() || member.set != StandardSet::RPos {
                    return Err(invalid("PositiveMembership"));
                }
                Ok(format!(
                    "(Litex.inRPos_positive {} {})",
                    self.compile_object_reference(&proof.element, position)?,
                    self.compile_structural(member, position)?
                ))
            }
            StructuralRealSignReason::Closed(closed) => {
                let ClosedAtomicExceptEqualityCalculationProof::Less(closed) = closed.as_ref()
                else {
                    return Err(invalid("ClosedFamily"));
                };
                let zero = Obj::Literal(Literal::Number(Number::new("0".into())));
                let endpoint_real = |obj: &Obj| -> Result<String, LeanCompileError> {
                    let observed = self.compile_numeric_observation(obj, position)?;
                    let value = exact_rational_literal(
                        observed.3.as_ref().ok_or_else(|| invalid("ClosedValue"))?,
                        "ℝ",
                    )?;
                    Ok(format!("((M.real_members _).mpr ⟨{value}, ({}).trans (congrArg M.number (by norm_num))⟩)", observed.1))
                };
                self.compile_closed_order_endpoints(
                    SourceOrderKind::Less,
                    &zero,
                    &proof.element,
                    closed,
                    false,
                    Some((&endpoint_real(&zero)?, &endpoint_real(&proof.element)?)),
                    position,
                )
            }
            StructuralRealSignReason::Div { left, right } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Div(q)) = &proof.element else {
                    return Err(invalid("Division"));
                };
                if q.left.ir() != left.element.ir() || q.right.ir() != right.element.ir() {
                    return Err(invalid("DivisionOperands"));
                }
                let left = self.compile_structural_positive(left, position)?;
                let right = self.compile_structural_positive(right, position)?;
                let quotient = self.compile_object_reference(&proof.element, position)?;
                Ok(format!("(by\n  let _sign_quotient := {quotient}\n  have _sign_left : Litex.Lt (Litex.number (M := M) 0) _sign_quotient.val.left :=\n    {}\n  have _sign_right : Litex.Lt (Litex.number (M := M) 0) _sign_quotient.val.right :=\n    {}\n  exact Litex.divPositive _sign_quotient.val.left _sign_quotient.val.right _sign_quotient.wd.1 _sign_quotient.wd.2.1 _sign_quotient.wd.2.2 _sign_left _sign_right\n)", left.replace('\n', "\n    "), right.replace('\n', "\n    ")))
            }
            StructuralRealSignReason::Add { left, right }
            | StructuralRealSignReason::Mul { left, right } => {
                let (a, b, product) = match &proof.element {
                    Obj::ArithmeticOperator(ArithmeticOperator::Add(v))
                        if matches!(&proof.reason, StructuralRealSignReason::Add { .. }) =>
                    {
                        (&v.left, &v.right, false)
                    }
                    Obj::ArithmeticOperator(ArithmeticOperator::Mul(v))
                        if matches!(&proof.reason, StructuralRealSignReason::Mul { .. }) =>
                    {
                        (&v.left, &v.right, true)
                    }
                    _ => return Err(invalid("BinaryConstructor")),
                };
                if a.ir() != left.element.ir() || b.ir() != right.element.ir() {
                    return Err(invalid("BinaryOperands"));
                }
                let (rule, lhs, rhs) =
                    if left.sign == RealSign::Positive && right.sign == RealSign::Positive {
                        (
                            if product {
                                "mulPositive"
                            } else {
                                "addPositive"
                            },
                            self.compile_structural_positive(left, position)?,
                            self.compile_structural_positive(right, position)?,
                        )
                    } else if !product
                        && left.sign == RealSign::Positive
                        && right.sign.implies(RealSign::Nonnegative)
                    {
                        (
                            "addPositiveLeft",
                            self.compile_structural_positive(left, position)?,
                            self.compile_structural_nonnegative(right, position)?,
                        )
                    } else if !product
                        && right.sign == RealSign::Positive
                        && left.sign.implies(RealSign::Nonnegative)
                    {
                        (
                            "addPositiveRight",
                            self.compile_structural_nonnegative(left, position)?,
                            self.compile_structural_positive(right, position)?,
                        )
                    } else {
                        return Err(invalid("BinarySigns"));
                    };
                let object = self.compile_object_reference(&proof.element, position)?;
                Ok(format!("(by\n  let _sign_binary := {object}\n  exact Litex.{rule} _sign_binary.val.left _sign_binary.val.right _sign_binary.wd.1 _sign_binary.wd.2 ({lhs}) ({rhs})\n)"))
            }
            StructuralRealSignReason::PositivePower {
                base,
                exponent_real,
            } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) = &proof.element else {
                    return Err(invalid("PositivePower"));
                };
                if p.base.ir() != base.element.ir()
                    || p.exponent.ir() != exponent_real.element.ir()
                    || exponent_real.set != StandardSet::R
                {
                    return Err(invalid("PositivePowerSubject"));
                }
                let power = self.compile_object_reference(&proof.element, position)?;
                let exponent = self.compile_structural(exponent_real, position)?;
                let base = self.compile_structural_positive(base, position)?;
                Ok(format!("(by\n  let _sign_power := {power}\n  have _sign_exponent_real : Litex.In _sign_power.val.exponent (Litex.R (M := M)) :=\n    {}\n  have _sign_base : Litex.Lt (Litex.number (M := M) 0) _sign_power.val.base :=\n    {}\n  exact Litex.powStructuralPositiveOfPositive _sign_power _sign_base\n)", exponent.replace('\n', "\n    "), base.replace('\n', "\n    ")))
            }
            _ => Err(invalid("SelectedReason")),
        }
    }

    pub(super) fn compile_structural_nonnegative_order(
        &self,
        goal: &AtomicFact,
        proof: &StructuralRealSignProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (zero, element, strict) = source_order_oriented(goal)?;
        if strict {
            return Err(invalid("WeakGoal"));
        }
        if is_zero(element)
            && zero.ir() == proof.element.ir()
            && proof.sign == RealSign::Nonpositive
        {
            return self.compile_structural_nonpositive(proof, position);
        }
        if !is_zero(zero) || element.ir() != proof.element.ir() {
            return Err(invalid("WeakGoal"));
        }
        self.compile_structural_nonnegative(proof, position)
    }

    fn compile_structural_nonnegative(
        &self,
        proof: &StructuralRealSignProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let element = &proof.element;
        if proof.sign == RealSign::Zero
            && matches!(proof.reason, StructuralRealSignReason::ZeroLiteral)
            && is_zero(element)
        {
            return Ok("(Litex.leRefl (Litex.number (M := M) 0) (Litex.NativeBridge.numberInROfEq (M := M) 0 0 (by norm_num)))".into());
        }
        if proof.sign == RealSign::Positive {
            return Ok(format!(
                "(Litex.ltToLe (Litex.number (M := M) 0) {} {})",
                self.compile_object_reference(element, position)?,
                self.compile_structural_positive(proof, position)?
            ));
        }
        if proof.sign != RealSign::Nonnegative {
            return Err(invalid("WeakSign"));
        }
        match &proof.reason {
            StructuralRealSignReason::NonnegativeSqrt { argument_real } => {
                let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root)) = element else {
                    return Err(invalid("SqrtConstructor"));
                };
                if root.arg.ir() != argument_real.element.ir()
                    || argument_real.set != StandardSet::R
                {
                    return Err(invalid("SqrtSubject"));
                }
                let real = self.compile_structural(argument_real, position)?;
                let object = self.compile_object_reference(element, position)?;
                return Ok(format!("(by\n  have _sign_real := {real}\n  let _sign_root := {object}\n  exact Litex.sqrtNonnegative _sign_root.val.arg _sign_root.wd.1 _sign_root.wd.2\n)"));
            }
            StructuralRealSignReason::NonnegativeAbs { argument_real } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = element else {
                    return Err(invalid("AbsConstructor"));
                };
                if abs.arg.ir() != argument_real.element.ir() || argument_real.set != StandardSet::R
                {
                    return Err(invalid("AbsSubject"));
                }
                let real = self.compile_structural(argument_real, position)?;
                let object = self.compile_object_reference(element, position)?;
                return Ok(format!("(by\n  have _sign_real := {real}\n  let _sign_abs := {object}\n  exact Litex.absNonnegative _sign_abs.val.arg _sign_abs.wd\n)"));
            }
            StructuralRealSignReason::Known { real, source } => {
                if real.element.ir() != element.ir() || real.set != StandardSet::R {
                    return Err(invalid("KnownReal"));
                }
                let (zero, subject, strict) = source_order_oriented(&source.fact)?;
                if strict || !is_zero(zero) || subject.ir() != element.ir() {
                    return Err(invalid("KnownSubject"));
                }
                let real = self.compile_structural(real, position)?;
                let cited = self.compile_order_known_premise(source, position)?.1;
                return Ok(format!(
                    "(by\n  have _sign_real := {real}\n  exact {cited}\n)"
                ));
            }
            StructuralRealSignReason::Add { left, right }
            | StructuralRealSignReason::Mul { left, right } => {
                let (a, b, rule) = match (element, &proof.reason) {
                    (
                        Obj::ArithmeticOperator(ArithmeticOperator::Add(v)),
                        StructuralRealSignReason::Add { .. },
                    ) => (&v.left, &v.right, "addNonnegative"),
                    (
                        Obj::ArithmeticOperator(ArithmeticOperator::Mul(v)),
                        StructuralRealSignReason::Mul { .. },
                    ) => (&v.left, &v.right, "mulNonnegative"),
                    _ => return Err(invalid("BinaryConstructor")),
                };
                if a.ir() != left.element.ir() || b.ir() != right.element.ir() {
                    return Err(invalid("BinaryOperands"));
                }
                let lhs = self.compile_structural_nonnegative(left, position)?;
                let rhs = self.compile_structural_nonnegative(right, position)?;
                let object = self.compile_object_reference(element, position)?;
                return Ok(format!("(by\n  let _sign_sum := {object}\n  exact Litex.{rule} _sign_sum.val.left _sign_sum.val.right _sign_sum.wd.1 _sign_sum.wd.2 ({lhs}) ({rhs})\n)"));
            }
            StructuralRealSignReason::Div { left, right } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Div(v)) = element else {
                    return Err(invalid("Division"));
                };
                if v.left.ir() != left.element.ir() || v.right.ir() != right.element.ir() {
                    return Err(invalid("DivisionOperands"));
                }
                let lhs = self.compile_structural_nonnegative(left, position)?;
                let rhs = self.compile_structural_positive(right, position)?;
                let object = self.compile_object_reference(element, position)?;
                return Ok(format!(
                    "(Litex.divStructuralNonnegative {object} ({rhs}) ({lhs}))"
                ));
            }
            _ => {}
        }
        let StructuralRealSignReason::NonnegativeEvenPower {
            base_real,
            exponent,
        } = &proof.reason
        else {
            return Err(invalid("WeakReason"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Pow(p)) = element else {
            return Err(invalid("EvenPower"));
        };
        let n = closed_integer(exponent)
            .filter(|n| *n >= 0 && *n % 2 == 0)
            .ok_or_else(|| invalid("EvenExponent"))?;
        if p.base.ir() != base_real.element.ir()
            || base_real.set != StandardSet::R
            || p.exponent.ir() != exponent.ir()
        {
            return Err(invalid("EvenSubject"));
        }
        let observed = self.compile_numeric_observation(exponent, position)?;
        let he = format!("(Litex.NativeBridge.sameOfDenoteNumber {} (Litex.number (M := M) (({n} : ℕ) : ℂ)) {} (({n} : ℕ) : ℂ) {} (Litex.NativeBridge.denoteNumber (M := M) (({n} : ℕ) : ℂ)) (by norm_num))",
            self.compile_object_reference(exponent, position)?, observed.0, observed.1);
        Ok(format!(
            "(Litex.powStructuralNonnegativeOfEven {} {} ({n} : ℕ) {he} (by norm_num))",
            self.compile_object_reference(element, position)?,
            self.compile_structural(base_real, position)?
        ))
    }

    fn compile_structural_nonpositive(
        &self,
        proof: &StructuralRealSignProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if proof.sign != RealSign::Nonpositive {
            return Err(invalid("NonpositiveSign"));
        }
        match &proof.reason {
            StructuralRealSignReason::Known { real, source } => {
                let (subject, zero, strict) = source_order_oriented(&source.fact)?;
                if strict
                    || !is_zero(zero)
                    || subject.ir() != proof.element.ir()
                    || real.element.ir() != proof.element.ir()
                    || real.set != StandardSet::R
                {
                    return Err(invalid("KnownSubject"));
                }
                let real = self.compile_structural(real, position)?;
                let cited = self.compile_order_known_premise(source, position)?.1;
                Ok(format!(
                    "(by\n  have _sign_real := {real}\n  exact {cited}\n)"
                ))
            }
            StructuralRealSignReason::Div { left, right } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Div(v)) = &proof.element else {
                    return Err(invalid("Division"));
                };
                if v.left.ir() != left.element.ir() || v.right.ir() != right.element.ir() {
                    return Err(invalid("DivisionOperands"));
                }
                let lhs = self.compile_structural_nonpositive(left, position)?;
                let rhs = self.compile_structural_positive(right, position)?;
                let object = self.compile_object_reference(&proof.element, position)?;
                Ok(format!(
                    "(Litex.divStructuralNonpositive {object} ({rhs}) ({lhs}))"
                ))
            }
            _ => Err(invalid("NonpositiveReason")),
        }
    }

    pub(super) fn compile_structural_nonzero_order(
        &self,
        goal: &AtomicFact,
        proof: &StructuralRealSignProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotEqualFact(fact) = goal else {
            return Err(invalid("NonzeroGoal"));
        };
        let reverse = if fact.left.ir() == proof.element.ir() && is_zero(&fact.right) {
            false
        } else if is_zero(&fact.left) && fact.right.ir() == proof.element.ir() {
            true
        } else {
            return Err(invalid("NonzeroGoal"));
        };
        let value = self.compile_structural_nonzero(proof, position)?;
        Ok(if reverse {
            format!("(fun h => ({value}) h.symm)")
        } else {
            value
        })
    }

    fn compile_structural_nonzero(
        &self,
        proof: &StructuralRealSignProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let object = self.compile_object_reference(&proof.element, position)?;
        if proof.sign == RealSign::Positive {
            let positive = self.compile_structural_positive(proof, position)?;
            return Ok(format!(
                "(fun h => Litex.ltNotSame (Litex.number (M := M) 0) {object} ({positive}) h.symm)"
            ));
        }
        if proof.sign != RealSign::Nonzero {
            return Err(invalid("NonzeroSign"));
        }
        match &proof.reason {
            StructuralRealSignReason::Known { real, source } => {
                if real.element.ir() != proof.element.ir() || real.set != StandardSet::R {
                    return Err(invalid("KnownReal"));
                }
                let AtomicFact::NotEqualFact(fact) = &source.fact else {
                    return Err(invalid("KnownSubject"));
                };
                let forward = fact.left.ir() == proof.element.ir() && is_zero(&fact.right);
                if !forward && !(is_zero(&fact.left) && fact.right.ir() == proof.element.ir()) {
                    return Err(invalid("KnownSubject"));
                }
                let real = self.compile_structural(real, position)?;
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
                    source.searched_proof.as_ref()
                else {
                    return Err(invalid("KnownCitation"));
                };
                let cited = self.compile_known_atomic(citation, &source.fact, position)?;
                let cited = if forward {
                    cited
                } else {
                    format!("(fun h => ({cited}) h.symm)")
                };
                Ok(format!(
                    "(by\n  have _sign_real := {real}\n  exact {cited}\n)"
                ))
            }
            StructuralRealSignReason::Mul { left, right }
            | StructuralRealSignReason::Div { left, right } => {
                let (a, b, rule) = match (&proof.element, &proof.reason) {
                    (
                        Obj::ArithmeticOperator(ArithmeticOperator::Mul(v)),
                        StructuralRealSignReason::Mul { .. },
                    ) => (&v.left, &v.right, "mulNonzero"),
                    (
                        Obj::ArithmeticOperator(ArithmeticOperator::Div(v)),
                        StructuralRealSignReason::Div { .. },
                    ) => (&v.left, &v.right, "divNonzero"),
                    _ => return Err(invalid("BinaryConstructor")),
                };
                if a.ir() != left.element.ir() || b.ir() != right.element.ir() {
                    return Err(invalid("BinaryOperands"));
                }
                let lhs = self.compile_structural_nonzero(left, position)?;
                let rhs = self.compile_structural_nonzero(right, position)?;
                let right_membership = if rule == "divNonzero" {
                    "_sign_product.wd.2.1"
                } else {
                    "_sign_product.wd.2"
                };
                Ok(format!("(by\n  let _sign_product := {object}\n  exact Litex.{rule} _sign_product.val.left _sign_product.val.right _sign_product.wd.1 {right_membership} ({lhs}) ({rhs})\n)"))
            }
            _ => Err(invalid("NonzeroReason")),
        }
    }

    pub(super) fn compile_structural_signed_membership(
        &self,
        fact: &InFact,
        proof: &SignedNumericMembershipProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::StandardSet(set) = &fact.set else {
            return Err(invalid("MembershipCarrier"));
        };
        let (base, name, sign) = match set {
            StandardSet::RPos => (StandardSet::R, "RPos", RealSign::Positive),
            StandardSet::QPos => (StandardSet::Q, "QPos", RealSign::Positive),
            StandardSet::RStar => (StandardSet::R, "RStar", RealSign::Nonzero),
            StandardSet::QStar => (StandardSet::Q, "QStar", RealSign::Nonzero),
            _ => return Err(invalid("MembershipCarrier")),
        };
        if proof.base_membership.element.ir() != fact.element.ir()
            || proof.base_membership.set != base
            || proof.sign.element.ir() != fact.element.ir()
            || !proof.sign.sign.implies(sign)
        {
            return Err(invalid("MembershipSubject"));
        }
        let member = self.compile_structural(&proof.base_membership, position)?;
        let condition = match sign {
            RealSign::Positive => self.compile_structural_positive(&proof.sign, position)?,
            _ => self.compile_structural_nonzero(&proof.sign, position)?,
        };
        Ok(format!(
            "(Litex.in{name}_intro {} {member} {condition})",
            self.compile_object_reference(&fact.element, position)?
        ))
    }

    fn compile_sign_nonzero_citation(
        &self,
        element: &Obj,
        source: &AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::NotEqualFact(fact) = &source.fact else {
            return Err(invalid("KnownSubject"));
        };
        let forward = fact.left.ir() == element.ir() && is_zero(&fact.right);
        if !forward && !(is_zero(&fact.left) && fact.right.ir() == element.ir()) {
            return Err(invalid("KnownSubject"));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
            source.searched_proof.as_ref()
        else {
            return Err(invalid("KnownCitation"));
        };
        let cited = self.compile_known_atomic(citation, &source.fact, position)?;
        Ok(if forward {
            cited
        } else {
            format!("(fun h => ({cited}) h.symm)")
        })
    }
}
