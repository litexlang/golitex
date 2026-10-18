use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::IntrinsicCodomain;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_known_subset_member(
        &self,
        goal: &InFact,
        known: &crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::KnownSubsetMembershipProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (AtomicFact::InFact(member), AtomicFact::SubsetFact(subset)) =
            (&known.member_proof.fact, &known.subset_proof.fact)
        else {
            return Err(LeanCompileError::new(
                "StructuralMembership/SubsetFamily",
                "Subset membership requires member and subset premise subjects.",
            ));
        };
        if member.element.ir() != goal.element.ir()
            || member.set.ir() != subset.left.ir()
            || subset.right.ir() != goal.set.ir()
        {
            return Err(LeanCompileError::new(
                "StructuralMembership/SubsetSubject",
                "The cited premises do not connect this element to its target carrier.",
            ));
        }
        let (
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(member_cite),
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(subset_cite),
        ) = (
            known.member_proof.searched_proof.as_ref(),
            known.subset_proof.searched_proof.as_ref(),
        )
        else {
            return Err(LeanCompileError::unsupported(
                "StructuralMembership/SubsetCitation",
            ));
        };
        let member = self.compile_known_atomic(member_cite, &known.member_proof.fact, position)?;
        let subset = self.compile_known_atomic(subset_cite, &known.subset_proof.fact, position)?;
        Ok(format!(
            "({subset} (Litex.denote {}) {member})",
            self.compile_object_reference(&goal.element, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_structural(
        &self,
        proof: &StructuralMembershipProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let compiled = match &proof.reason {
            StructuralMembershipReason::Known(known) => {
                let mut fact = match self.resolve_fact(known.cite_fact_id, position)? {
                    Fact::AtomicFact(AtomicFact::InFact(fact)) => fact,
                    _ => {
                        return Err(LeanCompileError::new(
                            "StructuralMembership/Known",
                            "The structural citation is not a membership fact.",
                        ))
                    }
                };
                // Known membership may target an equal alias. Replay the exact
                // argument certificates against the structural node's subject.
                fact.element = proof.element.clone();
                fact.set = Obj::StandardSet(proof.set.clone());
                self.compile_known_atomic(known, &AtomicFact::InFact(fact), position)
            }
            StructuralMembershipReason::Closed(closed) => self.compile_closed_membership(
                &proof.element,
                &Obj::StandardSet(proof.set.clone()),
                closed,
                position,
            ),
            StructuralMembershipReason::StandardSuperset(child) => {
                if child.element.ir() != proof.element.ir() {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/SupersetSubject",
                        "Standard inclusion evidence changes its element.",
                    ));
                }
                let bridge = match (&child.set, &proof.set) {
                    (StandardSet::RPos, StandardSet::R) => "inRPos_real",
                    (StandardSet::RPos, StandardSet::C) => "positiveRealToComplex",
                    (StandardSet::R, StandardSet::C) => "realToComplex",
                    (StandardSet::Z, StandardSet::C) => "integerToComplex",
                    (StandardSet::N, StandardSet::C) => "naturalToComplex",
                    (StandardSet::N, StandardSet::Z) => "naturalToInteger",
                    (StandardSet::N, StandardSet::R) => "naturalToReal",
                    (StandardSet::Z, StandardSet::R) => "integerToReal",
                    (StandardSet::N, StandardSet::Q) => "naturalToRational",
                    (StandardSet::Z, StandardSet::Q) => "integerToRational",
                    (StandardSet::Q, StandardSet::R) => "rationalToReal",
                    (StandardSet::Q, StandardSet::C) => "rationalToComplex",
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "StructuralMembership/StandardSuperset",
                        ))
                    }
                };
                let child = self.compile_structural(child, position)?;
                Ok(format!(
                    "(Litex.{bridge} {} {child})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::KnownSubset(known) => {
                let goal = InFact {
                    fact_id: known.member_proof.fact.fact_id(),
                    element: proof.element.clone(),
                    set: Obj::StandardSet(proof.set.clone()),
                    line_file: None,
                };
                self.compile_known_subset_member(&goal, known, position)
            }
            StructuralMembershipReason::Add { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Add, position)
            }
            StructuralMembershipReason::Sub { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Sub, position)
            }
            StructuralMembershipReason::Mul { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Mul, position)
            }
            StructuralMembershipReason::Div { left, right } => {
                self.compile_structural_binary(proof, left, right, BinaryArithmetic::Div, position)
            }
            StructuralMembershipReason::ExactIntegerDiv { .. } => Err(
                LeanCompileError::unsupported("StructuralMembership/ExactIntegerDiv"),
            ),
            StructuralMembershipReason::Neg { argument } => {
                let operand = match &proof.element {
                    Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) => x.arg.as_ref(),
                    _ => {
                        return Err(LeanCompileError::new(
                            "StructuralMembership/NegSubject",
                            "Negation membership evidence has another constructor.",
                        ))
                    }
                };
                if operand.ir() != argument.element.ir() || proof.set != argument.set {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/NegChild",
                        "Negation membership changes its operand or carrier.",
                    ));
                }
                let child = self.compile_structural(argument, position)?;
                match proof.set {
                    StandardSet::C => Ok(format!(
                        "(Litex.negInC {} {child})",
                        self.compile_object_reference(operand, position)?
                    )),
                    StandardSet::R => Ok(format!(
                        "(Litex.negInR {} {child})",
                        self.compile_object_reference(operand, position)?
                    )),
                    StandardSet::Q => Ok(format!(
                        "(Litex.negInQ {} {child})",
                        self.compile_object_reference(operand, position)?
                    )),
                    StandardSet::Z => Ok(format!(
                        "(Litex.negInZ {} {child})",
                        self.compile_object_reference(operand, position)?
                    )),
                    _ => Err(LeanCompileError::unsupported(
                        "StructuralMembership/NegCarrier",
                    )),
                }
            }
            StructuralMembershipReason::Abs { argument } => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = &proof.element else {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/AbsSubject",
                        "The absolute-value certificate has another source constructor.",
                    ));
                };
                if abs.arg.ir() != argument.element.ir() || argument.set != proof.set {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/AbsChild",
                        "The recorded absolute-value child changes its exact argument or carrier.",
                    ));
                }
                let bridge = match proof.set {
                    StandardSet::R => "absInR",
                    StandardSet::C => "absInC",
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "StructuralMembership/AbsCarrier",
                        ))
                    }
                };
                let child = self.compile_structural(argument, position)?;
                let term = self.compile_object_reference(&proof.element, position)?;
                Ok(format!("(by\n  let _litex_abs := {term}\n  have _recorded_abs_argument : Litex.In _litex_abs.val.arg {} := {child}\n  exact Litex.{bridge} _litex_abs.val.arg _litex_abs.wd\n)", standard_term(&proof.set)?))
            }
            StructuralMembershipReason::Pow { base, exponent } => {
                let power = match &proof.element {
                    Obj::ArithmeticOperator(ArithmeticOperator::Pow(x)) => x,
                    _ => {
                        return Err(LeanCompileError::new(
                            "StructuralMembership/PowSubject",
                            "Power membership evidence has another constructor.",
                        ))
                    }
                };
                let expected_exponent = if matches!(proof.set, StandardSet::N | StandardSet::Z) {
                    StandardSet::N
                } else {
                    StandardSet::Z
                };
                if power.base.ir() != base.element.ir()
                    || power.exponent.ir() != exponent.element.ir()
                    || base.set != proof.set
                    || exponent.set != expected_exponent
                {
                    return Err(LeanCompileError::new(
                        "StructuralMembership/PowChild",
                        "Power membership changes its operand or integer carrier.",
                    ));
                }
                let ha_c = self.compile_structural(base, position)?;
                let he_z = self.compile_structural(exponent, position)?;
                match proof.set {
                    StandardSet::N | StandardSet::Z => {
                        let suffix = if proof.set == StandardSet::N {
                            "N"
                        } else {
                            "Z"
                        };
                        Ok(format!(
                            "(Litex.powStructuralIn{suffix} {} {ha_c} {he_z})",
                            self.compile_object_reference(&proof.element, position)?
                        ))
                    }
                    StandardSet::C => Ok(format!(
                        "(Litex.powStructuralInC {} {ha_c} {he_z})",
                        self.compile_object_reference(&proof.element, position)?
                    )),
                    StandardSet::R | StandardSet::Q => {
                        let suffix = if proof.set == StandardSet::Q {
                            "Q"
                        } else {
                            "R"
                        };
                        // Replay the actual integer-child certificate even though the
                        // owned power WD already proves exponent identification.
                        Ok(format!("(by\n  have _recorded_exp : Litex.In {} (Litex.Z (M := M)) := {he_z}\n  exact Litex.powStructuralIn{suffix} {} {ha_c}\n)", self.compile_object_reference(&power.exponent, position)?, self.compile_object_reference(&proof.element, position)?))
                    }
                    _ => Err(LeanCompileError::unsupported(
                        "StructuralMembership/PowCarrier",
                    )),
                }
            }
            StructuralMembershipReason::Intrinsic(IntrinsicCodomain::Abs) => {
                if proof.set != StandardSet::R
                    || !matches!(
                        &proof.element,
                        Obj::ArithmeticOperator(ArithmeticOperator::Abs(_))
                    )
                {
                    return Err(LeanCompileError::new("StructuralMembership/IntrinsicAbsSubject", "The selected intrinsic absolute-value codomain must retain its exact owned Abs constructor and R target."));
                }
                let term = self.compile_object_reference(&proof.element, position)?;
                Ok(format!("(by\n  let _litex_abs := {term}\n  exact Litex.absInR _litex_abs.val.arg _litex_abs.wd\n)"))
            }
            StructuralMembershipReason::Intrinsic(_) => Err(LeanCompileError::unsupported(
                "StructuralMembership/Intrinsic",
            )),
        }?;
        Ok(compiled)
    }

    pub(in crate::compile_to_lean) fn compile_structural_binary(
        &self,
        root: &StructuralMembershipProof,
        left: &StructuralMembershipProof,
        right: &StructuralMembershipProof,
        operation: BinaryArithmetic,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (a, b, name) = match (&root.element, operation) {
            (Obj::ArithmeticOperator(ArithmeticOperator::Add(x)), BinaryArithmetic::Add) => {
                (x.left.as_ref(), x.right.as_ref(), "add")
            }
            (Obj::ArithmeticOperator(ArithmeticOperator::Sub(x)), BinaryArithmetic::Sub) => {
                (x.left.as_ref(), x.right.as_ref(), "sub")
            }
            (Obj::ArithmeticOperator(ArithmeticOperator::Mul(x)), BinaryArithmetic::Mul) => {
                (x.left.as_ref(), x.right.as_ref(), "mul")
            }
            (Obj::ArithmeticOperator(ArithmeticOperator::Div(x)), BinaryArithmetic::Div) => {
                (x.left.as_ref(), x.right.as_ref(), "div")
            }
            _ => {
                return Err(LeanCompileError::new(
                    "StructuralMembership/ArithmeticSubject",
                    "Arithmetic membership evidence has another constructor.",
                ))
            }
        };
        if left.element.ir() != a.ir()
            || right.element.ir() != b.ir()
            || left.set != root.set
            || right.set != root.set
        {
            return Err(LeanCompileError::new(
                "StructuralMembership/ArithmeticChild",
                "Arithmetic membership changes its exact children or carrier.",
            ));
        }
        let ha = self.compile_structural(left, position)?;
        let hb = self.compile_structural(right, position)?;
        match root.set {
            StandardSet::C => {
                let guard = if matches!(operation, BinaryArithmetic::Div) {
                    format!(
                        " ({}).wd.2.2",
                        self.compile_object_reference(&root.element, position)?
                    )
                } else {
                    String::new()
                };
                Ok(format!(
                    "(Litex.{name}InC {} {} {ha} {hb}{guard})",
                    self.compile_object_reference(a, position)?,
                    self.compile_object_reference(b, position)?
                ))
            }
            StandardSet::R | StandardSet::Q => {
                let suffix = if root.set == StandardSet::Q { "Q" } else { "R" };
                let guard = if matches!(operation, BinaryArithmetic::Div) {
                    format!(
                        " ({}).wd.2.2",
                        self.compile_object_reference(&root.element, position)?
                    )
                } else {
                    String::new()
                };
                Ok(format!(
                    "(Litex.{name}In{suffix} {} {} {ha} {hb}{guard})",
                    self.compile_object_reference(a, position)?,
                    self.compile_object_reference(b, position)?
                ))
            }
            StandardSet::N
                if matches!(operation, BinaryArithmetic::Add | BinaryArithmetic::Mul) =>
            {
                Ok(format!(
                    "(Litex.{name}InN {} {} {ha} {hb})",
                    self.compile_object_reference(a, position)?,
                    self.compile_object_reference(b, position)?
                ))
            }
            StandardSet::Z
                if matches!(
                    operation,
                    BinaryArithmetic::Add | BinaryArithmetic::Sub | BinaryArithmetic::Mul
                ) =>
            {
                Ok(format!(
                    "(Litex.{name}InZ {} {} {ha} {hb})",
                    self.compile_object_reference(a, position)?,
                    self.compile_object_reference(b, position)?
                ))
            }
            _ => Err(LeanCompileError::unsupported(
                "StructuralMembership/ArithmeticCarrier",
            )),
        }
    }
}
