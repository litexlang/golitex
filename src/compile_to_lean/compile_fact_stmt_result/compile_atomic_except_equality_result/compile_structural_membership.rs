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
            StructuralMembershipReason::Min { left, right }
            | StructuralMembershipReason::Max { left, right } => {
                let maximum = matches!(&proof.reason, StructuralMembershipReason::Max { .. });
                let Some((a, b)) = crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::min_max_arguments(&proof.element, maximum) else {
                    return Err(LeanCompileError::unsupported("StructuralMembership/MinMaxConstructor"));
                };
                if a.ir() != left.element.ir()
                    || b.ir() != right.element.ir()
                    || left.set != proof.set
                    || right.set != proof.set
                {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/MinMaxSubject",
                    ));
                }
                Ok(format!(
                    "(Litex.minMaxMember {} {} {} {})",
                    self.compile_object_reference(&proof.element, position)?,
                    standard_term(&proof.set)?,
                    self.compile_structural(left, position)?,
                    self.compile_structural(right, position)?
                ))
            }
            StructuralMembershipReason::NaturalMaxDifference { .. } => Err(
                LeanCompileError::unsupported("StructuralMembership/OrderedSelection"),
            ),
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
                if numeric_refinement(&child.set).is_some()
                    || numeric_refinement(&proof.set).is_some()
                {
                    return standard_inclusion_term(
                        &child.set,
                        &proof.set,
                        &self.compile_object_reference(&proof.element, position)?,
                        &self.compile_structural(child, position)?,
                    );
                }
                if child.set == StandardSet::NPos {
                    let bridge = match proof.set {
                        StandardSet::N => None,
                        StandardSet::Z => Some("naturalToInteger"),
                        StandardSet::Q => Some("naturalToRational"),
                        StandardSet::R => Some("naturalToReal"),
                        StandardSet::C => Some("naturalToComplex"),
                        _ => {
                            return Err(LeanCompileError::unsupported(
                                "StructuralMembership/StandardSuperset",
                            ))
                        }
                    };
                    let member = self.compile_structural(child, position)?;
                    let object = self.compile_object_reference(&proof.element, position)?;
                    let natural = format!("(Litex.inNPos_natural {object} {member})");
                    return Ok(match bridge {
                        Some(bridge) => format!("(Litex.{bridge} {object} {natural})"),
                        None => natural,
                    });
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
                let real_to_complex =
                    matches!((&child.set, &proof.set), (StandardSet::R, StandardSet::C));
                let child = self.compile_structural(child, position)?;
                // Validate the original constructor/WD even when its denotation
                // can be inferred from the recorded membership proof.
                let object = self.compile_object_reference(&proof.element, position)?;
                if real_to_complex {
                    Ok(format!("(M.real_subset_complex _ {child})"))
                } else {
                    Ok(format!("(Litex.{bridge} {object} {child})"))
                }
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
                let base_proof = self.compile_structural(base, position)?;
                let exponent_proof = self.compile_structural(exponent, position)?;
                let (suffix, exponent_argument) = match proof.set {
                    StandardSet::N => ("N", " _recorded_power_exponent"),
                    StandardSet::Z => ("Z", " _recorded_power_exponent"),
                    StandardSet::C => ("C", " _recorded_power_exponent"),
                    StandardSet::R => ("R", ""),
                    StandardSet::Q => ("Q", ""),
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "StructuralMembership/PowCarrier",
                        ))
                    }
                };
                let term = self.compile_object_reference(&proof.element, position)?;
                // Finish each original proof independently before comparing its
                // type with the owned endpoint. Nested tactic-built objects can
                // otherwise still contain delayed elaboration metavariables.
                // R/Q still replay the integer child although their law only
                // needs the base child and the parent's certified power domain.
                Ok(format!(
                    "(by\n  let _litex_power := {term}\n  have _elaborated_power_base := {base_proof}\n  have _elaborated_power_exponent := {exponent_proof}\n  have _recorded_power_base : Litex.In _litex_power.val.base {} := _elaborated_power_base\n  have _recorded_power_exponent : Litex.In _litex_power.val.exponent {} := _elaborated_power_exponent\n  exact Litex.powStructuralIn{suffix} _litex_power _recorded_power_base{exponent_argument}\n)",
                    standard_term(&proof.set)?,
                    standard_term(&expected_exponent)?,
                ))
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::Min | IntrinsicCodomain::Max),
            ) => {
                let maximum = matches!(kind, IntrinsicCodomain::Max);
                if proof.set != StandardSet::R || crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::min_max_arguments(&proof.element, maximum).is_none() {
                    return Err(LeanCompileError::unsupported("StructuralMembership/IntrinsicMinMax"));
                }
                let term = self.compile_object_reference(&proof.element, position)?;
                Ok(format!("(by\n  let _extremum := {term}\n  exact Litex.minMaxMember _extremum Litex.R _extremum.wd.1 _extremum.wd.2\n)"))
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::EuclideanNorm | IntrinsicCodomain::MatrixFrobeniusNorm),
            ) => {
                let euclidean = matches!(kind, IntrinsicCodomain::EuclideanNorm);
                let (name, valid) = if euclidean {
                    (
                        "euclideanNormInR",
                        matches!(
                            &proof.element,
                            Obj::MatrixOperator(MatrixOperator::EuclideanNorm(_))
                        ),
                    )
                } else {
                    (
                        "frobeniusNormInR",
                        matches!(
                            &proof.element,
                            Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(_))
                        ),
                    )
                };
                if proof.set != StandardSet::R || !valid {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/NormSubject",
                    ));
                }
                Ok(format!(
                    "(Litex.{name} {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(IntrinsicCodomain::FiniteInnerProduct) => {
                if proof.set != StandardSet::C
                    || !matches!(
                        &proof.element,
                        Obj::MatrixOperator(MatrixOperator::InnerProduct(_))
                    )
                {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/InnerProductSubject",
                    ));
                }
                Ok(format!(
                    "(Litex.finiteInnerProductInC {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(IntrinsicCodomain::MatrixCofactor) => {
                if proof.set != StandardSet::C
                    || !matches!(
                        &proof.element,
                        Obj::MatrixOperator(MatrixOperator::Cofactor(_))
                    )
                {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/CofactorSubject",
                    ));
                }
                Ok(format!(
                    "(Litex.matrixCofactorInC {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::Supremum | IntrinsicCodomain::Infimum),
            ) => {
                let name = match (kind, &proof.element) {
                    (
                        IntrinsicCodomain::Supremum,
                        Obj::BoundOperator(BoundOperator::Supremum(_)),
                    ) => "supremum",
                    (IntrinsicCodomain::Infimum, Obj::BoundOperator(BoundOperator::Infimum(_))) => {
                        "infimum"
                    }
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "RealExtremum/MembershipSubject",
                        ))
                    }
                };
                if proof.set != StandardSet::R {
                    return Err(LeanCompileError::unsupported(
                        "RealExtremum/MembershipCarrier",
                    ));
                }
                Ok(format!(
                    "(Litex.{name}InR {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(IntrinsicCodomain::MatrixRank) => {
                if proof.set != StandardSet::N
                    || !matches!(&proof.element, Obj::MatrixOperator(MatrixOperator::Rank(_)))
                {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/RankSubject",
                    ));
                }
                Ok(format!(
                    "(Litex.matrixRankInN {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(IntrinsicCodomain::MatrixDeterminant) => {
                if proof.set != StandardSet::C
                    || !matches!(
                        &proof.element,
                        Obj::MatrixOperator(MatrixOperator::Determinant(_))
                    )
                {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/DeterminantSubject",
                    ));
                }
                Ok(format!(
                    "(Litex.matrixDeterminantInC {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(IntrinsicCodomain::MatrixTrace) => {
                if proof.set != StandardSet::C
                    || !matches!(
                        &proof.element,
                        Obj::MatrixOperator(MatrixOperator::Trace(_))
                    )
                {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/TraceSubject",
                    ));
                }
                Ok(format!(
                    "(Litex.matrixTraceInC {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
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
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::FiniteSetMax | IntrinsicCodomain::FiniteSetMin),
            ) => {
                let valid = matches!(
                    (&proof.element, kind),
                    (
                        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(_)),
                        IntrinsicCodomain::FiniteSetMax
                    ) | (
                        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(_)),
                        IntrinsicCodomain::FiniteSetMin
                    )
                );
                if proof.set != StandardSet::R || !valid {
                    return Err(LeanCompileError::unsupported("FiniteExtremum/Codomain"));
                }
                Ok(format!(
                    "(Litex.finiteExtremumInR {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(IntrinsicCodomain::FiniteSetSize) => {
                if proof.set != StandardSet::N
                    || !matches!(
                        &proof.element,
                        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(_))
                    )
                {
                    return Err(LeanCompileError::unsupported("FiniteSetSize/Codomain"));
                }
                Ok(format!(
                    "(Litex.finiteSetSizeInN {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(IntrinsicCodomain::Factorial) => {
                if proof.set != StandardSet::NPos
                    || !matches!(
                        &proof.element,
                        Obj::IntegerOperator(IntegerOperator::Factorial(_))
                    )
                {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/Factorial",
                    ));
                }
                Ok(format!(
                    "(Litex.factorialInNPos {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::Gcd | IntrinsicCodomain::Lcm),
            ) => {
                use super::super::compile_obj_well_defined_result::compile_gcd_lcm::gcd_lcm_arguments;
                let least = matches!(kind, IntrinsicCodomain::Lcm);
                if proof.set
                    != if least {
                        StandardSet::N
                    } else {
                        StandardSet::NPos
                    }
                    || gcd_lcm_arguments(&proof.element, least).is_none()
                {
                    return Err(LeanCompileError::unsupported("StructuralMembership/GcdLcm"));
                }
                let term = self.compile_object_reference(&proof.element, position)?;
                let law = if least { "lcmInN" } else { "gcdInNPos" };
                Ok(format!("(Litex.{law} {term})"))
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::Mod | IntrinsicCodomain::Quot),
            ) => {
                use super::super::compile_obj_well_defined_result::compile_integer_division::integer_division_arguments;
                let quotient = matches!(kind, IntrinsicCodomain::Quot);
                if proof.set != StandardSet::Z
                    || integer_division_arguments(&proof.element, quotient).is_none()
                {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/IntegerDivision",
                    ));
                }
                let term = self.compile_object_reference(&proof.element, position)?;
                let name = if quotient { "quot" } else { "mod" };
                Ok(format!("(Litex.{name}InZ {term})"))
            }
            StructuralMembershipReason::Intrinsic(IntrinsicCodomain::Sign) => {
                if proof.set != StandardSet::Z
                    || !matches!(
                        &proof.element,
                        Obj::ArithmeticOperator(ArithmeticOperator::Sign(_))
                    )
                {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/IntrinsicSign",
                    ));
                }
                Ok(format!(
                    "(Litex.signInZ {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::Floor | IntrinsicCodomain::Ceil),
            ) => {
                let ceiling = matches!(kind, IntrinsicCodomain::Ceil);
                if proof.set != StandardSet::Z || crate::compile_to_lean::compile_fact_stmt_result::compile_obj_well_defined_result::compile_rounding::rounding_argument(&proof.element, ceiling).is_none() {
                    return Err(LeanCompileError::unsupported("StructuralMembership/IntrinsicRounding"));
                }
                Ok(format!(
                    "(Litex.roundingInZ {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::EulerNumber | IntrinsicCodomain::Pi),
            ) => {
                if !matches!(
                    (&proof.element, kind),
                    (
                        Obj::Literal(Literal::EulerNumber(_)),
                        IntrinsicCodomain::EulerNumber
                    ) | (Obj::Literal(Literal::Pi(_)), IntrinsicCodomain::Pi)
                ) {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/ConstantSubject",
                    ));
                }
                self.compile_real_constant_member(&proof.element, &proof.set, position)
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::Conjugate
                | IntrinsicCodomain::RealPart
                | IntrinsicCodomain::ImaginaryPart
                | IntrinsicCodomain::ComplexAbs),
            ) => {
                let (law, carrier) = match (kind, &proof.element) {
                    (
                        IntrinsicCodomain::Conjugate,
                        Obj::ComplexOperator(ComplexOperator::Conjugate(_)),
                    ) => ("conjInC", StandardSet::C),
                    (
                        IntrinsicCodomain::RealPart,
                        Obj::ComplexOperator(ComplexOperator::RealPart(_)),
                    ) => ("reInR", StandardSet::R),
                    (
                        IntrinsicCodomain::ImaginaryPart,
                        Obj::ComplexOperator(ComplexOperator::ImaginaryPart(_)),
                    ) => ("imgInR", StandardSet::R),
                    (
                        IntrinsicCodomain::ComplexAbs,
                        Obj::ComplexOperator(ComplexOperator::ComplexAbs(_)),
                    ) => ("complexAbsInR", StandardSet::R),
                    _ => return Err(LeanCompileError::unsupported("Complex/CodomainSubject")),
                };
                if proof.set != carrier {
                    return Err(LeanCompileError::unsupported("Complex/CodomainCarrier"));
                }
                Ok(format!(
                    "(Litex.{law} {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::Sinh
                | IntrinsicCodomain::Cosh
                | IntrinsicCodomain::Tanh
                | IntrinsicCodomain::Coth
                | IntrinsicCodomain::Sech
                | IntrinsicCodomain::Csch),
            ) => {
                let (law, carrier) = match (kind, &proof.element) {
                    (
                        IntrinsicCodomain::Sinh,
                        Obj::HyperbolicOperator(HyperbolicOperator::Sinh(_)),
                    ) => ("sinhInR", StandardSet::R),
                    (
                        IntrinsicCodomain::Cosh,
                        Obj::HyperbolicOperator(HyperbolicOperator::Cosh(_)),
                    ) => ("coshInRPos", StandardSet::RPos),
                    (
                        IntrinsicCodomain::Tanh,
                        Obj::HyperbolicOperator(HyperbolicOperator::Tanh(_)),
                    ) => ("tanhInR", StandardSet::R),
                    (
                        IntrinsicCodomain::Coth,
                        Obj::HyperbolicOperator(HyperbolicOperator::Coth(_)),
                    ) => ("cothInRStar", StandardSet::RStar),
                    (
                        IntrinsicCodomain::Sech,
                        Obj::HyperbolicOperator(HyperbolicOperator::Sech(_)),
                    ) => ("sechInRPos", StandardSet::RPos),
                    (
                        IntrinsicCodomain::Csch,
                        Obj::HyperbolicOperator(HyperbolicOperator::Csch(_)),
                    ) => ("cschInRStar", StandardSet::RStar),
                    _ => return Err(LeanCompileError::unsupported("Hyperbolic/CodomainSubject")),
                };
                if proof.set != carrier {
                    return Err(LeanCompileError::unsupported("Hyperbolic/CodomainCarrier"));
                }
                Ok(format!(
                    "(Litex.{law} {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::Sin
                | IntrinsicCodomain::Cos
                | IntrinsicCodomain::Tan
                | IntrinsicCodomain::Cot
                | IntrinsicCodomain::Sec
                | IntrinsicCodomain::Csc
                | IntrinsicCodomain::Arcsin
                | IntrinsicCodomain::Arccos
                | IntrinsicCodomain::Arctan
                | IntrinsicCodomain::Arccot),
            ) => {
                let law = match (kind, &proof.element) {
                    (IntrinsicCodomain::Sin, Obj::TrigOperator(TrigOperator::Sin(_))) => "sinInR",
                    (IntrinsicCodomain::Cos, Obj::TrigOperator(TrigOperator::Cos(_))) => "cosInR",
                    (IntrinsicCodomain::Tan, Obj::TrigOperator(TrigOperator::Tan(_))) => "tanInR",
                    (IntrinsicCodomain::Cot, Obj::TrigOperator(TrigOperator::Cot(_))) => "cotInR",
                    (IntrinsicCodomain::Sec, Obj::TrigOperator(TrigOperator::Sec(_))) => {
                        "secInRStar"
                    }
                    (IntrinsicCodomain::Csc, Obj::TrigOperator(TrigOperator::Csc(_))) => {
                        "cscInRStar"
                    }
                    (IntrinsicCodomain::Arcsin, Obj::TrigOperator(TrigOperator::Arcsin(_))) => {
                        "arcsinInR"
                    }
                    (IntrinsicCodomain::Arccos, Obj::TrigOperator(TrigOperator::Arccos(_))) => {
                        "arccosInR"
                    }
                    (IntrinsicCodomain::Arctan, Obj::TrigOperator(TrigOperator::Arctan(_))) => {
                        "arctanInR"
                    }
                    (IntrinsicCodomain::Arccot, Obj::TrigOperator(TrigOperator::Arccot(_))) => {
                        "arccotInR"
                    }
                    _ => return Err(LeanCompileError::unsupported("Trig/CodomainSubject")),
                };
                let carrier = if matches!(kind, IntrinsicCodomain::Sec | IntrinsicCodomain::Csc) {
                    StandardSet::RStar
                } else {
                    StandardSet::R
                };
                if proof.set != carrier {
                    return Err(LeanCompileError::unsupported("Trig/CodomainCarrier"));
                }
                Ok(format!(
                    "(Litex.{law} {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(
                kind @ (IntrinsicCodomain::Exp | IntrinsicCodomain::Ln | IntrinsicCodomain::Log),
            ) => {
                let (law, carrier) = match (kind, &proof.element) {
                    (IntrinsicCodomain::Exp, Obj::ExpLogOperator(ExpLogOperator::Exp(_))) => {
                        ("expInRPos", StandardSet::RPos)
                    }
                    (IntrinsicCodomain::Ln, Obj::ExpLogOperator(ExpLogOperator::Ln(_))) => {
                        ("lnInR", StandardSet::R)
                    }
                    (IntrinsicCodomain::Log, Obj::ExpLogOperator(ExpLogOperator::Log(_))) => {
                        ("logInR", StandardSet::R)
                    }
                    _ => {
                        return Err(LeanCompileError::unsupported(
                            "StructuralMembership/ExpLogSubject",
                        ))
                    }
                };
                if proof.set != carrier {
                    return Err(LeanCompileError::unsupported(
                        "StructuralMembership/ExpLogCarrier",
                    ));
                }
                Ok(format!(
                    "(Litex.{law} {})",
                    self.compile_object_reference(&proof.element, position)?
                ))
            }
            StructuralMembershipReason::Intrinsic(IntrinsicCodomain::Sqrt) => {
                if proof.set != StandardSet::R
                    || !matches!(&proof.element, Obj::ExpLogOperator(ExpLogOperator::Sqrt(_)))
                {
                    return Err(LeanCompileError::new("StructuralMembership/IntrinsicSqrtSubject", "The intrinsic square-root codomain requires its original Sqrt object and R target."));
                }
                let term = self.compile_object_reference(&proof.element, position)?;
                Ok(format!("(by\n  let _litex_sqrt := {term}\n  exact Litex.sqrtInR _litex_sqrt.val.arg _litex_sqrt.wd.1 _litex_sqrt.wd.2\n)"))
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
