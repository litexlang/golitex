use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::not_in_fact::NotInFactSearchProofByBuiltinRule;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_nonmembership_builtin(
        &self,
        fact: &NotInFact,
        rule: &NotInFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match rule {
            NotInFactSearchProofByBuiltinRule::NonMembershipOfSetMinusFromRight(p) => self
                .compile_set_minus_nonmembership(fact, &p.right_membership_proof, true, position),
            NotInFactSearchProofByBuiltinRule::NonMembershipOfSetMinusFromLeft(p) => self
                .compile_set_minus_nonmembership(
                    fact,
                    &p.left_non_membership_proof,
                    false,
                    position,
                ),
            NotInFactSearchProofByBuiltinRule::NonMembershipOfIntersectFromLeft(p) => self
                .compile_intersection_nonmembership(
                    fact,
                    &p.left_non_membership_proof,
                    true,
                    position,
                ),
            NotInFactSearchProofByBuiltinRule::NonMembershipOfIntersectFromRight(p) => self
                .compile_intersection_nonmembership(
                    fact,
                    &p.right_non_membership_proof,
                    false,
                    position,
                ),
            NotInFactSearchProofByBuiltinRule::NonMembershipOfUnion(p) => self
                .compile_union_nonmembership(
                    fact,
                    [&p.left_non_membership_proof, &p.right_non_membership_proof],
                    position,
                ),
            NotInFactSearchProofByBuiltinRule::ClosedNumericNonMembership(p) => {
                self.compile_closed_numeric_nonmembership(fact, &p.normal, position)
            }
            NotInFactSearchProofByBuiltinRule::ListSetExhaustiveDisequality(p) => {
                let Obj::SetFormer(SetFormer::ListSet(set)) = &fact.set else {
                    return Err(LeanCompileError::unsupported("NotIn/FiniteSetSubject"));
                };
                if set.list.len() != p.disequality_proofs.len() {
                    return Err(LeanCompileError::unsupported("NotIn/FiniteSetChildren"));
                }
                let mut children = Vec::new();
                for (element, proof) in set.list.iter().zip(&p.disequality_proofs) {
                    if !matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::NotEqualFact(f))
                        if f.left.ir() == fact.element.ir() && f.right.ir() == element.ir())
                    {
                        return Err(LeanCompileError::unsupported("NotIn/FiniteSetChildSubject"));
                    }
                    children.push(self.compile_verify(proof, position)?.1);
                }
                let object = self.compile_object_reference(&fact.element, position)?;
                let mut term = format!("(Litex.notInEmpty {object})");
                for (index, proof) in children.iter().enumerate().rev() {
                    let set = format!("_set{}", ".val.tail".repeat(index));
                    term = format!("(Litex.notInInsert {object} {set}.val.element {set}.val.tail {set}.wd {proof} {term})");
                }
                Ok(format!(
                    "(by\n  let _set := {}\n  exact {term})",
                    self.compile_object_reference(&fact.set, position)?
                ))
            }
            _ => Err(LeanCompileError::unsupported("NotIn/BuiltinRule")),
        }
    }

    pub(in crate::compile_to_lean) fn compile_closed_nonmembership(
        &self,
        fact: &NotInFact,
        proof: &ClosedMembershipCalculationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let ClosedMembershipCalculationProof::StandardSet { value, set } = proof else {
            return Err(LeanCompileError::unsupported("NotIn/ClosedRange"));
        };
        if fact.set != Obj::StandardSet(set.clone()) {
            return Err(LeanCompileError::unsupported("NotIn/ClosedSet"));
        }
        match value {
            ClosedScalarValue::Decimal(normal) => {
                self.compile_closed_numeric_nonmembership(fact, normal, position)
            }
            ClosedScalarValue::ExactComplex { real, imaginary } => {
                let Some((a, b)) =
                    crate::rational_expression::exact_complex::exact_complex_coordinates(
                        &fact.element,
                    )
                else {
                    return Err(LeanCompileError::unsupported("NotIn/ComplexExpression"));
                };
                if &a != real || &b != imaginary || crate::rational_expression::closed_scalar_membership::exact_complex_inhabits_standard_set(real, imaginary, set) {
                    return Err(LeanCompileError::unsupported("NotIn/ClosedCertificate"));
                }
                if imaginary.is_zero() {
                    return self.compile_real_numeric_nonmembership(
                        fact,
                        set,
                        &exact_rational_literal(real, "ℚ")?,
                        real.to_i128_if_integer().is_none(),
                        real.is_zero(),
                        position,
                    );
                }
                let native = self.compile_numeric_observation(&fact.element, position)?;
                let number = format!("(Litex.number (M := M) {})", native.0);
                let real_member =
                    standard_inclusion_term(set, &StandardSet::R, &number, "_member")?;
                let denial = format!("(fun _member => (Litex.numberNotInROfImaginary {} (by norm_num [Complex.ext_iff])) {real_member})", native.0);
                Ok(format!(
                    "(Litex.notInOfSame {} {number} {} {} {denial})",
                    self.compile_object_reference(&fact.element, position)?,
                    standard_term(set)?,
                    native.1
                ))
            }
        }
    }

    fn compile_closed_numeric_nonmembership(
        &self,
        fact: &NotInFact,
        normal: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::StandardSet(set) = &fact.set else {
            return Err(LeanCompileError::unsupported("NotIn/NumericSet"));
        };
        let actual = evaluate_obj_to_normalized_decimal_number(&fact.element)
            .ok_or_else(|| LeanCompileError::unsupported("NotIn/ClosedExpression"))?;
        if actual.normalized_value != normal
            || crate::rational_expression::closed_scalar_membership::normalized_decimal_inhabits_standard_set(normal, set)
        {
            return Err(LeanCompileError::unsupported("NotIn/ClosedCertificate"));
        }
        self.compile_real_numeric_nonmembership(
            fact,
            set,
            &format!("({normal} : ℚ)"),
            normal.contains('.'),
            normal == "0",
            position,
        )
    }

    fn compile_real_numeric_nonmembership(
        &self,
        fact: &NotInFact,
        set: &StandardSet,
        q: &str,
        nonintegral: bool,
        zero: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let value = format!("(({q} : ℚ) : ℂ)");
        let number = format!("(Litex.number (M := M) {value})");
        let integer_domain = matches!(
            set,
            StandardSet::N
                | StandardSet::NPos
                | StandardSet::Z
                | StandardSet::ZNeg
                | StandardSet::ZStar
        );
        let contradiction = if integer_domain && nonintegral {
            let integer = standard_inclusion_term(set, &StandardSet::Z, &number, "_member")?;
            format!("(Litex.numberNotInZOfDenominator (M := M) {q} (by norm_num)) {integer}")
        } else if *set == StandardSet::N {
            format!("(Litex.numberNotInNOfNegative (M := M) {q} (by norm_num)) _member")
        } else if matches!(
            set,
            StandardSet::NPos | StandardSet::QPos | StandardSet::RPos
        ) {
            let positive = standard_sign_term(set, "positive", &number, "_member")?;
            format!("(Litex.numberNotPositive (M := M) {q} (by norm_num)) {positive}")
        } else if matches!(
            set,
            StandardSet::ZNeg | StandardSet::QNeg | StandardSet::RNeg
        ) {
            let negative = standard_sign_term(set, "negative", &number, "_member")?;
            format!("(Litex.numberNotNegative (M := M) {q} (by norm_num)) {negative}")
        } else if matches!(
            set,
            StandardSet::ZStar | StandardSet::QStar | StandardSet::RStar | StandardSet::CStar
        ) && zero
        {
            let nonzero = standard_sign_term(set, "nonzero", &number, "_member")?;
            format!("{nonzero} (congrArg M.number (by norm_num : {value} = (0 : ℂ)))")
        } else {
            return Err(LeanCompileError::unsupported("NotIn/NumericCarrier"));
        };
        let native = self.compile_numeric_observation(&fact.element, position)?;
        let equality = format!(
            "(({}).trans (congrArg M.number (by norm_num : {} = {value})))",
            native.1, native.0
        );
        Ok(format!(
            "(Litex.notInOfSame {} {number} {} {equality} (fun _member => {contradiction}))",
            self.compile_object_reference(&fact.element, position)?,
            standard_term(set)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_membership_contradiction(
        &self,
        goal: &NotEqualFact,
        member: &VerifyFactResult,
        nonmember: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::InFact(positive)) = source_subject(member)? else {
            return Err(LeanCompileError::unsupported(
                "MembershipContradiction/PositiveChild",
            ));
        };
        let Fact::AtomicFact(AtomicFact::NotInFact(negative)) = source_subject(nonmember)? else {
            return Err(LeanCompileError::unsupported(
                "MembershipContradiction/NegativeChild",
            ));
        };
        if positive.set.ir() != negative.set.ir() {
            return Err(LeanCompileError::unsupported("MembershipContradiction/Set"));
        }
        let reversed = if positive.element.ir() == goal.left.ir()
            && negative.element.ir() == goal.right.ir()
        {
            false
        } else if positive.element.ir() == goal.right.ir()
            && negative.element.ir() == goal.left.ir()
        {
            true
        } else {
            return Err(LeanCompileError::unsupported(
                "MembershipContradiction/Endpoints",
            ));
        };
        let proof = format!(
            "(Litex.notSameOfMembership {} {} {} {} {})",
            self.compile_object_reference(&positive.element, position)?,
            self.compile_object_reference(&negative.element, position)?,
            self.compile_object_reference(&positive.set, position)?,
            self.compile_verify(member, position)?.1,
            self.compile_verify(nonmember, position)?.1
        );
        Ok(if reversed {
            format!("(fun _equal => {proof} _equal.symm)")
        } else {
            proof
        })
    }
}
