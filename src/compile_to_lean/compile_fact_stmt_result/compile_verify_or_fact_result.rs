use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;
use crate::prelude::{
    OrFactSearchProofByBuiltinRule, OrFactSearchedProof, OrFactWellDefinedProof, VerifyOrFactResult,
};

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_verify_or_result(
        &self,
        result: &VerifyOrFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        let VerifyOrFactResult::Success(proof) = result else {
            return Err(LeanCompileError::unsupported("Or/Failed"));
        };
        self.compile_or_wd(&proof.fact, &proof.well_defined_proof, position)?;
        let formed = SourcePosition {
            before: proof.fact.facts.len(),
            ..*position
        };
        let position = &formed;
        let fact = Fact::OrFact(proof.fact.clone());
        let term = match &proof.searched_proof {
            OrFactSearchedProof::ByKnownOrFact(known) => {
                return self.compile_known_or_fact(&proof.fact, known, position)
            }
            OrFactSearchedProof::ByKnownForallFact(known) => {
                return self.compile_known_application(&fact, known, position)
            }
            OrFactSearchedProof::BySelectedBranch(selected)
                if selected.assumed_negated_branches.is_empty() =>
            {
                if selected.selected_index >= proof.fact.facts.len()
                    || source_subject(&selected.selected_branch)?
                        != crate::ast::fact::and_chain_as_fact(
                            &proof.fact.facts[selected.selected_index],
                        )
                {
                    return Err(LeanCompileError::new(
                        "Or/SelectedSubject",
                        "The selected original branch differs from its proof or index.",
                    ));
                }
                let mut term = self.compile_verify(&selected.selected_branch, position)?.1;
                if selected.selected_index + 1 != proof.fact.facts.len() {
                    term = format!("(Or.inl {term})");
                }
                for _ in 0..selected.selected_index {
                    term = format!("(Or.inr {term})");
                }
                term
            }
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::SquareSumComponentNonzero(selected),
            ) => self.compile_or_square_sum_nonzero(
                &proof.fact,
                &selected.left,
                &selected.right,
                &selected.square_sum_nonzero,
                position,
            )?,
            OrFactSearchedProof::ByBuiltinRule(
                OrFactSearchProofByBuiltinRule::IntegerSuccessorTail(selected),
            ) => {
                let [AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(equal)), AndChainAtomicFact::AtomicFact(AtomicFact::GreaterFact(greater))] =
                    proof.fact.facts.as_slice()
                else {
                    return Err(LeanCompileError::unsupported("Or/IntegerTailShape"));
                };
                if equal.left.ir() != selected.subject.ir()
                    || equal.right.ir() != selected.base.ir()
                    || greater.left.ir() != selected.subject.ir()
                    || greater.right.ir() != selected.base.ir()
                {
                    return Err(LeanCompileError::new("Or/IntegerTailSubject", "The original equality and strict tail must use the recorded subject and base."));
                }
                let mut integer_memberships = Vec::new();
                for (child, operand) in [
                    (&selected.subject_in_z, &selected.subject),
                    (&selected.base_in_z, &selected.base),
                ] {
                    match source_subject(child)? {
                        Fact::AtomicFact(AtomicFact::InFact(member))
                            if member.element.ir() == operand.ir()
                                && member.set == Obj::StandardSet(StandardSet::Z) => {}
                        _ => {
                            return Err(LeanCompileError::new(
                                "Or/IntegerTailMembership",
                                "An integer child has another subject or carrier.",
                            ))
                        }
                    }
                    integer_memberships.push(self.compile_verify(child, position)?.1);
                }
                let Fact::AtomicFact(bound) = source_subject(&selected.subject_ge_base)? else {
                    return Err(LeanCompileError::unsupported("Or/IntegerTailBound"));
                };
                let (base, subject, strict) = source_order_oriented(&bound)?;
                if strict
                    || base.ir() != selected.base.ir()
                    || subject.ir() != selected.subject.ir()
                {
                    return Err(LeanCompileError::new(
                        "Or/IntegerTailBound",
                        "The weak-bound child has another subject, base or strictness.",
                    ));
                }
                let bound = self.compile_verify(&selected.subject_ge_base, position)?.1;
                let base = self.compile_object_reference(&selected.base, position)?;
                let subject = self.compile_object_reference(&selected.subject, position)?;
                format!(
                    "(Litex.integerSuccessorTail {subject} {base} {} {} {bound})",
                    integer_memberships[0], integer_memberships[1]
                )
            }
            _ => return Err(LeanCompileError::unsupported("Or/SelectedRule")),
        };
        Ok((self.fact_proposition(&fact, position)?, term))
    }

    fn compile_or_square_sum_nonzero(
        &self,
        fact: &OrFact,
        left: &Obj,
        right: &Obj,
        nonzero: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [AndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(first)), AndChainAtomicFact::AtomicFact(AtomicFact::NotEqualFact(second))] =
            fact.facts.as_slice()
        else {
            return Err(LeanCompileError::unsupported("Or/SquareSumSubject"));
        };
        let orientation = |fact: &NotEqualFact, operand: &Obj| {
            if &fact.left == operand && is_zero(&fact.right) {
                Ok(false)
            } else if is_zero(&fact.left) && &fact.right == operand {
                Ok(true)
            } else {
                Err(LeanCompileError::new(
                    "Or/SquareSumSubject",
                    "The ordered nonzero branches differ from the recorded components.",
                ))
            }
        };
        let left_reversed = orientation(first, left)?;
        let right_reversed = orientation(second, right)?;
        let Fact::AtomicFact(AtomicFact::NotEqualFact(premise)) = source_subject(nonzero)? else {
            return Err(LeanCompileError::unsupported("Or/SquareSumPremise"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = &premise.left else {
            return Err(LeanCompileError::unsupported("Or/SquareSumPremise"));
        };
        // The producer tries precisely two powers or two self-products, in
        // either component order. Do not accept other equivalent polynomials.
        let components = match (sum.left.as_ref(), sum.right.as_ref()) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Pow(b)),
            ) if matches!(a.exponent.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "2")
                && matches!(b.exponent.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "2") =>
            {
                Some((
                    a.base.as_ref(),
                    b.base.as_ref(),
                    "fun (x y : ℂ) => x ^ (2 : ℕ) + y ^ (2 : ℕ)",
                ))
            }
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)),
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(b)),
            ) if a.left == a.right && b.left == b.right => Some((
                a.left.as_ref(),
                b.left.as_ref(),
                "fun (x y : ℂ) => x * x + y * y",
            )),
            _ => None,
        };
        let Some((a, b, square_sum)) = components else {
            return Err(LeanCompileError::unsupported("Or/SquareSumPremise"));
        };
        if !is_zero(&premise.right) || !((a == left && b == right) || (a == right && b == left)) {
            return Err(LeanCompileError::new(
                "Or/SquareSumPremise",
                "The original nonzero child is not one of the recorded components' square sums.",
            ));
        }
        let checked = self.compile_verify(nonzero, position)?;
        let complete =
            SourcePosition::new(Some(position), SourceOwner::Verify(nonzero), usize::MAX);
        let left_object = self.compile_object_reference(left, &complete)?;
        let right_object = self.compile_object_reference(right, &complete)?;
        let sum_object = self.compile_object_reference(&premise.left, &complete)?;
        let left_native = self.compile_numeric_observation(left, &complete)?;
        let right_native = self.compile_numeric_observation(right, &complete)?;
        let sum_native = self.compile_numeric_observation(&premise.left, &complete)?;
        let zero = "(Litex.number (M := M) (0 : ℂ))";
        let zero_denote = "(Litex.NativeBridge.denoteNumber (M := M) (0 : ℂ))";
        let left_same = if left_reversed {
            format!("Litex.Same {zero} {left_object}")
        } else {
            format!("Litex.Same {left_object} {zero}")
        };
        let left_equal = if left_reversed {
            "_litex_left.symm"
        } else {
            "_litex_left"
        };
        let right_equal = if right_reversed {
            "_litex_right.symm"
        } else {
            "_litex_right"
        };
        let (first_equal, second_equal) = if a == left && b == right {
            ("_litex_x_zero", "_litex_y_zero")
        } else {
            ("_litex_y_zero", "_litex_x_zero")
        };
        Ok(format!(
            "(by\n  classical\n  have _litex_sum_nonzero : {} := {}\n  by_cases _litex_left : {left_same}\n  · apply Or.inr\n    intro _litex_right\n    have _litex_x_zero : {} = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber {left_object} {zero} {} (0 : ℂ) {} {zero_denote} ({left_equal})\n    have _litex_y_zero : {} = (0 : ℂ) := Litex.NativeBridge.nativeEqOfDenoteNumber {right_object} {zero} {} (0 : ℂ) {} {zero_denote} ({right_equal})\n    apply _litex_sum_nonzero\n    exact Litex.NativeBridge.sameOfDenoteNumber {sum_object} {zero} {} (0 : ℂ) {} {zero_denote} ((congrArg₂ ({square_sum}) {first_equal} {second_equal}).trans (by norm_num))\n  · exact Or.inl _litex_left\n)",
            checked.0, checked.1,
            left_native.0, left_native.0, left_native.1,
            right_native.0, right_native.0, right_native.1,
            sum_native.0, sum_native.1,
        ))
    }

    pub(in crate::compile_to_lean) fn compile_or_wd(
        &self,
        fact: &OrFact,
        proof: &OrFactWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<(), LeanCompileError> {
        if fact.facts.is_empty() || fact.facts.len() != proof.branches.len() {
            return Err(LeanCompileError::unsupported("Or/FormationArity"));
        }
        for (index, (branch, wd)) in fact.facts.iter().zip(&proof.branches).enumerate() {
            self.compile_fact_wd(
                wd,
                &crate::ast::fact::and_chain_as_fact(branch),
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?;
        }
        Ok(())
    }
}
