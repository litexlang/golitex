use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_natural_predecessor(
        &self,
        goal: &InFact,
        natural: &AtomicExceptEqualityFactKnownProof,
        positive: &AtomicExceptEqualityFactKnownProof,
        strict_zero: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = &goal.element else {
            return Err(LeanCompileError::new(
                "NaturalPredecessor/Constructor",
                "The actual predecessor membership must retain its original subtraction.",
            ));
        };
        if goal.set != Obj::StandardSet(StandardSet::N)
            || closed_integer(&sub.right) != Some(1)
            || !matches!(sub.right.as_ref(), Obj::Literal(Literal::Number(_)))
        {
            return Err(LeanCompileError::new("NaturalPredecessor/Subject", "The selected predecessor rule only concludes membership of the exact natural predecessor."));
        }
        if membership_subject(&Fact::AtomicFact(natural.fact.clone()), &sub.left)? != StandardSet::N
        {
            return Err(LeanCompileError::new(
                "NaturalPredecessor/NaturalChild",
                "The original natural-membership citation belongs to another minuend or carrier.",
            ));
        }
        let (zero, value, strict) = source_order_oriented(&positive.fact)?;
        let expected_bound = if strict_zero {
            is_exact_zero(zero)
        } else {
            matches!(zero, Obj::Literal(Literal::Number(_))) && closed_integer(zero) == Some(1)
        };
        if strict != strict_zero || !expected_bound || value.ir() != sub.left.ir() {
            return Err(LeanCompileError::new(
                "NaturalPredecessor/PositiveChild",
                "The original order citation changes its minuend or the selected zero/one bound.",
            ));
        }
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
            natural.searched_proof.as_ref()
        else {
            return Err(LeanCompileError::unsupported(
                "NaturalPredecessor/KnownMembershipRoute",
            ));
        };
        let hn = self.compile_known_atomic(citation, &natural.fact, position)?;
        let hpos = self.compile_order_known_premise(positive, position)?.1;
        let hone = self.compile_literal_one_identity(&sub.right, position)?;
        let hpos = if strict_zero {
            hpos
        } else {
            let bound = self.compile_object_reference(zero, position)?;
            let value = self.compile_object_reference(value, position)?;
            let bound_one = self.compile_literal_one_identity(zero, position)?;
            format!("(Litex.ltLeTrans (Litex.number (M := M) 0) {bound} {value} (Litex.NativeBridge.ltOfDenoteReal (Litex.number (M := M) 0) {bound} 0 1 rfl {bound_one} (by norm_num)) {hpos})")
        };
        Ok(format!(
            "(Litex.predecessorInN {} {hn} {hpos} {hone})",
            self.compile_object_reference(&goal.element, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_subtract_one_less(
        &self,
        goal: &AtomicFact,
        minuend: &Obj,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = low else {
            return Err(LeanCompileError::new(
                "SubtractOneLess/Constructor",
                "The selected rule has another lower source constructor.",
            ));
        };
        if !strict || sub.left.ir() != high.ir() || minuend.ir() != high.ir() {
            return Err(LeanCompileError::new(
                "SubtractOneLess/Subject",
                "The selected minuend does not match both original endpoints.",
            ));
        }
        let hone = self.compile_literal_one_identity(&sub.right, position)?;
        Ok(format!(
            "(Litex.subtractOneLess {} {} {hone})",
            self.compile_object_reference(low, position)?,
            self.compile_real_membership_certificate(high, position)?
        ))
    }

    pub(super) fn compile_subtract_positive_closed_less(
        &self,
        goal: &AtomicFact,
        minuend: &Obj,
        subtrahend: &Obj,
        normalized: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let invalid = || LeanCompileError::unsupported("SubtractPositiveClosedLess/Certificate");
        let (low, high, strict) = source_order_oriented(goal)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = low else {
            return Err(invalid());
        };
        if !strict
            || sub.left.ir() != high.ir()
            || minuend.ir() != high.ir()
            || sub.right.ir() != subtrahend.ir()
        {
            return Err(invalid());
        }
        let zero = EvalRational::new(0, 1).unwrap().to_obj();
        let Some((crate::rational_expression::NumberCompareResult::Greater, actual, _)) =
            crate::rational_expression::compare_closed_numeric_objs(subtrahend, &zero)
        else {
            return Err(invalid());
        };
        if actual != normalized {
            return Err(invalid());
        }
        let value = EvalRational::from_obj(subtrahend).ok_or_else(invalid)?;
        let value = exact_rational_literal(&value, "ℝ")?;
        let difference = self.compile_object_reference(low, position)?;
        let real = self.compile_real_membership_certificate(high, position)?;
        let observation = self.compile_numeric_observation(subtrahend, position)?.1;
        Ok(format!("(by\n  let _difference := {difference}\n  obtain ⟨_real, _real_eq⟩ := (M.real_members (Litex.denote _difference.val.left)).mp {real}\n  have _offset : Litex.denote _difference.val.right = M.number (({value} : ℝ) : ℂ) := ({observation}).trans (congrArg M.number (by norm_num))\n  refine Litex.NativeBridge.ltOfDenoteReal _difference _difference.val.left (_real - {value}) _real ?_ _real_eq (sub_lt_self _real (by norm_num))\n  change M.subValue (Litex.denote _difference.val.left) (Litex.denote _difference.val.right) = _\n  rw [_real_eq, _offset, M.sub_numbers, Complex.ofReal_sub])"))
    }

    pub(in crate::compile_to_lean) fn compile_integer_successor_lower_bound(
        &self,
        goal: &AtomicFact,
        cited: FactId,
        integer: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        if !strict
            && matches!(low, Obj::Literal(Literal::Number(_)))
            && closed_integer(low) != Some(1)
        {
            let Some(target_bound) = closed_integer(low) else {
                return Err(LeanCompileError::unsupported(
                    "IntegerSuccessorLowerBound/ClosedInteger",
                ));
            };
            let complete = position.atomic_search_prior(1)?;
            let source = self.resolve_fact(cited, &complete)?;
            let Fact::AtomicFact(source) = source else {
                return Err(LeanCompileError::unsupported(
                    "IntegerSuccessorLowerBound/CitedFamily",
                ));
            };
            let (bound, value, strict) = source_order_oriented(&source)?;
            let Some(previous) = closed_integer(bound) else {
                return Err(LeanCompileError::unsupported(
                    "IntegerSuccessorLowerBound/ClosedPredecessor",
                ));
            };
            if !strict
                || !matches!(bound, Obj::Literal(Literal::Number(_)))
                || previous.checked_add(1) != Some(target_bound)
                || value.ir() != high.ir()
                || membership_subject(&source_subject(integer)?, high)? != StandardSet::Z
            {
                return Err(LeanCompileError::unsupported(
                    "IntegerSuccessorLowerBound/ExactPredecessor",
                ));
            }
            let hpos = self.cited_fact_reference(cited, &complete)?.1;
            let hz = self
                .compile_verify(integer, &position.atomic_search_prior(0)?)?
                .1;
            let mut terms = Vec::new();
            let mut values = Vec::new();
            let mut equalities = Vec::new();
            for object in [bound, high, low, high] {
                terms.push(self.compile_object_reference(object, &complete)?);
                let observed = self.compile_numeric_observation(object, &complete)?;
                values.push(observed.0);
                equalities.push(observed.1);
            }
            let hbound=format!("(show Litex.In {} Litex.Z from (M.integer_members _).mpr ⟨({previous} : ℤ),({}).trans (congrArg M.number (by norm_num))⟩)",terms[0],equalities[0]);
            return Ok(format!(
                "(Litex.integerGapLe {} {hbound} {hz} {hpos} {} {} (Or.inl ⟨by norm_num, by rfl⟩))",
                terms.join(" "),
                values.join(" "),
                equalities.join(" ")
            ));
        }
        if strict
            || !matches!(low, Obj::Literal(Literal::Number(_)))
            || closed_integer(low) != Some(1)
        {
            return Err(LeanCompileError::unsupported(
                "IntegerSuccessorLowerBound/OtherClosedBound",
            ));
        }
        let source = self.resolve_fact(cited, position)?;
        let Fact::AtomicFact(atomic) = &source else {
            return Err(LeanCompileError::new(
                "IntegerSuccessorLowerBound/CitedFamily",
                "The selected source ID must name an atomic strict lower bound.",
            ));
        };
        let (zero, value, strict) = source_order_oriented(atomic)?;
        if !strict
            || !is_exact_zero(zero)
            || value.ir() != high.ir()
            || membership_subject(&source_subject(integer)?, high)? != StandardSet::Z
        {
            return Err(LeanCompileError::new("IntegerSuccessorLowerBound/CitedSubject", "The original strict bound and integer proof must retain the same exact upper object."));
        }
        let hpos = self.cited_fact_reference(cited, position)?.1;
        let hz = self.compile_verify(integer, position)?.1;
        let one = self.compile_literal_one_identity(low, position)?;
        // The source literal may have another faithful spelling. Transport its
        // original denotation instead of replacing the goal's endpoint.
        Ok(format!("(Litex.leOfSame (Litex.number (M := M) (1 : ℂ)) {} {} {} ({one}).symm (Litex.sameRefl {}) (Litex.integerSuccessorLowerBound {} {hz} {hpos}))", self.compile_object_reference(low, position)?, self.compile_object_reference(high, position)?, self.compile_object_reference(high, position)?, self.compile_object_reference(high, position)?, self.compile_object_reference(high, position)?))
    }

    pub(in crate::compile_to_lean) fn compile_sub_nonnegative_strategy(
        &self,
        goal: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (zero, expression, strict) = source_order_oriented(goal)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = expression else {
            return Err(LeanCompileError::new(
                "SubNonnegative/Constructor",
                "The selected strategy must retain its original difference.",
            ));
        };
        if strict || !is_exact_zero(zero) || requirements.len() != 1 || proofs.len() != 1 {
            return Err(LeanCompileError::new(
                "SubNonnegative/Requirements",
                "The selected difference needs its one original weak operand-order result.",
            ));
        }
        let Fact::AtomicFact(atomic) = &requirements[0] else {
            return Err(LeanCompileError::new(
                "SubNonnegative/RequirementFamily",
                "The operand-order requirement must be atomic.",
            ));
        };
        let (low, high, strict) = source_order_oriented(atomic)?;
        if strict
            || low.ir() != sub.right.ir()
            || high.ir() != sub.left.ir()
            || source_subject(&proofs[0])? != requirements[0]
        {
            return Err(LeanCompileError::new("SubNonnegative/RequirementSubject", "The ordered proof changes the exact original subtraction operands or comparison strength."));
        }
        Ok(format!(
            "(Litex.subNonnegative {} {})",
            self.compile_object_reference(expression, position)?,
            self.compile_verify(&proofs[0], position)?.1
        ))
    }
}
