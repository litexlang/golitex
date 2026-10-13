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
        if !strict || !is_exact_zero(zero) || value.ir() != sub.left.ir() {
            return Err(LeanCompileError::new(
                "NaturalPredecessor/PositiveChild",
                "The original positive citation changes its minuend or strict zero bound.",
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

    pub(in crate::compile_to_lean) fn compile_integer_successor_lower_bound(
        &self,
        goal: &AtomicFact,
        cited: FactId,
        integer: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
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
