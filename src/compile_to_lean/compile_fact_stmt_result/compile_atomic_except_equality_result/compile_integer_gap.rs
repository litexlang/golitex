//! Discrete integer strengthening consumes two original carriers and strict order.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

fn invalid(stage: &str) -> LeanCompileError {
    LeanCompileError::unsupported(&format!("IntegerSuccessorGap/{stage}"))
}
impl LitexToLeanCompiler {
    pub(super) fn compile_integer_adjacency_le(
        &self,
        goal: &AtomicFact,
        left_integer: &VerifyFactResult,
        right_integer: &VerifyFactResult,
        strict_proof: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::LessEqualFact(target) = goal else {
            return Err(invalid("AdjacencyTargetFamily"));
        };
        let Fact::AtomicFact(source) = source_subject(strict_proof)? else {
            return Err(invalid("AdjacencyStrictFamily"));
        };
        let (a, upper, strict) = source_order_oriented(&source)?;
        if !strict
            || a.ir() != target.left.ir()
            || !matches!(upper,Obj::ArithmeticOperator(ArithmeticOperator::Add(s)) if s.left.ir()==target.right.ir()&&matches!(s.right.as_ref(),Obj::Literal(Literal::Number(n)) if n.normalized_value=="1"))
        {
            return Err(invalid("AdjacencyEndpoints"));
        }
        let mut proofs = Vec::new();
        for (index, (value, checked)) in
            [(&target.left, left_integer), (&target.right, right_integer)]
                .into_iter()
                .enumerate()
        {
            if !matches!(source_subject(checked)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==value.ir()&&f.set==Obj::StandardSet(StandardSet::Z))
            {
                return Err(invalid("AdjacencyIntegerMember"));
            }
            proofs.push(
                self.compile_verify(checked, &position.atomic_search_prior(index)?)?
                    .1,
            );
        }
        let order = self
            .compile_verify(strict_proof, &position.atomic_search_prior(2)?)?
            .1;
        let a = self.compile_object_reference(&target.left, position)?;
        let b = self.compile_object_reference(&target.right, position)?;
        Ok(format!(
            "(Litex.integerAdjacencyLeValue (Litex.denote {a}) (Litex.denote {b}) {} {} {order})",
            proofs[0], proofs[1]
        ))
    }

    pub(super) fn compile_integer_successor_le(
        &self,
        goal: &AtomicFact,
        left_integer: &VerifyFactResult,
        right_integer: &VerifyFactResult,
        strict_proof: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::AtomicFact(source) = source_subject(strict_proof)? else {
            return Err(invalid("VerifiedStrictFamily"));
        };
        let (a, b, strict) = source_order_oriented(&source)?;
        let AtomicFact::LessEqualFact(target) = goal else {
            return Err(invalid("VerifiedTargetFamily"));
        };
        if !strict
            || target.right.ir() != b.ir()
            || !matches!(&target.left,Obj::ArithmeticOperator(ArithmeticOperator::Add(s)) if s.left.ir()==a.ir()&&matches!(s.right.as_ref(),Obj::Literal(Literal::Number(n)) if n.normalized_value=="1"))
        {
            return Err(invalid("VerifiedSuccessorEndpoints"));
        }
        let mut members = Vec::new();
        for (index, (value, checked)) in [(a, left_integer), (b, right_integer)]
            .into_iter()
            .enumerate()
        {
            if !matches!(source_subject(checked)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==value.ir()&&f.set==Obj::StandardSet(StandardSet::Z))
            {
                return Err(invalid("VerifiedIntegerMember"));
            }
            members.push(
                self.compile_verify(checked, &position.atomic_search_prior(index)?)?
                    .1,
            );
        }
        let order = self
            .compile_verify(strict_proof, &position.atomic_search_prior(2)?)?
            .1;
        let a = self.compile_object_reference(a, position)?;
        let b = self.compile_object_reference(b, position)?;
        Ok(format!("((Litex.integerSuccessorGapValue (Litex.denote {a}) (Litex.denote {b}) {} {} {order}).1)",members[0],members[1]))
    }
}
