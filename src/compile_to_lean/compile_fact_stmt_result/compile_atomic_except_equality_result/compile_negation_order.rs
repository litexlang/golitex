use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_negation_order(
        &self,
        goal: &AtomicFact,
        premise: &AtomicExceptEqualityFactKnownProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (left, right, strict) = source_order_oriented(goal)?;
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)),
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(b)),
        ) = (left, right)
        else {
            return Err(LeanCompileError::unsupported("NegationOrder/Operands"));
        };
        let (low, high, known_strict) = source_order_oriented(&premise.fact)?;
        if low.ir() != b.arg.ir() || high.ir() != a.arg.ir() || (strict && !known_strict) {
            return Err(LeanCompileError::unsupported(
                "NegationOrder/ReversedPremise",
            ));
        }
        let (_, mut term) = self.compile_order_known_premise(premise, position)?;
        if !strict && known_strict {
            term = format!(
                "(Litex.ltToLe {} {} {term})",
                self.compile_object_reference(low, position)?,
                self.compile_object_reference(high, position)?
            );
        }
        Ok(format!(
            "(Litex.negation{}Order {} {} {term})",
            if strict { "Strict" } else { "Weak" },
            self.compile_object_reference(left, position)?,
            self.compile_object_reference(right, position)?
        ))
    }
}
