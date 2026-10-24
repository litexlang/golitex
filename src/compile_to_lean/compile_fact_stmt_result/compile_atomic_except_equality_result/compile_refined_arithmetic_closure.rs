use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_refined_arithmetic_closure(
        &self,
        fact: &InFact,
        rule: &InFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use InFactSearchProofByBuiltinRule as Rule;
        let (set, quotient, left_proof, right_proof, law) = match rule {
            Rule::PositiveRealProduct(p) => (
                StandardSet::RPos,
                false,
                &p.left_positive,
                &p.right_positive,
                "mulInRPos",
            ),
            Rule::PositiveRealQuotient(p) => (
                StandardSet::RPos,
                true,
                &p.numerator_positive,
                &p.denominator_positive,
                "divInRPos",
            ),
            Rule::NonzeroRationalProduct(p) => (
                StandardSet::QStar,
                false,
                &p.left_nonzero_rational,
                &p.right_nonzero_rational,
                "mulInQStar",
            ),
            Rule::NonzeroRationalQuotient(p) => (
                StandardSet::QStar,
                true,
                &p.numerator_nonzero_rational,
                &p.denominator_nonzero_rational,
                "divInQStar",
            ),
            _ => return Err(LeanCompileError::unsupported("RefinedArithmetic/Rule")),
        };
        if fact.set != Obj::StandardSet(set.clone()) {
            return Err(LeanCompileError::unsupported("RefinedArithmetic/Carrier"));
        }
        let (left, right) = match &fact.element {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) if !quotient => (&p.left, &p.right),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) if quotient => (&p.left, &p.right),
            _ => return Err(LeanCompileError::unsupported("RefinedArithmetic/Operation")),
        };
        if membership_subject(&source_subject(left_proof)?, left)? != set
            || membership_subject(&source_subject(right_proof)?, right)? != set
        {
            return Err(LeanCompileError::unsupported(
                "RefinedArithmetic/OperandMembership",
            ));
        }
        let object = self.compile_object_reference(&fact.element, position)?;
        let left = self.compile_verify(left_proof, position)?.1;
        let right = self.compile_verify(right_proof, position)?.1;
        Ok(format!("(Litex.{law} {object} {left} {right})"))
    }
}
