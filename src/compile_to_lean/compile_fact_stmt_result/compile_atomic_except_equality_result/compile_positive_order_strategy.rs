use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_positive_order_strategy(
        &self,
        goal: &AtomicFact,
        strategy: &AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (operation, requirements, results) = match strategy {
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PosAddPosIsPos(proof) => (
                BinaryArithmetic::Add,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::QuotientPositiveSameSignPos(
                proof,
            ) => (
                BinaryArithmetic::Div,
                &proof.requirement_facts,
                &proof.proof_of_requirement_facts,
            ),
            _ => return Err(LeanCompileError::unsupported("PositiveOrder/Strategy")),
        };
        let (zero, expression, strict) = source_order_oriented(goal)?;
        if !strict || !is_exact_zero(zero) {
            return Err(LeanCompileError::new(
                "PositiveOrder/Goal",
                "The selected positive operation strategy must conclude strict positivity.",
            ));
        }
        let (left, right) = match (operation, expression) {
            (BinaryArithmetic::Add, Obj::ArithmeticOperator(ArithmeticOperator::Add(add))) => {
                (add.left.as_ref(), add.right.as_ref())
            }
            (BinaryArithmetic::Div, Obj::ArithmeticOperator(ArithmeticOperator::Div(div))) => {
                (div.left.as_ref(), div.right.as_ref())
            }
            _ => {
                return Err(LeanCompileError::new(
                    "PositiveOrder/Constructor",
                    "The source operation differs from the selected strategy variant.",
                ))
            }
        };
        if requirements.len() != 2 || results.len() != 2 {
            return Err(LeanCompileError::new(
                "PositiveOrder/Requirements",
                "The selected operation needs its two ordered positivity results.",
            ));
        }
        let mut proofs = Vec::new();
        for ((requirement, result), operand) in requirements.iter().zip(results).zip([left, right])
        {
            let Fact::AtomicFact(requirement_atomic) = requirement else {
                return Err(LeanCompileError::new(
                    "PositiveOrder/RequirementFamily",
                    "An operand positivity requirement must be atomic.",
                ));
            };
            let (zero, positive, strict) = source_order_oriented(requirement_atomic)?;
            if !strict || !is_exact_zero(zero) || positive.ir() != operand.ir() {
                return Err(LeanCompileError::new("PositiveOrder/RequirementSubject", "An ordered positivity premise belongs to another operand or uses a weak comparison."));
            }
            if &source_subject(result)? != requirement {
                return Err(LeanCompileError::new(
                    "PositiveOrder/RequirementCapture",
                    "The actual proof differs from its recorded ordered requirement.",
                ));
            }
            proofs.push(self.compile_verify(result, position)?.1);
        }
        // The original goal constructor was already replayed by atomic WD.
        // Its proof fields own the exact C-domain and divisor certificates;
        // no positivity result is used to select a replacement construction.
        let term = self.compile_object_reference(expression, position)?;
        let adapter = match operation {
            BinaryArithmetic::Add => format!(
                "Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 {} {}",
                proofs[0], proofs[1]
            ),
            BinaryArithmetic::Div => format!(
                "Litex.divPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2.1 _litex_positive_result.wd.2.2 {} {}",
                proofs[0], proofs[1]
            ),
            BinaryArithmetic::Sub | BinaryArithmetic::Mul => unreachable!(),
        };
        Ok(format!(
            "(by\n  let _litex_positive_result := {term}\n  exact {adapter}\n)"
        ))
    }
}
