use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::SumBothPositiveBuiltinRuleProof;
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
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::ProductPositiveBothPos(proof) => {
                (
                    BinaryArithmetic::Mul,
                    &proof.requirement_facts,
                    &proof.proof_of_requirement_facts,
                )
            }
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
            (BinaryArithmetic::Mul, Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul))) => {
                (mul.left.as_ref(), mul.right.as_ref())
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
            BinaryArithmetic::Mul => format!(
                "Litex.mulPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 {} {}",
                proofs[0], proofs[1]
            ),
            BinaryArithmetic::Sub => unreachable!(),
        };
        Ok(format!(
            "(by\n  let _litex_positive_result := {term}\n  exact {adapter}\n)"
        ))
    }

    pub(in crate::compile_to_lean) fn compile_positive_sum_builtin(
        &self,
        goal: &AtomicFact,
        proof: &SumBothPositiveBuiltinRuleProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::LessFact(goal) = goal else {
            return Err(LeanCompileError::unsupported("PositiveSum/GoalFamily"));
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = &goal.right else {
            return Err(LeanCompileError::new(
                "PositiveSum/Constructor",
                "The selected strict sum builtin must conclude positivity of its source sum.",
            ));
        };
        if !is_exact_zero(&goal.left) {
            return Err(LeanCompileError::new(
                "PositiveSum/Goal",
                "The selected positive sum builtin has a different lower endpoint.",
            ));
        }
        let children = [&proof.left_positive_proof, &proof.right_positive_proof];
        let mut ids = std::collections::HashSet::new();
        let mut compiled = Vec::new();
        for (child, operand) in children
            .into_iter()
            .zip([sum.left.as_ref(), sum.right.as_ref()])
        {
            let subject = source_subject(child)?;
            let Fact::AtomicFact(atomic) = &subject else {
                return Err(LeanCompileError::new(
                    "PositiveSum/ChildFamily",
                    "The actual child must be an atomic strict positivity result.",
                ));
            };
            let (zero, positive, strict) = source_order_oriented(atomic)?;
            if !strict
                || !is_exact_zero(zero)
                || positive.ir() != operand.ir()
                || !ids.insert(subject.fact_id())
            {
                return Err(LeanCompileError::new("PositiveSum/ChildSubject", "The two actual ordered child identities must prove their distinct source positivity obligations."));
            }
            compiled.push(self.compile_verify(child, position)?.1);
        }
        let term = self.compile_object_reference(&goal.right, position)?;
        Ok(format!("(by\n  let _litex_positive_result := {term}\n  exact Litex.addPositive _litex_positive_result.val.left _litex_positive_result.val.right _litex_positive_result.wd.1 _litex_positive_result.wd.2 {} {}\n)", compiled[0], compiled[1]))
    }
}
