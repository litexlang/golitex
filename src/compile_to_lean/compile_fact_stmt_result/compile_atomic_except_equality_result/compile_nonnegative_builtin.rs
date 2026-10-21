use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::NonnegativeSumTree;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_add_nonnegative_bound(
        &self,
        goal: &AtomicFact,
        child: &VerifyFactResult,
        right_addend: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (low, high, strict) = source_order_oriented(goal)?;
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) = high else {
            return Err(LeanCompileError::unsupported("AddNonnegative/Constructor"));
        };
        let (base, addend, field, law) = if right_addend {
            (&add.left, &add.right, "left", "leSelfAddRight")
        } else {
            (&add.right, &add.left, "right", "leSelfAddLeft")
        };
        let Fact::AtomicFact(bound) = source_subject(child)? else {
            return Err(LeanCompileError::unsupported("AddNonnegative/Premise"));
        };
        let (zero, subject, child_strict) = source_order_oriented(&bound)?;
        if strict
            || child_strict
            || !is_exact_zero(zero)
            || low.ir() != base.ir()
            || subject.ir() != addend.ir()
        {
            return Err(LeanCompileError::unsupported("AddNonnegative/Subjects"));
        }
        let prior = position.atomic_search_prior(0)?;
        let proof = self.compile_verify(child, &prior)?.1;
        let complete = position.atomic_search_prior(1)?;
        let real = self.compile_real_membership_certificate(base, &complete)?;
        let term = self.compile_object_reference(high, &complete)?;
        Ok(format!("(by\n  let _sum := {term}\n  have _baseReal : Litex.In _sum.val.{field} Litex.R := {real}\n  exact Litex.{law} _sum _baseReal {proof}\n)"))
    }

    pub(in crate::compile_to_lean) fn compile_nonnegative_sum_tree(
        &self,
        goal: &AtomicFact,
        tree: &NonnegativeSumTree,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::GreaterEqualFact(goal) = goal else {
            return Err(LeanCompileError::new(
                "NonnegativeSum/Goal",
                "The original sum rule concludes greater-equal zero.",
            ));
        };
        if !is_exact_zero(&goal.right) {
            return Err(LeanCompileError::new(
                "NonnegativeSum/Zero",
                "The original lower bound must be zero.",
            ));
        }
        let formed = position.atomic_search_prior(0)?;
        let object = self.compile_object_reference(&goal.left, &formed)?;
        let proof =
            self.compile_nonnegative_sum_node(&goal.left, tree, "_litex_sum", position, &mut 0)?;
        Ok(format!(
            "(by\n  let _litex_sum := {object}\n  exact {proof}\n)"
        ))
    }

    fn compile_nonnegative_sum_node(
        &self,
        expression: &Obj,
        tree: &NonnegativeSumTree,
        object: &str,
        position: &SourcePosition<'_>,
        next: &mut usize,
    ) -> Result<String, LeanCompileError> {
        match (expression, tree) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(add)),
                NonnegativeSumTree::Add { left, right },
            ) => {
                let a = format!("{object}.val.left");
                let b = format!("{object}.val.right");
                let ha = self.compile_nonnegative_sum_node(&add.left, left, &a, position, next)?;
                let hb =
                    self.compile_nonnegative_sum_node(&add.right, right, &b, position, next)?;
                Ok(format!(
                    "(Litex.addNonnegative {a} {b} {object}.wd.1 {object}.wd.2 {ha} {hb})"
                ))
            }
            (Obj::ArithmeticOperator(ArithmeticOperator::Add(_)), NonnegativeSumTree::Leaf(_)) => {
                Err(LeanCompileError::new(
                    "NonnegativeSum/Shape",
                    "An addition must retain its two original child branches.",
                ))
            }
            (_, NonnegativeSumTree::Leaf(child)) => {
                if !matches!(source_subject(child)?, Fact::AtomicFact(AtomicFact::GreaterEqualFact(ref fact))
                    if fact.left.ir() == expression.ir() && is_exact_zero(&fact.right))
                {
                    return Err(LeanCompileError::new(
                        "NonnegativeSum/Leaf",
                        "The original leaf must prove this exact operand is greater-equal zero.",
                    ));
                }
                let prior = position.atomic_search_prior(*next)?;
                let proof = self.compile_verify(child, &prior)?.1;
                *next += 1;
                Ok(proof)
            }
            _ => Err(LeanCompileError::new(
                "NonnegativeSum/Shape",
                "The captured sum tree differs from the original addition structure.",
            )),
        }
    }

    pub(in crate::compile_to_lean) fn compile_nonnegative_builtin(
        &self,
        goal: &AtomicFact,
        rule: &LessEqualFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::LessEqualFact(goal) = goal else {
            return Err(LeanCompileError::new(
                "NonnegativeBuiltin/GoalFamily",
                "The selected builtin must retain its weak less-equal conclusion.",
            ));
        };
        if !is_exact_zero(&goal.left) {
            return Err(LeanCompileError::new(
                "NonnegativeBuiltin/ZeroBound",
                "The selected sum or product must retain its exact lower bound zero.",
            ));
        }
        let (law, operands, children) = match (&goal.right, rule) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)),
                LessEqualFactSearchProofByBuiltinRule::SumOfNonnegatives(proof),
            ) => (
                "addNonnegative",
                [sum.left.as_ref(), sum.right.as_ref()],
                [
                    &proof.left_nonnegative_proof,
                    &proof.right_nonnegative_proof,
                ],
            ),
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)),
                LessEqualFactSearchProofByBuiltinRule::ProductOfNonnegatives(proof),
            ) => (
                "mulNonnegative",
                [product.left.as_ref(), product.right.as_ref()],
                [
                    &proof.left_nonnegative_proof,
                    &proof.right_nonnegative_proof,
                ],
            ),
            _ => {
                return Err(LeanCompileError::new(
                    "NonnegativeBuiltin/Constructor",
                    "The selected builtin must retain its own sum or product constructor.",
                ))
            }
        };
        let mut proofs = Vec::new();
        for (index, (child, operand)) in children.into_iter().zip(operands).enumerate() {
            let subject = source_subject(child)?;
            let Fact::AtomicFact(atomic) = &subject else {
                return Err(LeanCompileError::new(
                    "NonnegativeBuiltin/ChildFamily",
                    "The original nonnegative premise must be an atomic order fact.",
                ));
            };
            let (zero, value, strict) = source_order_oriented(atomic)?;
            if !is_exact_zero(zero) || value.ir() != operand.ir() {
                return Err(LeanCompileError::new(
                    "NonnegativeBuiltin/ChildSubject",
                    "The ordered child must certify the same operand's lower bound zero.",
                ));
            }
            let prior = position.atomic_search_prior(index)?;
            let proof = self.compile_verify(child, &prior)?.1;
            let side = if index == 0 { "left" } else { "right" };
            // The producer may retain a strict positive premise unchanged.
            // Its actual proof is replayed before weakening its conclusion.
            proofs.push(if strict {
                format!("(Litex.ltToLe (Litex.number (M := M) 0) _litex_nonnegative.val.{side} {proof})")
            } else {
                proof
            });
        }
        let formed = position.atomic_search_prior(0)?;
        let term = self.compile_object_reference(&goal.right, &formed)?;
        Ok(format!(
            "(by\n  let _litex_nonnegative := {term}\n  exact Litex.{law} _litex_nonnegative.val.left _litex_nonnegative.val.right _litex_nonnegative.wd.1 _litex_nonnegative.wd.2 {} {}\n)",
            proofs[0], proofs[1],
        ))
    }
}
