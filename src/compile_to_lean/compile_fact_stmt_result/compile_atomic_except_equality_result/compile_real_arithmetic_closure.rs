use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::{InFactSearchProofByBuiltinRule, RealArithmeticConstructorTree};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::AtomicExceptEqualityFactSearchProofByKnownSpecialProperty;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_real_arithmetic_membership(
        &self,
        goal: &InFact,
        rule: &InFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if goal.set != Obj::StandardSet(StandardSet::R) {
            return Err(LeanCompileError::new(
                "RealArithmetic/Carrier",
                "The selected real closure must retain its original R target.",
            ));
        }
        match rule {
            InFactSearchProofByBuiltinRule::RealPower(proof) => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = &goal.element else {
                    return Err(LeanCompileError::new(
                        "RealArithmetic/PowerSubject",
                        "Real power evidence has another source constructor.",
                    ));
                };
                if membership_subject(&source_subject(&proof.base_in_real_proof)?, &power.base)?
                    != StandardSet::R
                {
                    return Err(LeanCompileError::new(
                        "RealArithmetic/PowerBase",
                        "The selected real-base child has another source subject or carrier.",
                    ));
                }
                Ok(format!(
                    "(Litex.powStructuralInR {} {})",
                    self.compile_object_reference(&goal.element, position)?,
                    self.compile_verify(&proof.base_in_real_proof, position)?.1
                ))
            }
            InFactSearchProofByBuiltinRule::RealOperandArithmeticClosure(proof) => {
                let (name, operands) = real_arithmetic_operands(&goal.element)?;
                if proof.operand_proofs.len() != operands.len() {
                    return Err(LeanCompileError::new(
                        "RealArithmetic/Children",
                        "Real closure needs each of its original ordered operand proofs.",
                    ));
                }
                let mut children = Vec::new();
                for (operand, child) in operands.into_iter().zip(&proof.operand_proofs) {
                    if membership_subject(&source_subject(child)?, operand)? != StandardSet::R {
                        return Err(LeanCompileError::new(
                            "RealArithmetic/ChildSubject",
                            "An original operand proof changes its source subject or real carrier.",
                        ));
                    }
                    children.push(self.compile_verify(child, position)?.1);
                }
                self.real_arithmetic_from_children(&goal.element, name, &children, position)
            }
            InFactSearchProofByBuiltinRule::RealArithmeticConstructorClosure(proof) => {
                self.compile_real_arithmetic_tree(&goal.element, &proof.constructor_tree, position)
            }
            _ => Err(LeanCompileError::unsupported("RealArithmetic/Rule")),
        }
    }

    fn compile_real_arithmetic_tree(
        &self,
        object: &Obj,
        tree: &RealArithmeticConstructorTree,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        use RealArithmeticConstructorTree as Tree;
        if let Tree::Leaf(proof) = tree {
            if proof.fact.element.ir() != object.ir()
                || proof.fact.set != Obj::StandardSet(StandardSet::R)
            {
                return Err(LeanCompileError::new(
                    "RealArithmetic/TerminalSubject",
                    "An original constructor-tree terminal changes its real source membership.",
                ));
            }
            return self.compile_real_arithmetic_terminal(
                &proof.fact,
                &proof.searched_proof,
                position,
            );
        }
        let (name, operands) = real_arithmetic_operands(object)?;
        let children: Vec<&Tree> = match (name, tree) {
            ("add", Tree::Add { left, right })
            | ("sub", Tree::Sub { left, right })
            | ("mul", Tree::Mul { left, right })
            | ("div", Tree::Div { left, right }) => vec![left, right],
            ("neg", Tree::Neg { argument }) => vec![argument],
            (
                "pow",
                Tree::IntegerPow {
                    base,
                    exponent_in_integer_proof,
                },
            ) => {
                let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = object else {
                    unreachable!()
                };
                if exponent_in_integer_proof.fact.element.ir() != power.exponent.ir()
                    || exponent_in_integer_proof.fact.set != Obj::StandardSet(StandardSet::Z)
                {
                    return Err(LeanCompileError::new("RealArithmetic/TreeExponent", "The original constructor-tree exponent certificate changes its exact integer source subject."));
                }
                let exponent = self.compile_real_arithmetic_terminal(
                    &exponent_in_integer_proof.fact,
                    &exponent_in_integer_proof.searched_proof,
                    position,
                )?;
                let base = self.compile_real_arithmetic_tree(&power.base, base, position)?;
                return Ok(format!("(by\n  have _litex_recorded_exp : Litex.In {} (Litex.Z (M := M)) := {exponent}\n  exact Litex.powStructuralInR {} {base}\n)", self.compile_object_reference(&power.exponent, position)?, self.compile_object_reference(object, position)?));
            }
            _ => {
                return Err(LeanCompileError::new(
                    "RealArithmetic/TreeConstructor",
                    "The original constructor-tree variant differs from its source operation.",
                ))
            }
        };
        let mut compiled = Vec::new();
        for (operand, child) in operands.into_iter().zip(children) {
            compiled.push(self.compile_real_arithmetic_tree(operand, child, position)?);
        }
        self.real_arithmetic_from_children(object, name, &compiled, position)
    }

    fn compile_real_arithmetic_terminal(
        &self,
        fact: &InFact,
        proof: &AtomicExceptEqualityFactSearchedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => {
                self.compile_known_atomic(proof, &AtomicFact::InFact(fact.clone()), position)
            }
            AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) => {
                if proof.element.ir() != fact.element.ir()
                    || fact.set != Obj::StandardSet(proof.set.clone())
                {
                    return Err(LeanCompileError::new(
                        "RealArithmetic/TerminalCapture",
                        "The original terminal's structural evidence describes another membership.",
                    ));
                }
                self.compile_structural(proof, position)
            }
            AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
                ClosedAtomicExceptEqualityCalculationProof::In(proof),
            ) => self.compile_closed_membership(&fact.element, &fact.set, proof, position),
            AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
                AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(proof),
            ) => self.compile_fn_return_rule(fact, proof, position),
            _ => Err(LeanCompileError::unsupported(
                "RealArithmetic/TerminalRoute",
            )),
        }
    }

    fn real_arithmetic_from_children(
        &self,
        object: &Obj,
        name: &str,
        children: &[String],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let term = self.compile_object_reference(object, position)?;
        Ok(match name {
            "neg" => format!("(by\n  let _litex_real_result := {term}\n  exact Litex.negInR _litex_real_result.val.arg {}\n)", children[0]),
            "pow" => format!("(Litex.powStructuralInR {term} {})", children[0]),
            "div" => format!("(by\n  let _litex_real_result := {term}\n  exact Litex.divInR _litex_real_result.val.left _litex_real_result.val.right {} {} _litex_real_result.wd.2.2\n)", children[0], children[1]),
            _ => format!("(by\n  let _litex_real_result := {term}\n  exact Litex.{name}InR _litex_real_result.val.left _litex_real_result.val.right {} {}\n)", children[0], children[1]),
        })
    }
}

fn real_arithmetic_operands(object: &Obj) -> Result<(&'static str, Vec<&Obj>), LeanCompileError> {
    match object {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(value)) => {
            Ok(("add", vec![&value.left, &value.right]))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(value)) => {
            Ok(("sub", vec![&value.left, &value.right]))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(value)) => {
            Ok(("mul", vec![&value.left, &value.right]))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Div(value)) => {
            Ok(("div", vec![&value.left, &value.right]))
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(value)) => Ok(("neg", vec![&value.arg])),
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(value)) => Ok(("pow", vec![&value.base])),
        _ => Err(LeanCompileError::unsupported("RealArithmetic/Constructor")),
    }
}
