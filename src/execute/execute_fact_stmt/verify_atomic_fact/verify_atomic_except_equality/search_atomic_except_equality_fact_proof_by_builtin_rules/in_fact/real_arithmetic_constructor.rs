use crate::ast::fact::{AtomicFact, InFact};
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{ArithmeticOperator, Obj, StandardSet};
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// The enclosing atomic fact has already checked every object's WD, including
// nonzero divisors and the domain of negative powers. This success-only tree
// records the additional real-carrier evidence, rather than treating C WD as R.
pub struct RealArithmeticConstructorClosureBuiltinRuleProof {
    pub constructor_tree: RealArithmeticConstructorTree,
}

// Carrier truth only; the enclosing expression's WD owns the terminal's domain.
pub struct RealArithmeticConstructorTerminalProof {
    pub fact: InFact,
    pub searched_proof: Box<AtomicExceptEqualityFactSearchedProof>,
}

pub enum RealArithmeticConstructorTree {
    Leaf(RealArithmeticConstructorTerminalProof),
    Add {
        left: Box<Self>,
        right: Box<Self>,
    },
    Sub {
        left: Box<Self>,
        right: Box<Self>,
    },
    Neg {
        argument: Box<Self>,
    },
    Mul {
        left: Box<Self>,
        right: Box<Self>,
    },
    Div {
        left: Box<Self>,
        right: Box<Self>,
    },
    IntegerPow {
        base: Box<Self>,
        exponent_in_integer_proof: RealArithmeticConstructorTerminalProof,
    },
}

impl Runtime {
    pub(super) fn real_arithmetic_constructor_closure_proof(
        &mut self,
        fact: &InFact,
        premise_state: VerifyState,
    ) -> RuntimeResult<Option<RealArithmeticConstructorClosureBuiltinRuleProof>> {
        if !matches!(fact.set, Obj::StandardSet(StandardSet::R))
            || !matches!(
                fact.element,
                Obj::ArithmeticOperator(
                    ArithmeticOperator::Add(_)
                        | ArithmeticOperator::Sub(_)
                        | ArithmeticOperator::Neg(_)
                        | ArithmeticOperator::Mul(_)
                        | ArithmeticOperator::Div(_)
                        | ArithmeticOperator::Pow(_)
                )
            )
        {
            return Ok(None);
        }
        Ok(self
            .real_arithmetic_constructor_tree_from_children(
                &fact.element,
                &fact.line_file,
                premise_state,
            )?
            .map(
                |constructor_tree| RealArithmeticConstructorClosureBuiltinRuleProof {
                    constructor_tree,
                },
            ))
    }

    // Descent removes one syntax constructor. It does not enter another search
    // stage or raise permissions. All terminals receive the same already
    // restricted builtin premise state (at most KnownSpecialProperty).
    fn real_arithmetic_constructor_tree(
        &mut self,
        expression: &Obj,
        line_file: &Option<SourceLine>,
        premise_state: VerifyState,
    ) -> RuntimeResult<Option<RealArithmeticConstructorTree>> {
        if let Some(tree) = self.real_arithmetic_constructor_tree_from_children(
            expression,
            line_file,
            premise_state,
        )? {
            return Ok(Some(tree));
        }
        // An opaque or already checked composite is also a legal real leaf.
        // For example, i^2 is real by closed calculation although i is not.
        Ok(self
            .real_constructor_terminal_proof(expression, StandardSet::R, line_file, premise_state)?
            .map(RealArithmeticConstructorTree::Leaf))
    }

    fn real_arithmetic_constructor_tree_from_children(
        &mut self,
        expression: &Obj,
        line_file: &Option<SourceLine>,
        premise_state: VerifyState,
    ) -> RuntimeResult<Option<RealArithmeticConstructorTree>> {
        use RealArithmeticConstructorTree as Tree;
        let binary = match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(value)) => {
                Some((&value.left, &value.right))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(value)) => {
                Some((&value.left, &value.right))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(value)) => {
                Some((&value.left, &value.right))
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(value)) => {
                Some((&value.left, &value.right))
            }
            _ => None,
        };
        if let Some((left, right)) = binary {
            let Some(left) =
                self.real_arithmetic_constructor_tree(left, line_file, premise_state)?
            else {
                return Ok(None);
            };
            let Some(right) =
                self.real_arithmetic_constructor_tree(right, line_file, premise_state)?
            else {
                return Ok(None);
            };
            let (left, right) = (Box::new(left), Box::new(right));
            return Ok(Some(match expression {
                Obj::ArithmeticOperator(ArithmeticOperator::Add(_)) => Tree::Add { left, right },
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(_)) => Tree::Sub { left, right },
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(_)) => Tree::Mul { left, right },
                Obj::ArithmeticOperator(ArithmeticOperator::Div(_)) => Tree::Div { left, right },
                _ => unreachable!("binary constructor selected above"),
            }));
        }
        match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(value)) => Ok(self
                .real_arithmetic_constructor_tree(&value.arg, line_file, premise_state)?
                .map(|argument| Tree::Neg {
                    argument: Box::new(argument),
                })),
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(value)) => {
                let Some(base) =
                    self.real_arithmetic_constructor_tree(&value.base, line_file, premise_state)?
                else {
                    return Ok(None);
                };
                let Some(exponent) = self.real_constructor_terminal_proof(
                    &value.exponent,
                    StandardSet::Z,
                    line_file,
                    premise_state,
                )?
                else {
                    return Ok(None);
                };
                Ok(Some(Tree::IntegerPow {
                    base: Box::new(base),
                    exponent_in_integer_proof: exponent,
                }))
            }
            _ => Ok(None),
        }
    }

    fn real_constructor_terminal_proof(
        &mut self,
        expression: &Obj,
        set: StandardSet,
        line_file: &Option<SourceLine>,
        premise_state: VerifyState,
    ) -> RuntimeResult<Option<RealArithmeticConstructorTerminalProof>> {
        let fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: expression.clone(),
            set: Obj::StandardSet(set),
            line_file: line_file.clone(),
        };
        // A real function call with a Cartesian argument is a typical leaf.
        // Its argument WD has already run at the parent's ceiling; replaying
        // it here would incorrectly demand its carrier rule below that ceiling.
        Ok(self
            .search_atomic_except_equality_fact_proof(
                &AtomicFact::InFact(fact.clone()),
                premise_state,
            )?
            .map(|searched_proof| RealArithmeticConstructorTerminalProof {
                fact,
                searched_proof: Box::new(searched_proof),
            }))
    }
}

#[cfg(test)]
#[path = "../../../../../../../tests/unit/execute/real_arithmetic_constructor_closure/tests.rs"]
mod tests;
