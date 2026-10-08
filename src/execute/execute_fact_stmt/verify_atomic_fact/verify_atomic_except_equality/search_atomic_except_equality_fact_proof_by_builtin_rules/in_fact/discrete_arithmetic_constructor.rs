use crate::ast::fact::{AtomicFact, InFact};
use crate::ast::obj::{ArithmeticOperator, Obj, StandardSet};
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// The enclosing atomic WD proof owns all constructor children and all function
// domains. This tree adds only carrier truth; it never rechecks WD at a lower
// search ceiling or publishes temporary facts. Sub/Neg are deliberately Z-only.
pub struct DiscreteArithmeticConstructorClosureBuiltinRuleProof {
    pub constructor_tree: DiscreteArithmeticConstructorTree,
}

pub enum DiscreteArithmeticConstructorTree {
    Leaf {
        fact: InFact,
        searched_proof: Box<AtomicExceptEqualityFactSearchedProof>,
    },
    Add {
        left: Box<Self>,
        right: Box<Self>,
    },
    Sub {
        left: Box<Self>,
        right: Box<Self>,
    },
    Mul {
        left: Box<Self>,
        right: Box<Self>,
    },
    Neg {
        argument: Box<Self>,
    },
}

impl Runtime {
    pub(super) fn discrete_arithmetic_constructor_closure_proof(
        &mut self,
        fact: &InFact,
        premise_state: VerifyState,
    ) -> RuntimeResult<Option<DiscreteArithmeticConstructorClosureBuiltinRuleProof>> {
        let Obj::StandardSet(set @ (StandardSet::N | StandardSet::Z)) = &fact.set else {
            return Ok(None);
        };
        Ok(self
            .discrete_arithmetic_constructor_children(&fact.element, set, premise_state)?
            .map(
                |constructor_tree| DiscreteArithmeticConstructorClosureBuiltinRuleProof {
                    constructor_tree,
                },
            ))
    }

    // Strict syntax descent retains the same restricted terminal permission.
    // A terminal search is truth-only: its object WD is a child of the already
    // checked enclosing expression. In particular recursive-call guards are
    // proved once at their owning WD phase, not searched again as carrier truth.
    fn discrete_arithmetic_constructor_tree(
        &mut self,
        expression: &Obj,
        set: &StandardSet,
        state: VerifyState,
    ) -> RuntimeResult<Option<DiscreteArithmeticConstructorTree>> {
        if let Some(tree) = self.discrete_arithmetic_constructor_children(expression, set, state)? {
            return Ok(Some(tree));
        }
        let fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: expression.clone(),
            set: Obj::StandardSet(set.clone()),
            line_file: None,
        };
        Ok(self
            .search_atomic_except_equality_fact_proof(&AtomicFact::InFact(fact.clone()), state)?
            .map(|searched_proof| DiscreteArithmeticConstructorTree::Leaf {
                fact,
                searched_proof: Box::new(searched_proof),
            }))
    }

    fn discrete_arithmetic_constructor_children(
        &mut self,
        expression: &Obj,
        set: &StandardSet,
        state: VerifyState,
    ) -> RuntimeResult<Option<DiscreteArithmeticConstructorTree>> {
        use DiscreteArithmeticConstructorTree as Tree;
        let binary = match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(v)) => Some((&v.left, &v.right)),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(v)) => Some((&v.left, &v.right)),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(v))
                if matches!(set, StandardSet::Z) =>
            {
                Some((&v.left, &v.right))
            }
            _ => None,
        };
        if let Some((left, right)) = binary {
            let Some(left) = self.discrete_arithmetic_constructor_tree(left, set, state)? else {
                return Ok(None);
            };
            let Some(right) = self.discrete_arithmetic_constructor_tree(right, set, state)? else {
                return Ok(None);
            };
            let (left, right) = (Box::new(left), Box::new(right));
            return Ok(Some(match expression {
                Obj::ArithmeticOperator(ArithmeticOperator::Add(_)) => Tree::Add { left, right },
                Obj::ArithmeticOperator(ArithmeticOperator::Sub(_)) => Tree::Sub { left, right },
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(_)) => Tree::Mul { left, right },
                _ => unreachable!("selected binary constructor"),
            }));
        }
        if let Obj::ArithmeticOperator(ArithmeticOperator::Neg(v)) = expression {
            if matches!(set, StandardSet::Z) {
                return Ok(self
                    .discrete_arithmetic_constructor_tree(&v.arg, set, state)?
                    .map(|argument| Tree::Neg {
                        argument: Box::new(argument),
                    }));
            }
        }
        Ok(None)
    }
}

#[cfg(test)]
#[path = "../../../../../../../tests/unit/execute/discrete_arithmetic_constructor_closure/tests.rs"]
mod tests;
