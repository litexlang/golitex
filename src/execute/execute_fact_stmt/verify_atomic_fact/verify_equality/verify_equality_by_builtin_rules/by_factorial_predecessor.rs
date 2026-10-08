//! Positive-natural factorial recurrence in predecessor form.
use crate::ast::fact::{EqualFact, Fact, InFact};
use crate::ast::obj::{ArithmeticOperator, IntegerOperator, Literal, Number, Obj, StandardSet, Sub};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::objs_equal_by_rational_expression_evaluation;
use crate::runtime::{Runtime, RuntimeResult};

pub struct FactorialPredecessorProof {
    pub positive_natural: VerifyFactResult,
}
impl FactorialPredecessorProof {
    pub fn new(positive_natural: VerifyFactResult) -> Self { Self { positive_natural } }
}
impl Runtime {
    pub(super) fn search_factorial_predecessor(
        &mut self, fact: &EqualFact, state: VerifyState,
    ) -> RuntimeResult<Option<FactorialPredecessorProof>> {
        // n in N+ => factorial(n)=n*factorial(n-1), with either factor order.
        // Parent WD retains the natural predecessor; n=0 is not a legal case.
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::IntegerOperator(IntegerOperator::Factorial(factorial)) = left else { continue; };
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = right else { continue; };
            for (coefficient, previous) in [(&*product.left, &*product.right), (&*product.right, &*product.left)] {
                if coefficient.ir() != factorial.arg.ir() { continue; }
                let Obj::IntegerOperator(IntegerOperator::Factorial(previous)) = previous else { continue; };
                let predecessor = Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
                    left: factorial.arg.clone(), right: Box::new(Obj::Literal(Literal::Number(Number::new("1".into())))),
                }));
                if !objs_equal_by_rational_expression_evaluation(&previous.arg, &predecessor) { continue; }
                let requirement: Fact = InFact {
                    fact_id: self.global_ids.allocate_fact_id(), element: *factorial.arg.clone(),
                    set: Obj::StandardSet(StandardSet::NPos), line_file: fact.line_file.clone(),
                }.into();
                let positive_natural = self.verify_builtin_rule_premise(&requirement, state)?;
                if !positive_natural.is_failed() { return Ok(Some(FactorialPredecessorProof::new(positive_natural))); }
            }
        }
        Ok(None)
    }
}
