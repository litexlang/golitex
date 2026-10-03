use super::helper::zero_obj;
use super::result::{
    FieldArithmeticCarrierClosureStrategySingleStep, FieldArithmeticCarrierConstructorTree as Tree,
};
use crate::ast::fact::{AtomicFact, Fact};
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{ArithmeticOperator, Obj, StandardSet};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_field_arithmetic_carrier_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<FieldArithmeticCarrierClosureStrategySingleStep>> {
        let AtomicFact::InFact(member) = fact else {
            return Ok(None);
        };
        let Obj::StandardSet(carrier @ (StandardSet::Q | StandardSet::R)) = &member.set else {
            return Ok(None);
        };
        if !is_field_constructor(&member.element) {
            return Ok(None);
        }
        // Constructor descent performs no search. All terminal requirements
        // receive exactly the already restricted central strategy-child state.
        let mut requirements = Vec::new();
        let constructor_tree = self.collect_field_carrier_requirements(
            &member.element,
            carrier,
            &member.line_file,
            &mut requirements,
        );
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(FieldArithmeticCarrierClosureStrategySingleStep {
            carrier: carrier.clone(),
            constructor_tree,
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    fn collect_field_carrier_requirements(
        &mut self,
        expression: &Obj,
        carrier: &StandardSet,
        line_file: &Option<SourceLine>,
        requirements: &mut Vec<Fact>,
    ) -> Tree {
        let mut descend = |rt: &mut Self, child: &Obj| {
            Box::new(rt.collect_field_carrier_requirements(child, carrier, line_file, requirements))
        };
        match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(value)) => Tree::Add {
                left: descend(self, &value.left),
                right: descend(self, &value.right),
            },
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(value)) => Tree::Sub {
                left: descend(self, &value.left),
                right: descend(self, &value.right),
            },
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(value)) => Tree::Neg {
                argument: descend(self, &value.arg),
            },
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(value)) => Tree::Mul {
                left: descend(self, &value.left),
                right: descend(self, &value.right),
            },
            Obj::ArithmeticOperator(ArithmeticOperator::Div(value)) => {
                let left = descend(self, &value.left);
                let right = descend(self, &value.right);
                let nonzero_requirement_index = requirements.len();
                requirements.push(self.strategy_not_equal_fact(
                    value.right.as_ref().clone(),
                    zero_obj(),
                    line_file.clone(),
                ));
                Tree::Div {
                    left,
                    right,
                    nonzero_requirement_index,
                }
            }
            // Any other object remains a terminal, checked ordinary membership
            // goal. Do not unfold a function, power or other constructor here.
            _ => {
                let requirement_index = requirements.len();
                requirements.push(self.strategy_in_fact(
                    expression.clone(),
                    Obj::StandardSet(carrier.clone()),
                    line_file.clone(),
                ));
                Tree::Leaf { requirement_index }
            }
        }
    }
}

fn is_field_constructor(expression: &Obj) -> bool {
    matches!(
        expression,
        Obj::ArithmeticOperator(
            ArithmeticOperator::Add(_)
                | ArithmeticOperator::Sub(_)
                | ArithmeticOperator::Neg(_)
                | ArithmeticOperator::Mul(_)
                | ArithmeticOperator::Div(_)
        )
    )
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/field_arithmetic_carrier_strategy/tests.rs"]
mod field_arithmetic_carrier_strategy_tests;
