use super::by_builtin_strategy_result::RationalWithNonzeroPremisesStrategySingleStep;
use crate::ast::fact::{EqualFact, NotEqualFact};
use crate::ast::obj::{ArithmeticOperator, Literal, Number, Obj};
use crate::execute::execute_fact_stmt::verify_state::VerifyState;
use crate::rational_expression::{
    algebraic_normalization_nonzero_requirements, objs_equal_by_rational_expression_evaluation,
};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Builtin strategy search: RationalWithNonzeroPremises.
    // Mathematical property / examples: see RationalWithNonzeroPremisesStrategySingleStep.
    pub fn search_equal_fact_by_rational_with_nonzero_premises(
        &mut self,
        fact: &EqualFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<RationalWithNonzeroPremisesStrategySingleStep>> {
        if !objs_equal_by_rational_expression_evaluation(&fact.left, &fact.right) {
            return Ok(None);
        }
        let mut required_objects = Vec::new();
        for denominator in algebraic_normalization_nonzero_requirements(&fact.left, &fact.right) {
            collect_nonzero_factors(&denominator, &mut required_objects);
        }
        if required_objects.is_empty() {
            // Zero-premise identities belong to Calculation::Rational.
            return Ok(None);
        }

        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        let mut requirements = Vec::with_capacity(required_objects.len());
        for object in required_objects {
            requirements.push(
                NotEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: object,
                    right: zero.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into(),
            );
        }
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };

        Ok(Some(RationalWithNonzeroPremisesStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}

// Nonzero scalar products are equivalent to nonzero factors. Descend only
// through the denominator's strictly smaller Mul children; parent WD retains
// nested domains and carriers. Do not re-enter a broader product strategy.
// Example: b!=0,d!=0 suffice for the denominator b*d in a/b-c/d.
fn collect_nonzero_factors(object: &Obj, factors: &mut Vec<Obj>) {
    if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = object {
        collect_nonzero_factors(&product.left, factors);
        collect_nonzero_factors(&product.right, factors);
    } else if !factors.iter().any(|factor| factor.ir() == object.ir()) {
        factors.push(object.clone());
    }
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/trig_final_examples/tests.rs"]
mod trig_final_examples_tests;
