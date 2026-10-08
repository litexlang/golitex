use super::by_builtin_strategy_result::ComplexWithNonzeroPremisesStrategySingleStep;
use crate::ast::fact::{EqualFact, NotEqualFact};
use crate::ast::obj::{Literal, Number, Obj};
use crate::execute::execute_fact_stmt::verify_state::VerifyState;
use crate::rational_expression::{
    algebraic_normalization_nonzero_requirements, contains_imaginary_unit,
    objs_equal_by_complex_expression_evaluation,
};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn search_equal_fact_by_complex_with_nonzero_premises(
        &mut self,
        fact: &EqualFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<ComplexWithNonzeroPremisesStrategySingleStep>> {
        if !(contains_imaginary_unit(&fact.left) || contains_imaginary_unit(&fact.right))
            || !objs_equal_by_complex_expression_evaluation(&fact.left, &fact.right)
        {
            return Ok(None);
        }
        let objects = algebraic_normalization_nonzero_requirements(&fact.left, &fact.right);
        if objects.is_empty() {
            return Ok(None);
        }
        let zero = Obj::Literal(Literal::Number(Number::new("0".into())));
        let requirements = objects
            .into_iter()
            .map(|left| {
                NotEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left,
                    right: zero.clone(),
                    line_file: fact.line_file.clone(),
                }
                .into()
            })
            .collect();
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(ComplexWithNonzeroPremisesStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}
