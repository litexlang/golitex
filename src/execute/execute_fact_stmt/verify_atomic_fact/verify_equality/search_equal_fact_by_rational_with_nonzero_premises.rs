use super::by_builtin_strategy_result::RationalWithNonzeroPremisesStrategySingleStep;
use crate::ast::fact::{EqualFact, NotEqualFact};
use crate::ast::obj::{Number, Obj, Literal};
use crate::execute::execute_fact_stmt::strategy_search::StrategySearch;
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
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<RationalWithNonzeroPremisesStrategySingleStep>> {
        if !objs_equal_by_rational_expression_evaluation(&fact.left, &fact.right) {
            return Ok(None);
        }
        let required_objects =
            algebraic_normalization_nonzero_requirements(&fact.left, &fact.right);
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
