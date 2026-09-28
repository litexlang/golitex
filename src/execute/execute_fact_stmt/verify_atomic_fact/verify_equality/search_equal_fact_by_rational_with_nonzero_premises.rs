use super::by_builtin_strategy_result::RationalWithNonzeroPremisesStrategySingleStep;
use crate::ast::fact::{EqualFact, Fact, NotEqualFact};
use crate::ast::obj::{Number, Obj, Literal};
use crate::execute::execute_fact_stmt::VerifyState;
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
        verify_state: VerifyState,
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
        let mut requirement_facts = Vec::with_capacity(required_objects.len());
        let mut proof_of_requirement_facts = Vec::with_capacity(required_objects.len());
        let child_state = verify_state.without_well_defined_storage();

        for object in required_objects {
            let premise: Fact = NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: object,
                right: zero.clone(),
                line_file: fact.line_file.clone(),
            }
            .into();
            let proof = self.verify_fact(&premise, child_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            requirement_facts.push(premise);
            proof_of_requirement_facts.push(proof);
        }

        Ok(Some(RationalWithNonzeroPremisesStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}
