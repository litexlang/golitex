use super::by_builtin_strategy_result::ExtremumEqualityStrategySingleStep;
use crate::new_pipeline::ast::fact::{EqualFact, Fact, LessEqualFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Builtin strategy: finite extremum equality via both weak-order directions.
    // Mathematical property / examples: see ExtremumEqualityStrategySingleStep.
    pub fn search_equal_fact_by_extremum_equality(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExtremumEqualityStrategySingleStep>> {
        let has_extremum = matches!(
            (&fact.left, &fact.right),
            (
                Obj::FiniteSetMax(_)
                    | Obj::FiniteSetMin(_)
                    | Obj::Max(_)
                    | Obj::Min(_),
                _
            ) | (
                _,
                Obj::FiniteSetMax(_)
                    | Obj::FiniteSetMin(_)
                    | Obj::Max(_)
                    | Obj::Min(_)
            )
        );
        if !has_extremum {
            return Ok(None);
        }

        let child_state = verify_state.without_well_defined_storage();
        let required = [
            LessEqualFact {
                fact_id: self.ids.allocate_fact_id(),
                left: fact.left.clone(),
                right: fact.right.clone(),
                line_file: fact.line_file.clone(),
            },
            LessEqualFact {
                fact_id: self.ids.allocate_fact_id(),
                left: fact.right.clone(),
                right: fact.left.clone(),
                line_file: fact.line_file.clone(),
            },
        ];
        let mut requirement_facts = Vec::with_capacity(2);
        let mut proof_of_requirement_facts = Vec::with_capacity(2);
        for child in required {
            let premise: Fact = child.into();
            let proof = self.verify_fact(&premise, child_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            requirement_facts.push(premise);
            proof_of_requirement_facts.push(proof);
        }
        Ok(Some(ExtremumEqualityStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}
