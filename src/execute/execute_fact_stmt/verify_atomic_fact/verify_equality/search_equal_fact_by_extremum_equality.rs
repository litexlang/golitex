use super::by_builtin_strategy_result::ExtremumEqualityStrategySingleStep;
use crate::ast::fact::{EqualFact, Fact, LessEqualFact};
use crate::ast::obj::{Obj, ArithmeticOperator, FiniteSetStat};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

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
                Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(_))
                    | Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(_))
                    | Obj::ArithmeticOperator(ArithmeticOperator::Max(_))
                    | Obj::ArithmeticOperator(ArithmeticOperator::Min(_)),
                _
            ) | (
                _,
                Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(_))
                    | Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(_))
                    | Obj::ArithmeticOperator(ArithmeticOperator::Max(_))
                    | Obj::ArithmeticOperator(ArithmeticOperator::Min(_))
            )
        );
        if !has_extremum {
            return Ok(None);
        }

        let child_state = verify_state.after_strategy();
        let required = [
            LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.left.clone(),
                right: fact.right.clone(),
                line_file: fact.line_file.clone(),
            },
            LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
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
