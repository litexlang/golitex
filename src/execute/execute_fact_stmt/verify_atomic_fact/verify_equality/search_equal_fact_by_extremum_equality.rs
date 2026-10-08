use super::by_builtin_strategy_result::ExtremumEqualityStrategySingleStep;
use crate::ast::fact::{EqualFact, LessEqualFact};
use crate::ast::obj::{ArithmeticOperator, FiniteSetStat, Obj};
use crate::execute::execute_fact_stmt::verify_state::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Builtin strategy: finite extremum equality via both weak-order directions.
    // Mathematical property / examples: see ExtremumEqualityStrategySingleStep.
    pub fn search_equal_fact_by_extremum_equality(
        &mut self,
        fact: &EqualFact,
        ctx: VerifyState,
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

        let requirements = vec![
            LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.left.clone(),
                right: fact.right.clone(),
                line_file: fact.line_file.clone(),
            }
            .into(),
            LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.right.clone(),
                right: fact.left.clone(),
                line_file: fact.line_file.clone(),
            }
            .into(),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(ExtremumEqualityStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}
