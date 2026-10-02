use super::by_builtin_strategy_result::{
    ArithmeticCongruenceStrategySingleStep, TupleComponentEqualityStrategySingleStep,
};
use super::helper::corresponding_arg_pairs;
use crate::ast::fact::EqualFact;
use crate::ast::obj::{Obj, ProductShape};
use crate::execute::execute_fact_stmt::strategy_search::StrategySearch;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Scalar coordinate expressions may need a projection/calculation at an
    // operand. This only peels matching arithmetic nodes, within the existing
    // strategy depth; it does not unfold functions or rewrite other shapes.
    pub fn search_equal_fact_by_arithmetic_congruence(
        &mut self,
        fact: &EqualFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<ArithmeticCongruenceStrategySingleStep>> {
        if !ctx.can_use_strategy()
            || !matches!(
                (&fact.left, &fact.right),
                (Obj::ArithmeticOperator(_), Obj::ArithmeticOperator(_))
            )
        {
            return Ok(None);
        }
        let Some(pairs) = corresponding_arg_pairs(&fact.left, &fact.right) else {
            return Ok(None);
        };
        if pairs.is_empty() {
            return Ok(None);
        }
        let requirements = pairs
            .into_iter()
            .map(|(left, right)| {
                EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left,
                    right,
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
        Ok(Some(ArithmeticCongruenceStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    // Constructor congruence with bounded, proof-producing coordinate search.
    // Known-only MatchingOneArgByOne keeps its existing behavior.
    pub fn search_equal_fact_by_tuple_components(
        &mut self,
        fact: &EqualFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<TupleComponentEqualityStrategySingleStep>> {
        if !ctx.can_use_strategy() {
            return Ok(None);
        }
        let (
            Obj::ProductShape(ProductShape::Tuple(left)),
            Obj::ProductShape(ProductShape::Tuple(right)),
        ) = (&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if left.args.len() != right.args.len() {
            return Ok(None);
        }
        let requirements = left
            .args
            .iter()
            .zip(&right.args)
            .map(|(left, right)| {
                EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: left.as_ref().clone(),
                    right: right.as_ref().clone(),
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
        Ok(Some(TupleComponentEqualityStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}
