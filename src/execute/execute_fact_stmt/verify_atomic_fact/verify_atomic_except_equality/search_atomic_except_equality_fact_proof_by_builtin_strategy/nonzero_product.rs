use super::helper::{is_zero_obj, zero_obj};
use super::result::NonzeroProductStrategySingleStep;
use crate::ast::fact::{AtomicFact, NotEqualFact};
use crate::ast::obj::{ArithmeticOperator, Obj};
use crate::execute::execute_fact_stmt::strategy_search::StrategySearch;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_nonzero_product_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: StrategySearch,
    ) -> RuntimeResult<Option<NonzeroProductStrategySingleStep>> {
        let AtomicFact::NotEqualFact(NotEqualFact { left, right, line_file, .. }) = fact else {
            return Ok(None);
        };
        let expression = if is_zero_obj(right) {
            left
        } else if is_zero_obj(left) {
            right
        } else {
            return Ok(None);
        };
        let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = expression else {
            return Ok(None);
        };
        let requirements = vec![
            self.strategy_not_equal_fact(product.left.as_ref().clone(), zero_obj(), line_file.clone()),
            self.strategy_not_equal_fact(product.right.as_ref().clone(), zero_obj(), line_file.clone()),
        ];
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(NonzeroProductStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}
