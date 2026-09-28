use super::helper::{is_zero_obj, zero_obj};
use super::result::NonzeroProductStrategySingleStep;
use crate::new_pipeline::ast::fact::{AtomicFact, NotEqualFact};
use crate::new_pipeline::ast::obj::{ArithmeticOperator, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub(super) fn search_nonzero_product_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
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
            self.verify_strategy_requirements(requirements, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(NonzeroProductStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}
