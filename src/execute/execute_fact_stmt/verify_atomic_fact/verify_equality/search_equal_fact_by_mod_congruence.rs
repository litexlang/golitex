use super::by_builtin_strategy_result::ModCongruenceStrategySingleStep;
use crate::ast::fact::EqualFact;
use crate::ast::obj::{Mod, Obj, ArithmeticOperator, IntegerOperator};
use crate::execute::execute_fact_stmt::verify_state::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Builtin strategy: congruence of a binary expression modulo m.
    // Mathematical property / examples: see ModCongruenceStrategySingleStep.
    pub fn search_equal_fact_by_mod_congruence(
        &mut self,
        fact: &EqualFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<ModCongruenceStrategySingleStep>> {
        let (Obj::IntegerOperator(IntegerOperator::Mod(left_mod)), Obj::IntegerOperator(IntegerOperator::Mod(right_mod))) = (&fact.left, &fact.right) else {
            return Ok(None);
        };
        let pairs = match (left_mod.left.as_ref(), right_mod.left.as_ref()) {
            (Obj::ArithmeticOperator(ArithmeticOperator::Add(left)), Obj::ArithmeticOperator(ArithmeticOperator::Add(right))) => [
                (left.left.as_ref().clone(), right.left.as_ref().clone()),
                (left.right.as_ref().clone(), right.right.as_ref().clone()),
            ],
            (Obj::ArithmeticOperator(ArithmeticOperator::Sub(left)), Obj::ArithmeticOperator(ArithmeticOperator::Sub(right))) => [
                (left.left.as_ref().clone(), right.left.as_ref().clone()),
                (left.right.as_ref().clone(), right.right.as_ref().clone()),
            ],
            (Obj::ArithmeticOperator(ArithmeticOperator::Mul(left)), Obj::ArithmeticOperator(ArithmeticOperator::Mul(right))) => [
                (left.left.as_ref().clone(), right.left.as_ref().clone()),
                (left.right.as_ref().clone(), right.right.as_ref().clone()),
            ],
            _ => return Ok(None),
        };

        let left_modulus = left_mod.right.as_ref();
        let right_modulus = right_mod.right.as_ref();
        let mut requirements = Vec::with_capacity(3);
        requirements.push(
            EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: left_mod.right.as_ref().clone(),
                right: right_mod.right.as_ref().clone(),
                line_file: fact.line_file.clone(),
            }
            .into(),
        );
        for (left_op, right_op) in pairs {
            requirements.push(
                EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: residue_mod(&left_op, left_modulus),
                    right: residue_mod(&right_op, right_modulus),
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

        Ok(Some(ModCongruenceStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}

fn residue_mod(obj: &Obj, modulus: &Obj) -> Obj {
    if let Obj::IntegerOperator(IntegerOperator::Mod(inner)) = obj {
        if inner.right.as_ref() == modulus {
            return obj.clone();
        }
    }
    Obj::IntegerOperator(IntegerOperator::Mod(Mod {
        left: Box::new(obj.clone()),
        right: Box::new(modulus.clone()),
    }))
}
