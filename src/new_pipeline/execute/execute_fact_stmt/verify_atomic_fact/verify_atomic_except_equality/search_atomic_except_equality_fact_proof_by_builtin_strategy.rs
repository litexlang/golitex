use crate::new_pipeline::ast::fact::{AtomicFact, Fact, GreaterFact, LessFact};
use crate::new_pipeline::ast::obj::{Number, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub enum AtomicExceptEqualityFactSearchProofByBuiltinStrategy {
    PosAddPosIsPos(PosAddPosIsPosStrategySingleStep),
}

// Strategy: sum of two strictly positive quantities is strictly positive.
// Mathematical property: if a > 0 and b > 0, then a + b > 0
// (equivalently 0 < a + b).
//
// Example:
//   have a, b R
//   trust a > 0
//   trust b > 0
//   a + b > 0
pub struct PosAddPosIsPosStrategySingleStep {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_builtin_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinStrategy>> {
        if let Some(proof) =
            self.search_pos_add_pos_is_pos_strategy(fact, verify_state)?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PosAddPosIsPos(proof),
            ));
        }
        Ok(None)
    }

    fn search_pos_add_pos_is_pos_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<PosAddPosIsPosStrategySingleStep>> {
        let Some((left_summand, right_summand, line_file)) = positive_sum_goal_summands(fact)
        else {
            return Ok(None);
        };

        let child_state = verify_state.without_well_defined_storage();
        let mut requirement_facts = Vec::with_capacity(2);
        let mut proof_of_requirement_facts = Vec::with_capacity(2);

        for summand in [left_summand, right_summand] {
            let premise: Fact = GreaterFact {
                fact_id: self.ids.allocate_fact_id(),
                left: summand,
                right: zero_obj(),
                line_file: line_file.clone(),
            }
            .into();
            let proof = self.verify_fact(&premise, child_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            requirement_facts.push(premise);
            proof_of_requirement_facts.push(proof);
        }

        Ok(Some(PosAddPosIsPosStrategySingleStep {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }
}

fn zero_obj() -> Obj {
    Obj::Number(Number {
        normalized_value: "0".to_string(),
    })
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Number(Number {
            normalized_value,
        }) if normalized_value == "0"
    )
}

// Match `a + b > 0` or `0 < a + b`. Soft miss otherwise.
fn positive_sum_goal_summands(fact: &AtomicFact) -> Option<(Obj, Obj, Option<crate::new_pipeline::ast::line_file::LineFile>)> {
    match fact {
        AtomicFact::GreaterFact(GreaterFact {
            left,
            right,
            line_file,
            ..
        }) if is_zero_obj(right) => {
            if let Obj::Add(add) = left {
                Some((
                    add.left.as_ref().clone(),
                    add.right.as_ref().clone(),
                    line_file.clone(),
                ))
            } else {
                None
            }
        }
        AtomicFact::LessFact(LessFact {
            left,
            right,
            line_file,
            ..
        }) if is_zero_obj(left) => {
            if let Obj::Add(add) = right {
                Some((
                    add.left.as_ref().clone(),
                    add.right.as_ref().clone(),
                    line_file.clone(),
                ))
            } else {
                None
            }
        }
        _ => None,
    }
}
