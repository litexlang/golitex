use super::result::NegatedOrderStrategySingleStep;
use crate::prelude::*;

impl Runtime {
    pub(super) fn search_negated_order_strategy(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<NegatedOrderStrategySingleStep>> {
        // Total real order: not (a > b) iff a <= b, and likewise for
        // the other three comparisons. Example: a <= 900 implies not a > 1070.
        // Only negative goals enter this branch. Remove their negation and
        // verify the complement at the existing strategy-premise ceiling;
        // never reopen strategy, forall, or rewrite search here.
        if !matches!(
            fact,
            AtomicFact::NotGreaterFact(_)
                | AtomicFact::NotLessFact(_)
                | AtomicFact::NotGreaterEqualFact(_)
                | AtomicFact::NotLessEqualFact(_)
        ) {
            return Ok(None);
        }
        let fact_id = self.global_ids.allocate_fact_id();
        let complement: AtomicFact = match fact {
            AtomicFact::NotGreaterFact(f) => LessEqualFact {
                fact_id,
                left: f.left.clone(),
                right: f.right.clone(),
                line_file: f.line_file.clone(),
            }
            .into(),
            AtomicFact::NotLessFact(f) => GreaterEqualFact {
                fact_id,
                left: f.left.clone(),
                right: f.right.clone(),
                line_file: f.line_file.clone(),
            }
            .into(),
            AtomicFact::NotGreaterEqualFact(f) => LessFact {
                fact_id,
                left: f.left.clone(),
                right: f.right.clone(),
                line_file: f.line_file.clone(),
            }
            .into(),
            AtomicFact::NotLessEqualFact(f) => GreaterFact {
                fact_id,
                left: f.left.clone(),
                right: f.right.clone(),
                line_file: f.line_file.clone(),
            }
            .into(),
            _ => return Ok(None),
        };
        let mut requirements = Vec::new();
        for operand in atomic_fact_args_ref(&complement) {
            requirements.push(
                InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: operand.clone(),
                    set: Obj::StandardSet(StandardSet::R),
                    line_file: None,
                }
                .into(),
            );
        }
        requirements.push(complement.into());
        let Some((requirement_facts, proof_of_requirement_facts)) =
            self.verify_strategy_requirements(requirements, ctx)?
        else {
            return Ok(None);
        };
        Ok(Some(NegatedOrderStrategySingleStep::new(
            requirement_facts,
            proof_of_requirement_facts,
        )))
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/negated_order/tests.rs"]
mod tests;
