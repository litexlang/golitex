//! Cardinality of an ordered natural-number range, with its three checked premises.
use super::EqualitySearchProofByBuiltinRule;
use crate::ast::fact::{EqualFact, Fact, InFact, LessEqualFact};
use crate::ast::obj::{FiniteSetStat, Literal, Number, Obj, SetFormer, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::{
    helper::{add_objs, sub_objs},
    objs_equal_by_rational_expression_evaluation,
};
use crate::runtime::{Runtime, RuntimeResult};

pub struct RangeSizeProof {
    pub start_natural: VerifyFactResult,
    pub end_natural: VerifyFactResult,
    pub endpoint_order: VerifyFactResult,
}
pub struct ClosedRangeSizeProof {
    pub start_natural: VerifyFactResult,
    pub end_natural: VerifyFactResult,
    pub endpoint_order: VerifyFactResult,
}

impl Runtime {
    pub(super) fn search_range_size(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRule>> {
        // a,b in N and a<=b: |[a,b)|=b-a, |[a,b]|=b-a+1.
        for (size, value) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(size)) = size else {
                continue;
            };
            let (start, end, closed) = match size.set.as_ref() {
                Obj::SetFormer(SetFormer::Range(r)) => (&*r.start, &*r.end, false),
                Obj::SetFormer(SetFormer::ClosedRange(r)) => (&*r.start, &*r.end, true),
                _ => continue,
            };
            let difference = sub_objs(end.clone(), start.clone());
            let expected = if closed {
                add_objs(
                    difference,
                    Obj::Literal(Literal::Number(Number::new("1".into()))),
                )
            } else {
                difference
            };
            if !objs_equal_by_rational_expression_evaluation(&expected, value) {
                continue;
            }
            let start_fact: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: start.clone(),
                set: Obj::StandardSet(StandardSet::N),
                line_file: fact.line_file.clone(),
            }
            .into();
            let start_natural = self.verify_builtin_rule_premise(&start_fact, state)?;
            if start_natural.is_failed() {
                continue;
            }
            let end_fact: Fact = InFact {
                fact_id: self.global_ids.allocate_fact_id(),
                element: end.clone(),
                set: Obj::StandardSet(StandardSet::N),
                line_file: fact.line_file.clone(),
            }
            .into();
            let end_natural = self.verify_builtin_rule_premise(&end_fact, state)?;
            if end_natural.is_failed() {
                continue;
            }
            let order: Fact = LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: start.clone(),
                right: end.clone(),
                line_file: fact.line_file.clone(),
            }
            .into();
            let endpoint_order = self.verify_builtin_rule_premise(&order, state)?;
            if endpoint_order.is_failed() {
                continue;
            }
            return Ok(Some(if closed {
                EqualitySearchProofByBuiltinRule::ClosedRangeSize(ClosedRangeSizeProof {
                    start_natural,
                    end_natural,
                    endpoint_order,
                })
            } else {
                EqualitySearchProofByBuiltinRule::RangeSize(RangeSizeProof {
                    start_natural,
                    end_natural,
                    endpoint_order,
                })
            }));
        }
        Ok(None)
    }
}
