use crate::ast::fact::{
    AndChainAtomicFact, AtomicFact, EqualFact, Fact, InFact, NotEqualFact, NotInFact, OrFact,
};
use crate::ast::obj::{Obj, SetFormer, SetOperator};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferInFactIntersectBothResult, InferInFactListSetOrEqualitiesResult,
    InferInFactListSetSingletonEqualResult, InferInFactResult, InferInFactSetMinusSplitResult,
    InferInFactUnionOrResult, StoreInferredFactResult,
};

impl Runtime {
    // When: `x $in {…}` / `union` / `intersect` / `set_minus`.
    // Infers: singleton `=`, multi `or` of `=`, union `or` of `$in`, both `$in`, or split.
    // Example: `x $in {2}` ⇒ `x = 2`; `x $in union(A,B)` ⇒ `x $in A or x $in B`.
    pub(super) fn infer_in_fact_list_set_ops_rules(
        &mut self,
        in_fact: &InFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferInFactResult>> {
        let mut rules = Vec::new();
        if let Some(r) = self.infer_in_fact_list_set(in_fact, verify_state)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_union(in_fact, verify_state)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_intersect(in_fact, verify_state)? {
            rules.push(r);
        }
        if let Some(r) = self.infer_in_fact_set_minus(in_fact, verify_state)? {
            rules.push(r);
        }
        Ok(rules)
    }
}

impl Runtime {
    fn infer_in_fact_list_set(
        &mut self,
        in_fact: &InFact,
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferInFactResult>> {
        let Obj::SetFormer(SetFormer::ListSet(list_set)) = &in_fact.set else {
            return Ok(None);
        };
        if list_set.list.is_empty() {
            return Ok(None);
        }
        let lf = in_fact.line_file.clone();
        if let [singleton] = list_set.list.as_slice() {
            let fact_id = self.global_ids.allocate_fact_id();
            let atomic = AtomicFact::EqualFact(EqualFact {
                fact_id,
                left: in_fact.element.clone(),
                right: singleton.as_ref().clone(),
                line_file: lf,
            });
            let derived = Box::new(self.store_inferred_fact(&Fact::AtomicFact(atomic))?);
            return Ok(Some(InferInFactResult::ListSetSingletonEqual(
                InferInFactListSetSingletonEqualResult { derived },
            )));
        }
        let mut branches = Vec::with_capacity(list_set.list.len());
        for item in &list_set.list {
            let fact_id = self.global_ids.allocate_fact_id();
            branches.push(AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(
                EqualFact {
                    fact_id,
                    left: in_fact.element.clone(),
                    right: item.as_ref().clone(),
                    line_file: lf.clone(),
                },
            )));
        }
        let fact_id = self.global_ids.allocate_fact_id();
        let or_fact = Fact::OrFact(OrFact {
            fact_id,
            facts: branches,
            line_file: lf,
        });
        let derived = Box::new(self.store_inferred_fact(&or_fact)?);
        Ok(Some(InferInFactResult::ListSetOrEqualities(
            InferInFactListSetOrEqualitiesResult { derived },
        )))
    }

    fn infer_in_fact_union(
        &mut self,
        in_fact: &InFact,
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferInFactResult>> {
        let Obj::SetOperator(SetOperator::Union(union)) = &in_fact.set else {
            return Ok(None);
        };
        let lf = in_fact.line_file.clone();
        let left_id = self.global_ids.allocate_fact_id();
        let right_id = self.global_ids.allocate_fact_id();
        let or_id = self.global_ids.allocate_fact_id();
        let or_fact = Fact::OrFact(OrFact {
            fact_id: or_id,
            facts: vec![
                AndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: left_id,
                    element: in_fact.element.clone(),
                    set: union.left.as_ref().clone(),
                    line_file: lf.clone(),
                })),
                AndChainAtomicFact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: right_id,
                    element: in_fact.element.clone(),
                    set: union.right.as_ref().clone(),
                    line_file: lf.clone(),
                })),
            ],
            line_file: lf,
        });
        let derived = Box::new(self.store_inferred_fact(&or_fact)?);
        Ok(Some(InferInFactResult::UnionOr(InferInFactUnionOrResult {
            derived,
        })))
    }

    fn infer_in_fact_intersect(
        &mut self,
        in_fact: &InFact,
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferInFactResult>> {
        let Obj::SetOperator(SetOperator::Intersect(intersect)) = &in_fact.set else {
            return Ok(None);
        };
        let lf = in_fact.line_file.clone();
        let mut derived: Vec<StoreInferredFactResult> = Vec::with_capacity(2);
        let left_id = self.global_ids.allocate_fact_id();
        derived.push(
            self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: left_id,
                element: in_fact.element.clone(),
                set: intersect.left.as_ref().clone(),
                line_file: lf.clone(),
            })))?,
        );
        let right_id = self.global_ids.allocate_fact_id();
        derived.push(
            self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: right_id,
                element: in_fact.element.clone(),
                set: intersect.right.as_ref().clone(),
                line_file: lf,
            })))?,
        );
        Ok(Some(InferInFactResult::IntersectBoth(
            InferInFactIntersectBothResult {
                left_membership: derived.remove(0),
                right_membership: derived.remove(0),
            },
        )))
    }

    fn infer_in_fact_set_minus(
        &mut self,
        in_fact: &InFact,
        _verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Option<InferInFactResult>> {
        let Obj::SetOperator(SetOperator::SetMinus(sm)) = &in_fact.set else {
            return Ok(None);
        };
        let lf = in_fact.line_file.clone();
        let right_set = sm.right.as_ref().clone();
        let mut derived: Vec<StoreInferredFactResult> = Vec::new();
        let in_left_id = self.global_ids.allocate_fact_id();
        derived.push(
            self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::InFact(InFact {
                fact_id: in_left_id,
                element: in_fact.element.clone(),
                set: sm.left.as_ref().clone(),
                line_file: lf.clone(),
            })))?,
        );
        let not_in_id = self.global_ids.allocate_fact_id();
        derived.push(
            self.store_inferred_fact(&Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
                fact_id: not_in_id,
                element: in_fact.element.clone(),
                set: right_set.clone(),
                line_file: lf.clone(),
            })))?,
        );
        if let Obj::SetFormer(SetFormer::ListSet(list_set)) = &right_set {
            if let [excluded] = list_set.list.as_slice() {
                let ne_id = self.global_ids.allocate_fact_id();
                derived.push(self.store_inferred_fact(&Fact::AtomicFact(
                    AtomicFact::NotEqualFact(NotEqualFact {
                        fact_id: ne_id,
                        left: in_fact.element.clone(),
                        right: excluded.as_ref().clone(),
                        line_file: lf,
                    }),
                ))?);
            }
        }
        Ok(Some(InferInFactResult::SetMinusSplit(
            InferInFactSetMinusSplitResult {
                base_membership: derived.remove(0),
                excluded_membership: derived.remove(0),
                singleton_inequality: derived.pop(),
            },
        )))
    }
}
