//! Stage B wave 10: empty aggregate identities (sum / product / reduce).
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::{AtomicFact, EqualFact, Fact, LessFact};
use crate::ast::obj::{
    FiniteSetReduce, IteratedOperator, ListSet, Literal, Number, Obj, Product, ProductOfFiniteSet,
    Reduce, SetFormer, Sum, SumOfFiniteSet,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin FiniteSetSumEmpty: finite_set_sum({}, f) = 0.
// Example: finite_set_sum({}, fn(x Z) Z {x}) = 0.
pub struct FiniteSetSumEmptyBuiltinRuleProof {}

// Builtin FiniteSetProductEmpty: finite_set_product({}, f) = 1.
// Example: finite_set_product({}, fn(x Z) Z {x}) = 1.
pub struct FiniteSetProductEmptyBuiltinRuleProof {}

// Builtin FiniteSetReduceEmpty: finite_set_reduce({}, f, op, seed) = seed.
// Example: have seed Z; finite_set_reduce({}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, seed) = seed.
pub struct FiniteSetReduceEmptyBuiltinRuleProof {}

// Builtin ReduceEmpty: end < start ⇒ reduce(start, end, f, op, seed) = seed.
// Example: trust 0 < 1; reduce(1, 0, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 7) = 7.
pub struct ReduceEmptyBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin SumEmptyRange: end < start ⇒ sum(start, end, f) = 0.
// Example: trust 0 < 1; sum(1, 0, fn(x Z) Z {x}) = 0.
pub struct SumEmptyRangeBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ProductEmptyRange: end < start ⇒ product(start, end, f) = 1.
// Example: trust 0 < 1; product(1, 0, fn(x Z) Z {x}) = 1.
pub struct ProductEmptyRangeBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum EqualityIdentitiesWave10BuiltinRuleProof {
    FiniteSetSumEmpty(FiniteSetSumEmptyBuiltinRuleProof),
    FiniteSetProductEmpty(FiniteSetProductEmptyBuiltinRuleProof),
    FiniteSetReduceEmpty(FiniteSetReduceEmptyBuiltinRuleProof),
    ReduceEmpty(ReduceEmptyBuiltinRuleProof),
    SumEmptyRange(SumEmptyRangeBuiltinRuleProof),
    ProductEmptyRange(ProductEmptyRangeBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave10(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave10BuiltinRuleProof>> {
        let child = verify_state;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if finite_set_sum_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave10BuiltinRuleProof::FiniteSetSumEmpty(
                        FiniteSetSumEmptyBuiltinRuleProof {},
                    ),
                ));
            }
            if finite_set_product_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave10BuiltinRuleProof::FiniteSetProductEmpty(
                        FiniteSetProductEmptyBuiltinRuleProof {},
                    ),
                ));
            }
            if finite_set_reduce_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave10BuiltinRuleProof::FiniteSetReduceEmpty(
                        FiniteSetReduceEmptyBuiltinRuleProof {},
                    ),
                ));
            }
            if let Some(p) = self.try_reduce_empty(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave10BuiltinRuleProof::ReduceEmpty(p)));
            }
            if let Some(p) = self.try_sum_empty_range(left, right, child.clone())? {
                return Ok(Some(EqualityIdentitiesWave10BuiltinRuleProof::SumEmptyRange(
                    p,
                )));
            }
            if let Some(p) = self.try_product_empty_range(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave10BuiltinRuleProof::ProductEmptyRange(p),
                ));
            }
        }
        Ok(None)
    }

    fn try_reduce_empty(
        &mut self,
        reduce_side: &Obj,
        other: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ReduceEmptyBuiltinRuleProof>> {
        let Some(reduce) = match_reduce(reduce_side) else {
            return Ok(None);
        };
        if other.ir() != reduce.seed.ir() {
            return Ok(None);
        }
        let premise = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: reduce.end.as_ref().clone(),
            right: reduce.start.as_ref().clone(),
            line_file: None,
        }));
        let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ReduceEmptyBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_sum_empty_range(
        &mut self,
        sum_side: &Obj,
        other: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SumEmptyRangeBuiltinRuleProof>> {
        let Some(sum) = match_sum(sum_side) else {
            return Ok(None);
        };
        if !is_zero_obj(other) {
            return Ok(None);
        }
        let premise = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: sum.end.as_ref().clone(),
            right: sum.start.as_ref().clone(),
            line_file: None,
        }));
        let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(SumEmptyRangeBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_product_empty_range(
        &mut self,
        product_side: &Obj,
        other: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ProductEmptyRangeBuiltinRuleProof>> {
        let Some(product) = match_product(product_side) else {
            return Ok(None);
        };
        if !is_one_obj(other) {
            return Ok(None);
        }
        let premise = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: product.end.as_ref().clone(),
            right: product.start.as_ref().clone(),
            line_file: None,
        }));
        let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ProductEmptyRangeBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }
}

fn match_sum(obj: &Obj) -> Option<&Sum> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::Sum(s)) => Some(s),
        _ => None,
    }
}

fn match_product(obj: &Obj) -> Option<&Product> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::Product(p)) => Some(p),
        _ => None,
    }
}

fn match_reduce(obj: &Obj) -> Option<&Reduce> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::Reduce(r)) => Some(r),
        _ => None,
    }
}

fn match_sum_of_finite_set(obj: &Obj) -> Option<&SumOfFiniteSet> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(s)) => Some(s),
        _ => None,
    }
}

fn match_product_of_finite_set(obj: &Obj) -> Option<&ProductOfFiniteSet> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(p)) => Some(p),
        _ => None,
    }
}

fn match_finite_set_reduce(obj: &Obj) -> Option<&FiniteSetReduce> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(r)) => Some(r),
        _ => None,
    }
}

fn is_empty_list_set(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::SetFormer(SetFormer::ListSet(ListSet { list, .. })) if list.is_empty()
    )
}

fn is_zero_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "0"
    )
}

fn is_one_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "1"
    )
}

fn finite_set_sum_empty_shape(sum_side: &Obj, other: &Obj) -> bool {
    let Some(s) = match_sum_of_finite_set(sum_side) else {
        return false;
    };
    is_empty_list_set(s.set.as_ref()) && is_zero_obj(other)
}

fn finite_set_product_empty_shape(product_side: &Obj, other: &Obj) -> bool {
    let Some(p) = match_product_of_finite_set(product_side) else {
        return false;
    };
    is_empty_list_set(p.set.as_ref()) && is_one_obj(other)
}

fn finite_set_reduce_empty_shape(reduce_side: &Obj, other: &Obj) -> bool {
    let Some(r) = match_finite_set_reduce(reduce_side) else {
        return false;
    };
    is_empty_list_set(r.set.as_ref()) && other.ir() == r.seed.ir()
}
