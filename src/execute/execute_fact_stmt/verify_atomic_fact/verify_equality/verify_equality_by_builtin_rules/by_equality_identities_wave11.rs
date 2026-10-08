//! Stage B wave 11: remaining high-value Obj equality builtins.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, LessFact, SubsetFact,
};
use crate::ast::obj::{
    Add, AnonymousFn, ArithmeticOperator, Cart, ClosedRange, ExpLogOperator, FiniteSetReduce,
    FiniteSetSize, FiniteSetStat, FnObj, FnObjHead, FunctionSpace, Intersect, IteratedOperator,
    ListSet, Literal, Log, Number, Obj, Pow, Product, ProductShape, Reduce,
    SetFormer, SetMinus, SetOperator, Sub, Sum, SumOfFiniteSet, Tuple, Union,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::anonymous_fns_alpha_equal;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};
use crate::execute::execute_fact_stmt::known_tuple::literal_positive_usize;

// Builtin UnionAbsorptionFromSubset: A ⊆ B ⇒ union(A, B) = B (either operand order).
// Example: have A set; have B set; trust A $subset B; union(A, B) = B.
pub struct UnionAbsorptionFromSubsetBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin SetMinusRecoversSubset: B ⊆ A ⇒ B = set_minus(A, set_minus(A, B)).
// Example: have A set; have B set; trust B $subset A; B = set_minus(A, set_minus(A, B)).
pub struct SetMinusRecoversSubsetBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin EmptySetFromSizeZero: finite_set_size(A) = 0 ⇒ A = {}.
// Example: have A finite_set; trust finite_set_size(A) = 0; A = {}.
pub struct EmptySetFromSizeZeroBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin FiniteSetSizeSetMinus:
//   finite_set_size(set_minus(A, B)) = finite_set_size(A) - finite_set_size(intersect(A, B)).
// Example: have A finite_set; have B finite_set;
//          finite_set_size(set_minus(A, B)) = finite_set_size(A) - finite_set_size(intersect(A, B)).
pub struct FiniteSetSizeSetMinusBuiltinRuleProof {}

// Builtin FiniteSetSizeUnion:
//   finite_set_size(union(A, B)) =
//     finite_set_size(A) + finite_set_size(B) - finite_set_size(intersect(A, B)).
// Example: have A finite_set; have B finite_set;
//          finite_set_size(union(A, B)) =
//            finite_set_size(A) + finite_set_size(B) - finite_set_size(intersect(A, B)).
pub struct FiniteSetSizeUnionBuiltinRuleProof {}

// Builtin ClosedRangeSingletonListSet: closed_range(a, a) = {a}.
// Example: closed_range(1, 1) = {1}.
pub struct ClosedRangeSingletonListSetBuiltinRuleProof {}

// Builtin SumSingleTerm: start = end ⇒ sum(start, end, f) = f(start).
// Example: sum(3, 3, fn(x Z) Z {x}) = 3.
pub struct SumSingleTermBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ProductSingleTerm: start = end ⇒ product(start, end, f) = f(start).
// Example: product(3, 3, fn(x Z) Z {x}) = 3.
pub struct ProductSingleTermBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin ReduceAddZeroEqualsSum:
//   reduce(s, e, f, add, 0) = sum(s, e, f) when op is binary addition.
// Example: reduce(1, 3, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = sum(1, 3, fn(x Z) Z {x}).
pub struct ReduceAddZeroEqualsSumBuiltinRuleProof {}

// Builtin FiniteSetReduceAddZeroEqualsSum:
//   finite_set_reduce(S, f, add, 0) = finite_set_sum(S, f).
// Example: finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0)
//          = finite_set_sum({1, 2}, fn(x Z) Z {x}).
pub struct FiniteSetReduceAddZeroEqualsSumBuiltinRuleProof {}

// Builtin PowOfLogInverse: b^(log(b, x)) = x when 1 < b and 0 < x.
// Example: have x N+; 2^(log(2, x)) = x.
pub struct PowOfLogInverseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub enum EqualityIdentitiesWave11BuiltinRuleProof {
    UnionAbsorptionFromSubset(UnionAbsorptionFromSubsetBuiltinRuleProof),
    SetMinusRecoversSubset(SetMinusRecoversSubsetBuiltinRuleProof),
    EmptySetFromSizeZero(EmptySetFromSizeZeroBuiltinRuleProof),

    FiniteSetSizeSetMinus(FiniteSetSizeSetMinusBuiltinRuleProof),
    FiniteSetSizeUnion(FiniteSetSizeUnionBuiltinRuleProof),
    ClosedRangeSingletonListSet(ClosedRangeSingletonListSetBuiltinRuleProof),
    SumSingleTerm(SumSingleTermBuiltinRuleProof),
    ProductSingleTerm(ProductSingleTermBuiltinRuleProof),
    ReduceAddZeroEqualsSum(ReduceAddZeroEqualsSumBuiltinRuleProof),
    FiniteSetReduceAddZeroEqualsSum(FiniteSetReduceAddZeroEqualsSumBuiltinRuleProof),
    PowOfLogInverse(PowOfLogInverseBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave11(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave11BuiltinRuleProof>> {
        let child = verify_state;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if finite_set_size_set_minus_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave11BuiltinRuleProof::FiniteSetSizeSetMinus(
                        FiniteSetSizeSetMinusBuiltinRuleProof {},
                    ),
                ));
            }
            if finite_set_size_union_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave11BuiltinRuleProof::FiniteSetSizeUnion(
                        FiniteSetSizeUnionBuiltinRuleProof {},
                    ),
                ));
            }
            if closed_range_singleton_list_set_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave11BuiltinRuleProof::ClosedRangeSingletonListSet(
                        ClosedRangeSingletonListSetBuiltinRuleProof {},
                    ),
                ));
            }
            if reduce_add_zero_equals_sum_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave11BuiltinRuleProof::ReduceAddZeroEqualsSum(
                        ReduceAddZeroEqualsSumBuiltinRuleProof {},
                    ),
                ));
            }
            if finite_set_reduce_add_zero_equals_sum_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave11BuiltinRuleProof::FiniteSetReduceAddZeroEqualsSum(
                        FiniteSetReduceAddZeroEqualsSumBuiltinRuleProof {},
                    ),
                ));
            }
            if let Some(p) = self.try_pow_of_log_inverse(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave11BuiltinRuleProof::PowOfLogInverse(p),
                ));
            }
            if let Some(p) = self.try_sum_single_term(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave11BuiltinRuleProof::SumSingleTerm(p),
                ));
            }
            if let Some(p) = self.try_product_single_term(left, right, child.clone())? {
                return Ok(Some(
                    EqualityIdentitiesWave11BuiltinRuleProof::ProductSingleTerm(p),
                ));
            }
        }
        if let Some(p) = self.try_union_absorption_from_subset(fact, child.clone())? {
            return Ok(Some(
                EqualityIdentitiesWave11BuiltinRuleProof::UnionAbsorptionFromSubset(p),
            ));
        }
        if let Some(p) = self.try_set_minus_recovers_subset(fact, child.clone())? {
            return Ok(Some(
                EqualityIdentitiesWave11BuiltinRuleProof::SetMinusRecoversSubset(p),
            ));
        }
        if let Some(p) = self.try_empty_set_from_size_zero(fact, child)? {
            return Ok(Some(
                EqualityIdentitiesWave11BuiltinRuleProof::EmptySetFromSizeZero(p),
            ));
        }
        Ok(None)
    }

    fn try_union_absorption_from_subset(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<UnionAbsorptionFromSubsetBuiltinRuleProof>> {
        for (union_side, retained) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Some(u) = match_union(union_side) else {
                continue;
            };
            let (subset, container) = if retained.ir() == u.right.ir() {
                (u.left.as_ref(), u.right.as_ref())
            } else if retained.ir() == u.left.ir() {
                (u.right.as_ref(), u.left.as_ref())
            } else {
                continue;
            };
            let premise = Fact::AtomicFact(AtomicFact::SubsetFact(SubsetFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: subset.clone(),
                right: container.clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
            if proof.is_failed() {
                continue;
            }
            return Ok(Some(UnionAbsorptionFromSubsetBuiltinRuleProof {
                proof_of_requirement_facts: vec![proof],
            }));
        }
        Ok(None)
    }

    fn try_set_minus_recovers_subset(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SetMinusRecoversSubsetBuiltinRuleProof>> {
        for (subset_side, recovery_side) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            let Some(outer) = match_set_minus(recovery_side) else {
                continue;
            };
            let Some(inner) = match_set_minus(outer.right.as_ref()) else {
                continue;
            };
            if outer.left.ir() != inner.left.ir() {
                continue;
            }
            if subset_side.ir() != inner.right.ir() {
                continue;
            }
            let premise = Fact::AtomicFact(AtomicFact::SubsetFact(SubsetFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: subset_side.clone(),
                right: outer.left.as_ref().clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
            if proof.is_failed() {
                continue;
            }
            return Ok(Some(SetMinusRecoversSubsetBuiltinRuleProof {
                proof_of_requirement_facts: vec![proof],
            }));
        }
        Ok(None)
    }

    fn try_empty_set_from_size_zero(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EmptySetFromSizeZeroBuiltinRuleProof>> {
        let set = match (&fact.left, &fact.right) {
            (left, right) if is_empty_list_set(left) => right,
            (left, right) if is_empty_list_set(right) => left,
            _ => return Ok(None),
        };
        let size = Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
            set: Box::new(set.clone()),
        }));
        let premise = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: size,
            right: zero_obj(),
            line_file: None,
        }));
        let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(EmptySetFromSizeZeroBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_sum_single_term(
        &mut self,
        sum_side: &Obj,
        other: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SumSingleTermBuiltinRuleProof>> {
        let Some(sum) = match_sum(sum_side) else {
            return Ok(None);
        };
        if sum.start.ir() != sum.end.ir() {
            return Ok(None);
        }
        let Some(applied) = apply_fn_one_arg(sum.func.as_ref(), sum.start.as_ref().clone()) else {
            return Ok(None);
        };
        let premise = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: applied,
            right: other.clone(),
            line_file: None,
        }));
        let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(SumSingleTermBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_product_single_term(
        &mut self,
        product_side: &Obj,
        other: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ProductSingleTermBuiltinRuleProof>> {
        let Some(product) = match_product(product_side) else {
            return Ok(None);
        };
        if product.start.ir() != product.end.ir() {
            return Ok(None);
        }
        let Some(applied) = apply_fn_one_arg(product.func.as_ref(), product.start.as_ref().clone())
        else {
            return Ok(None);
        };
        let premise = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: applied,
            right: other.clone(),
            line_file: None,
        }));
        let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(ProductSingleTermBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
        }))
    }

    fn try_pow_of_log_inverse(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<PowOfLogInverseBuiltinRuleProof>> {
        let Some((base, exp)) = match_pow(left) else {
            return Ok(None);
        };
        let Some((lbase, larg)) = match_log(exp) else {
            return Ok(None);
        };
        if base.ir() != lbase.ir() || larg.ir() != right.ir() {
            return Ok(None);
        }
        let base_gt_one = self.verify_order_gt_one(base, verify_state.clone())?;
        if base_gt_one.is_failed() {
            return Ok(None);
        }
        let arg_pos = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: zero_obj(),
            right: larg.clone(),
            line_file: None,
        }));
        let arg_pos_proof = self.verify_builtin_rule_premise(&arg_pos, verify_state)?;
        if arg_pos_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(PowOfLogInverseBuiltinRuleProof {
            proof_of_requirement_facts: vec![base_gt_one, arg_pos_proof],
        }))
    }
}

fn match_union(obj: &Obj) -> Option<&Union> {
    match obj {
        Obj::SetOperator(SetOperator::Union(u)) => Some(u),
        _ => None,
    }
}

fn match_intersect(obj: &Obj) -> Option<&Intersect> {
    match obj {
        Obj::SetOperator(SetOperator::Intersect(i)) => Some(i),
        _ => None,
    }
}

fn match_set_minus(obj: &Obj) -> Option<&SetMinus> {
    match obj {
        Obj::SetOperator(SetOperator::SetMinus(s)) => Some(s),
        _ => None,
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

fn match_finite_set_reduce(obj: &Obj) -> Option<&FiniteSetReduce> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(r)) => Some(r),
        _ => None,
    }
}

fn match_sum_of_finite_set(obj: &Obj) -> Option<&SumOfFiniteSet> {
    match obj {
        Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(s)) => Some(s),
        _ => None,
    }
}

fn match_pow(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base, exponent })) => {
            Some((base.as_ref(), exponent.as_ref()))
        }
        _ => None,
    }
}

fn match_log(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ExpLogOperator(ExpLogOperator::Log(Log { base, arg })) => {
            Some((base.as_ref(), arg.as_ref()))
        }
        _ => None,
    }
}

fn match_finite_set_size(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize { set })) => {
            Some(set.as_ref())
        }
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

fn zero_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }))
}

fn apply_fn_one_arg(f: &Obj, arg: Obj) -> Option<Obj> {
    match f {
        Obj::Identifier(id) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::Identifier(id.clone())),
            body: vec![vec![Box::new(arg)]],
        })),
        Obj::FnObj(existing) => {
            let mut body = existing.body.clone();
            body.push(vec![Box::new(arg)]);
            Some(Obj::FnObj(FnObj {
                head: existing.head.clone(),
                body,
            }))
        }
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(af)) => Some(Obj::FnObj(FnObj {
            head: Box::new(FnObjHead::AnonymousFnLiteral(Box::new(af.clone()))),
            body: vec![vec![Box::new(arg)]],
        })),
        _ => None,
    }
}

fn finite_set_size_set_minus_shape(size_side: &Obj, sub_side: &Obj) -> bool {
    let Some(set_minus_set) = match_finite_set_size(size_side) else {
        return false;
    };
    let Some(sm) = match_set_minus(set_minus_set) else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) = sub_side else {
        return false;
    };
    let Some(first) = match_finite_set_size(left.as_ref()) else {
        return false;
    };
    let Some(inter_set) = match_finite_set_size(right.as_ref()) else {
        return false;
    };
    let Some(inter) = match_intersect(inter_set) else {
        return false;
    };
    sm.left.ir() == first.ir()
        && sm.left.ir() == inter.left.ir()
        && sm.right.ir() == inter.right.ir()
}

fn finite_set_size_union_shape(size_side: &Obj, incl_excl: &Obj) -> bool {
    let Some(union_set) = match_finite_set_size(size_side) else {
        return false;
    };
    let Some(u) = match_union(union_set) else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) = incl_excl else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: a_size,
        right: b_size,
    })) = left.as_ref()
    else {
        return false;
    };
    let Some(a) = match_finite_set_size(a_size.as_ref()) else {
        return false;
    };
    let Some(b) = match_finite_set_size(b_size.as_ref()) else {
        return false;
    };
    let Some(inter_set) = match_finite_set_size(right.as_ref()) else {
        return false;
    };
    let Some(inter) = match_intersect(inter_set) else {
        return false;
    };
    ((u.left.ir() == a.ir() && u.right.ir() == b.ir())
        || (u.left.ir() == b.ir() && u.right.ir() == a.ir()))
        && ((inter.left.ir() == u.left.ir() && inter.right.ir() == u.right.ir())
            || (inter.left.ir() == u.right.ir() && inter.right.ir() == u.left.ir()))
}

fn closed_range_singleton_list_set_shape(range_side: &Obj, list_side: &Obj) -> bool {
    let Obj::SetFormer(SetFormer::ClosedRange(ClosedRange { start, end })) = range_side else {
        return false;
    };
    if start.ir() != end.ir() {
        return false;
    }
    let Obj::SetFormer(SetFormer::ListSet(ListSet { list })) = list_side else {
        return false;
    };
    list.len() == 1 && list[0].ir() == start.ir()
}

fn is_binary_add_anonymous_fn(obj: &Obj) -> bool {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn { body, equal_to })) = obj else {
        return false;
    };
    let mut params = Vec::new();
    for group in &body.set_bound_parameters.groups {
        for p in &group.params {
            params.push(p.clone());
        }
    }
    if params.len() != 2 {
        return false;
    }
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = equal_to.as_ref()
    else {
        return false;
    };
    let (Some(lid), Some(rid)) = (
        identifier_plain_id(left.as_ref()),
        identifier_plain_id(right.as_ref()),
    ) else {
        return false;
    };
    (lid == params[0].id && rid == params[1].id) || (lid == params[1].id && rid == params[0].id)
}

fn identifier_plain_id(obj: &Obj) -> Option<crate::runtime::runtime_ids::IdentifierId> {
    match obj {
        Obj::Identifier(crate::ast::obj::IdentifierObj::Plain { id, .. }) => Some(*id),
        _ => None,
    }
}

fn funcs_match_for_aggregate(left: &Obj, right: &Obj) -> bool {
    if left.ir() == right.ir() {
        return true;
    }
    match (left, right) {
        (
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(l)),
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(r)),
        ) => anonymous_fns_alpha_equal(l, r),
        _ => false,
    }
}

fn reduce_add_zero_equals_sum_shape(reduce_side: &Obj, sum_side: &Obj) -> bool {
    let Some(reduce) = match_reduce(reduce_side) else {
        return false;
    };
    let Some(sum) = match_sum(sum_side) else {
        return false;
    };
    is_zero_obj(reduce.seed.as_ref())
        && is_binary_add_anonymous_fn(reduce.op.as_ref())
        && reduce.start.ir() == sum.start.ir()
        && reduce.end.ir() == sum.end.ir()
        && funcs_match_for_aggregate(reduce.func.as_ref(), sum.func.as_ref())
}

fn finite_set_reduce_add_zero_equals_sum_shape(reduce_side: &Obj, sum_side: &Obj) -> bool {
    let Some(reduce) = match_finite_set_reduce(reduce_side) else {
        return false;
    };
    let Some(sum) = match_sum_of_finite_set(sum_side) else {
        return false;
    };
    is_zero_obj(reduce.seed.as_ref())
        && is_binary_add_anonymous_fn(reduce.op.as_ref())
        && reduce.set.ir() == sum.set.ir()
        && funcs_match_for_aggregate(reduce.func.as_ref(), sum.func.as_ref())
}
