//! Stage B wave 9: set algebra / empty-set / power-set cardinality equalities.
//!
//! One matcher ↔ one dedicated proof struct.

use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, IsFiniteSetFact, NotIsNonemptySetFact, SubsetFact,
};
use crate::ast::obj::{
    ArithmeticOperator, FiniteSetSize, FiniteSetStat, ListSet, Literal, Number, Obj, Pow, PowerSet,
    SetFormer, SetMinus, SetOperator, Union, Intersect,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin UnionEmptyRight: union(A, {}) = A.
// Example: have A set; union(A, {}) = A.
pub struct UnionEmptyRightBuiltinRuleProof {}

// Builtin UnionEmptyLeft: union({}, A) = A.
// Example: have A set; union({}, A) = A.
pub struct UnionEmptyLeftBuiltinRuleProof {}

// Builtin IntersectEmptyRight: intersect(A, {}) = {}.
// Example: have A set; intersect(A, {}) = {}.
pub struct IntersectEmptyRightBuiltinRuleProof {}

// Builtin IntersectEmptyLeft: intersect({}, A) = {}.
// Example: have A set; intersect({}, A) = {}.
pub struct IntersectEmptyLeftBuiltinRuleProof {}

// Builtin SetMinusSelfEmpty: set_minus(A, A) = {}.
// Example: have A set; set_minus(A, A) = {}.
pub struct SetMinusSelfEmptyBuiltinRuleProof {}

// Builtin SetMinusEmptyRight: set_minus(A, {}) = A.
// Example: have A set; set_minus(A, {}) = A.
pub struct SetMinusEmptyRightBuiltinRuleProof {}

// Builtin SetMinusEmptyLeft: set_minus({}, A) = {}.
// Example: have A set; set_minus({}, A) = {}.
pub struct SetMinusEmptyLeftBuiltinRuleProof {}

// Builtin UnionCommutative: union(A, B) = union(B, A).
// Example: have A set; have B set; union(A, B) = union(B, A).
pub struct UnionCommutativeBuiltinRuleProof {}

// Builtin IntersectCommutative: intersect(A, B) = intersect(B, A).
// Example: have A set; have B set; intersect(A, B) = intersect(B, A).
pub struct IntersectCommutativeBuiltinRuleProof {}

// Builtin UnionIdempotent: union(A, A) = A.
// Example: have A set; union(A, A) = A.
pub struct UnionIdempotentBuiltinRuleProof {}

// Builtin IntersectIdempotent: intersect(A, A) = A.
// Example: have A set; intersect(A, A) = A.
pub struct IntersectIdempotentBuiltinRuleProof {}

// Builtin IntersectFromSubset: B ⊆ A ⇒ intersect(A, B) = B (either operand order).
// Example: have A set; have B set; trust B $subset A; intersect(A, B) = B.
pub struct IntersectFromSubsetBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin EmptySetFromNotNonempty: not $is_nonempty_set(A) ⇒ A = {}.
// Example: have A set; trust not $is_nonempty_set(A); A = {}.
pub struct EmptySetFromNotNonemptyBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Builtin PowerSetFiniteSetSize:
//   $is_finite_set(S) ⇒ finite_set_size(power_set(S)) = 2^finite_set_size(S).
// Example: have S finite_set; finite_set_size(power_set(S)) = 2^finite_set_size(S).
pub struct PowerSetFiniteSetSizeBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}


// Builtin UnionAssociative: union(union(A, B), C) = union(A, union(B, C)).
// Example: have A, B, C set; union(union(A, B), C) = union(A, union(B, C)).
pub struct UnionAssociativeBuiltinRuleProof {}

// Builtin IntersectAssociative: intersect(intersect(A, B), C) = intersect(A, intersect(B, C)).
// Example: have A, B, C set; intersect(intersect(A, B), C) = intersect(A, intersect(B, C)).
pub struct IntersectAssociativeBuiltinRuleProof {}

// Builtin IntersectUnionDistributive:
//   intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C)).
// Example: have A, B, C set; intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C)).
pub struct IntersectUnionDistributiveBuiltinRuleProof {}

// Builtin SetMinusUnionDeMorgan:
//   set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C)).
// Example: have A, B, C set; set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C)).
pub struct SetMinusUnionDeMorganBuiltinRuleProof {}

// Builtin SetMinusIntersectDeMorgan:
//   set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C)).
// Example: have A, B, C set; set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C)).
pub struct SetMinusIntersectDeMorganBuiltinRuleProof {}

// Builtin IntersectSetMinusSelfEmpty: intersect(A, set_minus(B, A)) = {}.
// Example: have A set; have B set; intersect(A, set_minus(B, A)) = {}.
pub struct IntersectSetMinusSelfEmptyBuiltinRuleProof {}

pub enum EqualityIdentitiesWave9BuiltinRuleProof {
    UnionEmptyRight(UnionEmptyRightBuiltinRuleProof),
    UnionEmptyLeft(UnionEmptyLeftBuiltinRuleProof),
    IntersectEmptyRight(IntersectEmptyRightBuiltinRuleProof),
    IntersectEmptyLeft(IntersectEmptyLeftBuiltinRuleProof),
    SetMinusSelfEmpty(SetMinusSelfEmptyBuiltinRuleProof),
    SetMinusEmptyRight(SetMinusEmptyRightBuiltinRuleProof),
    SetMinusEmptyLeft(SetMinusEmptyLeftBuiltinRuleProof),
    UnionCommutative(UnionCommutativeBuiltinRuleProof),
    IntersectCommutative(IntersectCommutativeBuiltinRuleProof),
    UnionIdempotent(UnionIdempotentBuiltinRuleProof),
    IntersectIdempotent(IntersectIdempotentBuiltinRuleProof),
    IntersectFromSubset(IntersectFromSubsetBuiltinRuleProof),
    EmptySetFromNotNonempty(EmptySetFromNotNonemptyBuiltinRuleProof),
    PowerSetFiniteSetSize(PowerSetFiniteSetSizeBuiltinRuleProof),
    UnionAssociative(UnionAssociativeBuiltinRuleProof),
    IntersectAssociative(IntersectAssociativeBuiltinRuleProof),
    IntersectUnionDistributive(IntersectUnionDistributiveBuiltinRuleProof),
    SetMinusUnionDeMorgan(SetMinusUnionDeMorganBuiltinRuleProof),
    SetMinusIntersectDeMorgan(SetMinusIntersectDeMorganBuiltinRuleProof),
    IntersectSetMinusSelfEmpty(IntersectSetMinusSelfEmptyBuiltinRuleProof),
}

impl Runtime {
    pub fn search_equal_fact_builtin_rule_equality_identities_wave9(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualityIdentitiesWave9BuiltinRuleProof>> {
        let child = verify_state;
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            if union_empty_right_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave9BuiltinRuleProof::UnionEmptyRight(
                    UnionEmptyRightBuiltinRuleProof {},
                )));
            }
            if union_empty_left_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave9BuiltinRuleProof::UnionEmptyLeft(
                    UnionEmptyLeftBuiltinRuleProof {},
                )));
            }
            if intersect_empty_right_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::IntersectEmptyRight(
                        IntersectEmptyRightBuiltinRuleProof {},
                    ),
                ));
            }
            if intersect_empty_left_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::IntersectEmptyLeft(
                        IntersectEmptyLeftBuiltinRuleProof {},
                    ),
                ));
            }
            if set_minus_self_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::SetMinusSelfEmpty(
                        SetMinusSelfEmptyBuiltinRuleProof {},
                    ),
                ));
            }
            if set_minus_empty_right_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::SetMinusEmptyRight(
                        SetMinusEmptyRightBuiltinRuleProof {},
                    ),
                ));
            }
            if set_minus_empty_left_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::SetMinusEmptyLeft(
                        SetMinusEmptyLeftBuiltinRuleProof {},
                    ),
                ));
            }
            if union_commutative_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave9BuiltinRuleProof::UnionCommutative(
                    UnionCommutativeBuiltinRuleProof {},
                )));
            }
            if intersect_commutative_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::IntersectCommutative(
                        IntersectCommutativeBuiltinRuleProof {},
                    ),
                ));
            }
            if union_idempotent_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave9BuiltinRuleProof::UnionIdempotent(
                    UnionIdempotentBuiltinRuleProof {},
                )));
            }
            if intersect_idempotent_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::IntersectIdempotent(
                        IntersectIdempotentBuiltinRuleProof {},
                    ),
                ));
            }
            if union_associative_shape(left, right) {
                return Ok(Some(EqualityIdentitiesWave9BuiltinRuleProof::UnionAssociative(
                    UnionAssociativeBuiltinRuleProof {},
                )));
            }
            if intersect_associative_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::IntersectAssociative(
                        IntersectAssociativeBuiltinRuleProof {},
                    ),
                ));
            }
            if intersect_union_distributive_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::IntersectUnionDistributive(
                        IntersectUnionDistributiveBuiltinRuleProof {},
                    ),
                ));
            }
            if set_minus_union_de_morgan_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::SetMinusUnionDeMorgan(
                        SetMinusUnionDeMorganBuiltinRuleProof {},
                    ),
                ));
            }
            if set_minus_intersect_de_morgan_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::SetMinusIntersectDeMorgan(
                        SetMinusIntersectDeMorganBuiltinRuleProof {},
                    ),
                ));
            }
            if intersect_set_minus_self_empty_shape(left, right) {
                return Ok(Some(
                    EqualityIdentitiesWave9BuiltinRuleProof::IntersectSetMinusSelfEmpty(
                        IntersectSetMinusSelfEmptyBuiltinRuleProof {},
                    ),
                ));
            }

            if let Some(base) = power_set_finite_set_size_shape(left, right) {
                let premise = Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: base,
                    line_file: None,
                }));
                let proof = self.verify_builtin_rule_premise(&premise, child.clone())?;
                if !proof.is_failed() {
                    return Ok(Some(
                        EqualityIdentitiesWave9BuiltinRuleProof::PowerSetFiniteSetSize(
                            PowerSetFiniteSetSizeBuiltinRuleProof {
                                proof_of_requirement_facts: vec![proof],
                            },
                        ),
                    ));
                }
            }
        }
        if let Some(p) = self.try_intersect_from_subset(fact, child.clone())? {
            return Ok(Some(EqualityIdentitiesWave9BuiltinRuleProof::IntersectFromSubset(
                p,
            )));
        }
        if let Some(p) = self.try_empty_set_from_not_nonempty(fact, child)? {
            return Ok(Some(
                EqualityIdentitiesWave9BuiltinRuleProof::EmptySetFromNotNonempty(p),
            ));
        }
        Ok(None)
    }

    fn try_intersect_from_subset(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<IntersectFromSubsetBuiltinRuleProof>> {
        for (intersection_side, target_side) in [
            (&fact.left, &fact.right),
            (&fact.right, &fact.left),
        ] {
            let Some(intersect) = match_intersect(intersection_side) else {
                continue;
            };
            let (subset, superset) = if target_side.ir() == intersect.right.ir() {
                (intersect.right.as_ref(), intersect.left.as_ref())
            } else if target_side.ir() == intersect.left.ir() {
                (intersect.left.as_ref(), intersect.right.as_ref())
            } else {
                continue;
            };
            let premise = Fact::AtomicFact(AtomicFact::SubsetFact(SubsetFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: subset.clone(),
                right: superset.clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
            if proof.is_failed() {
                continue;
            }
            return Ok(Some(IntersectFromSubsetBuiltinRuleProof {
                proof_of_requirement_facts: vec![proof],
            }));
        }
        Ok(None)
    }

    fn try_empty_set_from_not_nonempty(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EmptySetFromNotNonemptyBuiltinRuleProof>> {
        let set = match (&fact.left, &fact.right) {
            (left, right) if is_empty_list_set(left) => right,
            (left, right) if is_empty_list_set(right) => left,
            _ => return Ok(None),
        };
        let premise = Fact::AtomicFact(AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: set.clone(),
            line_file: None,
        }));
        let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(EmptySetFromNotNonemptyBuiltinRuleProof {
            proof_of_requirement_facts: vec![proof],
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

fn is_empty_list_set(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::SetFormer(SetFormer::ListSet(ListSet { list, .. })) if list.is_empty()
    )
}

fn is_two_obj(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number { normalized_value })) if normalized_value == "2"
    )
}

fn union_empty_right_shape(union_side: &Obj, retained: &Obj) -> bool {
    let Some(u) = match_union(union_side) else {
        return false;
    };
    is_empty_list_set(u.right.as_ref()) && u.left.ir() == retained.ir()
}

fn union_empty_left_shape(union_side: &Obj, retained: &Obj) -> bool {
    let Some(u) = match_union(union_side) else {
        return false;
    };
    is_empty_list_set(u.left.as_ref()) && u.right.ir() == retained.ir()
}

fn intersect_empty_right_shape(intersect_side: &Obj, empty_side: &Obj) -> bool {
    let Some(i) = match_intersect(intersect_side) else {
        return false;
    };
    is_empty_list_set(i.right.as_ref()) && is_empty_list_set(empty_side)
}

fn intersect_empty_left_shape(intersect_side: &Obj, empty_side: &Obj) -> bool {
    let Some(i) = match_intersect(intersect_side) else {
        return false;
    };
    is_empty_list_set(i.left.as_ref()) && is_empty_list_set(empty_side)
}

fn set_minus_self_empty_shape(diff_side: &Obj, empty_side: &Obj) -> bool {
    let Some(s) = match_set_minus(diff_side) else {
        return false;
    };
    s.left.ir() == s.right.ir() && is_empty_list_set(empty_side)
}

fn set_minus_empty_right_shape(diff_side: &Obj, retained: &Obj) -> bool {
    let Some(s) = match_set_minus(diff_side) else {
        return false;
    };
    is_empty_list_set(s.right.as_ref()) && s.left.ir() == retained.ir()
}

fn set_minus_empty_left_shape(diff_side: &Obj, empty_side: &Obj) -> bool {
    let Some(s) = match_set_minus(diff_side) else {
        return false;
    };
    is_empty_list_set(s.left.as_ref()) && is_empty_list_set(empty_side)
}

fn union_commutative_shape(left: &Obj, right: &Obj) -> bool {
    let Some(l) = match_union(left) else {
        return false;
    };
    let Some(r) = match_union(right) else {
        return false;
    };
    l.left.ir() == r.right.ir() && l.right.ir() == r.left.ir()
}

fn intersect_commutative_shape(left: &Obj, right: &Obj) -> bool {
    let Some(l) = match_intersect(left) else {
        return false;
    };
    let Some(r) = match_intersect(right) else {
        return false;
    };
    l.left.ir() == r.right.ir() && l.right.ir() == r.left.ir()
}

fn union_idempotent_shape(union_side: &Obj, retained: &Obj) -> bool {
    let Some(u) = match_union(union_side) else {
        return false;
    };
    u.left.ir() == u.right.ir() && u.left.ir() == retained.ir()
}

fn intersect_idempotent_shape(intersect_side: &Obj, retained: &Obj) -> bool {
    let Some(i) = match_intersect(intersect_side) else {
        return false;
    };
    i.left.ir() == i.right.ir() && i.left.ir() == retained.ir()
}

fn power_set_finite_set_size_shape(size_side: &Obj, pow_side: &Obj) -> Option<Obj> {
    let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize { set })) = size_side else {
        return None;
    };
    let Obj::SetOperator(SetOperator::PowerSet(PowerSet { set: base })) = set.as_ref() else {
        return None;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow { base: two, exponent })) = pow_side
    else {
        return None;
    };
    if !is_two_obj(two.as_ref()) {
        return None;
    }
    let Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize { set: base_size })) =
        exponent.as_ref()
    else {
        return None;
    };
    if base.ir() == base_size.ir() {
        Some(base.as_ref().clone())
    } else {
        None
    }
}

fn union_associative_shape(left: &Obj, right: &Obj) -> bool {
    let Some(left_outer) = match_union(left) else { return false; };
    let Some(left_inner) = match_union(left_outer.left.as_ref()) else { return false; };
    let Some(right_outer) = match_union(right) else { return false; };
    let Some(right_inner) = match_union(right_outer.right.as_ref()) else { return false; };
    left_inner.left.ir() == right_outer.left.ir()
        && left_inner.right.ir() == right_inner.left.ir()
        && left_outer.right.ir() == right_inner.right.ir()
}

fn intersect_associative_shape(left: &Obj, right: &Obj) -> bool {
    let Some(left_outer) = match_intersect(left) else { return false; };
    let Some(left_inner) = match_intersect(left_outer.left.as_ref()) else { return false; };
    let Some(right_outer) = match_intersect(right) else { return false; };
    let Some(right_inner) = match_intersect(right_outer.right.as_ref()) else { return false; };
    left_inner.left.ir() == right_outer.left.ir()
        && left_inner.right.ir() == right_inner.left.ir()
        && left_outer.right.ir() == right_inner.right.ir()
}

fn intersect_union_distributive_shape(left: &Obj, right: &Obj) -> bool {
    let Some(intersect) = match_intersect(left) else { return false; };
    let Some(union) = match_union(intersect.right.as_ref()) else { return false; };
    let Some(right_union) = match_union(right) else { return false; };
    let Some(left_i) = match_intersect(right_union.left.as_ref()) else { return false; };
    let Some(right_i) = match_intersect(right_union.right.as_ref()) else { return false; };
    let a = intersect.left.as_ref();
    a.ir() == left_i.left.ir()
        && a.ir() == right_i.left.ir()
        && union.left.ir() == left_i.right.ir()
        && union.right.ir() == right_i.right.ir()
}

fn set_minus_union_de_morgan_shape(left: &Obj, right: &Obj) -> bool {
    let Some(diff) = match_set_minus(left) else { return false; };
    let Some(removed_union) = match_union(diff.right.as_ref()) else { return false; };
    let Some(inter) = match_intersect(right) else { return false; };
    let Some(left_diff) = match_set_minus(inter.left.as_ref()) else { return false; };
    let Some(right_diff) = match_set_minus(inter.right.as_ref()) else { return false; };
    let a = diff.left.as_ref();
    a.ir() == left_diff.left.ir()
        && a.ir() == right_diff.left.ir()
        && removed_union.left.ir() == left_diff.right.ir()
        && removed_union.right.ir() == right_diff.right.ir()
}

fn set_minus_intersect_de_morgan_shape(left: &Obj, right: &Obj) -> bool {
    let Some(diff) = match_set_minus(left) else { return false; };
    let Some(removed_inter) = match_intersect(diff.right.as_ref()) else { return false; };
    let Some(u) = match_union(right) else { return false; };
    let Some(left_diff) = match_set_minus(u.left.as_ref()) else { return false; };
    let Some(right_diff) = match_set_minus(u.right.as_ref()) else { return false; };
    let a = diff.left.as_ref();
    a.ir() == left_diff.left.ir()
        && a.ir() == right_diff.left.ir()
        && removed_inter.left.ir() == left_diff.right.ir()
        && removed_inter.right.ir() == right_diff.right.ir()
}

fn intersect_set_minus_self_empty_shape(intersect_side: &Obj, empty_side: &Obj) -> bool {
    let Some(i) = match_intersect(intersect_side) else { return false; };
    if !is_empty_list_set(empty_side) {
        return false;
    }
    for (plain, difference) in [
        (i.left.as_ref(), i.right.as_ref()),
        (i.right.as_ref(), i.left.as_ref()),
    ] {
        let Some(diff) = match_set_minus(difference) else { continue; };
        if plain.ir() == diff.right.ir() {
            return true;
        }
    }
    false
}
