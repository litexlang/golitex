use crate::prelude::*;

/// Short-lived target choice used while a checked arithmetic Result is
/// rendered. This is compiler control data, not another proof IR.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LeanArithmeticBuiltinCompilationKind {
    AddNonnegative,
    AddPositive,
    AddPositiveLeftStrict,
    AddPositiveRightStrict,
    MulNonnegative,
    MulPositive,
    DivNonnegative,
    DivPositive,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LeanSetBuiltinCompilationKind {
    EmptySubset,
    UnionCommutative,
    UnionAssociative,
    UnionIdempotent,
    UnionEmptyIdentity,
    IntersectCommutative,
    IntersectAssociative,
    UnionMembershipLeft,
    UnionMembershipRight,
    IntersectMembershipBoth,
    SetMinusMembership,
    IntersectEqLeftOfSubset,
    IntersectEqRightOfSubset,
    IntersectFinite,
    IntersectSubsetLeft,
    IntersectSubsetRight,
    IntersectUnionDistributive,
    PowerSetFinite,
    PowerSetMembershipOfSubset,
    PowerSetNonempty,
    SetMinusFiniteLeft,
    SetMinusIntersectDeMorgan,
    SetMinusRecoverSubset,
    SetMinusSubsetLeft,
    SetMinusUnionDeMorgan,
    SubsetEqSetMinusRecovery,
    SubsetUnionLeft,
    SubsetUnionRight,
    UnionFinite,
    UnionNonemptyLeft,
    UnionNonemptyRight,
    UnionSubset,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum LeanEqualityApplicationSide {
    Left,
    Right,
}

/// Exact local FactId/proposition pair visible in one compiler environment.
#[derive(Clone, Debug)]
pub(super) struct LeanLocalFactPremise {
    pub(super) fact_id: FactId,
    pub(super) fact: Fact,
}

impl LeanLocalFactPremise {
    pub(super) fn new(fact_id: FactId, fact: Fact) -> Self {
        Self { fact_id, fact }
    }
}

pub(super) fn facts_are_comparison_notation_duals(source: &Fact, target: &Fact) -> bool {
    let (Fact::AtomicFact(source), Fact::AtomicFact(target)) = (source, target) else {
        return false;
    };
    let swapped = |source_left: &Obj, source_right: &Obj, target_left: &Obj, target_right: &Obj| {
        obj_equality_key(source_left) == obj_equality_key(target_right)
            && obj_equality_key(source_right) == obj_equality_key(target_left)
    };
    match (source, target) {
        (AtomicFact::LessFact(source), AtomicFact::GreaterFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::GreaterFact(source), AtomicFact::LessFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::LessEqualFact(source), AtomicFact::GreaterEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::GreaterEqualFact(source), AtomicFact::LessEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotLessFact(source), AtomicFact::NotGreaterFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotGreaterFact(source), AtomicFact::NotLessFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotLessEqualFact(source), AtomicFact::NotGreaterEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        (AtomicFact::NotGreaterEqualFact(source), AtomicFact::NotLessEqualFact(target)) => {
            swapped(&source.left, &source.right, &target.left, &target.right)
        }
        _ => false,
    }
}

pub(super) fn fact_is_closed_numeric_relation(goal: &Fact) -> bool {
    let Fact::AtomicFact(atomic) = goal else {
        return false;
    };
    match atomic {
        AtomicFact::EqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::NotEqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::LessFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::GreaterFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::LessEqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::GreaterEqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::NotLessFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::NotGreaterFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::NotLessEqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        AtomicFact::NotGreaterEqualFact(fact) => {
            object_is_closed_rational_expression(&fact.left)
                && object_is_closed_rational_expression(&fact.right)
        }
        _ => false,
    }
}

fn object_is_closed_rational_expression(object: &Obj) -> bool {
    match object {
        Obj::Number(_) => true,
        Obj::Add(value) => {
            object_is_closed_rational_expression(value.left.as_ref())
                && object_is_closed_rational_expression(value.right.as_ref())
        }
        Obj::Sub(value) => {
            object_is_closed_rational_expression(value.left.as_ref())
                && object_is_closed_rational_expression(value.right.as_ref())
        }
        Obj::Mul(value) => {
            object_is_closed_rational_expression(value.left.as_ref())
                && object_is_closed_rational_expression(value.right.as_ref())
        }
        Obj::Div(value) => {
            object_is_closed_rational_expression(value.left.as_ref())
                && object_is_closed_rational_expression(value.right.as_ref())
        }
        _ => false,
    }
}
