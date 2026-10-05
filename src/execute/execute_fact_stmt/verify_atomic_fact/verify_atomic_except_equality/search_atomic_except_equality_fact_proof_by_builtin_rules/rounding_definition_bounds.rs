//! The four defining bounds for real floor and ceiling, after parent WD.
use super::less::LessFactSearchProofByBuiltinRule;
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::ast::fact::{LessEqualFact, LessFact};
use crate::ast::obj::{ArithmeticOperator, Literal, Obj};

pub struct FloorLowerBoundProof {}
impl FloorLowerBoundProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct FloorStrictUpperBoundProof {}
impl FloorStrictUpperBoundProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct CeilStrictLowerBoundProof {}
impl CeilStrictLowerBoundProof {
    pub fn new() -> Self {
        Self {}
    }
}
pub struct CeilUpperBoundProof {}
impl CeilUpperBoundProof {
    pub fn new() -> Self {
        Self {}
    }
}

pub(super) fn rounding_weak_bound(
    fact: &LessEqualFact,
) -> Option<LessEqualFactSearchProofByBuiltinRule> {
    if let Obj::ArithmeticOperator(ArithmeticOperator::Floor(floor)) = &fact.left {
        if floor.arg.ir() == fact.right.ir() {
            return Some(LessEqualFactSearchProofByBuiltinRule::FloorLowerBound(
                FloorLowerBoundProof::new(),
            ));
        }
    }
    if let Obj::ArithmeticOperator(ArithmeticOperator::Ceil(ceil)) = &fact.right {
        if ceil.arg.ir() == fact.left.ir() {
            return Some(LessEqualFactSearchProofByBuiltinRule::CeilUpperBound(
                CeilUpperBoundProof::new(),
            ));
        }
    }
    None
}

pub(super) fn rounding_strict_bound(fact: &LessFact) -> Option<LessFactSearchProofByBuiltinRule> {
    if let Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) = &fact.right {
        if is_one(&add.right) {
            if let Obj::ArithmeticOperator(ArithmeticOperator::Floor(floor)) = &*add.left {
                if floor.arg.ir() == fact.left.ir() {
                    return Some(LessFactSearchProofByBuiltinRule::FloorStrictUpperBound(
                        FloorStrictUpperBoundProof::new(),
                    ));
                }
            }
        }
    }
    if let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) = &fact.left {
        if is_one(&sub.right) {
            if let Obj::ArithmeticOperator(ArithmeticOperator::Ceil(ceil)) = &*sub.left {
                if ceil.arg.ir() == fact.right.ir() {
                    return Some(LessFactSearchProofByBuiltinRule::CeilStrictLowerBound(
                        CeilStrictLowerBoundProof::new(),
                    ));
                }
            }
        }
    }
    None
}

fn is_one(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::Number(n)) if n.normalized_value == "1")
}
