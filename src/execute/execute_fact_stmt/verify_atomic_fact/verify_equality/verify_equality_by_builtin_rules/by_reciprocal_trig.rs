//! Fixed reciprocal_trig equations. Parent equality WD checks both sides and all domain guards.
use super::super::helper::corresponding_arg_pairs;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
impl Runtime {
    pub(super) fn search_reciprocal_trig(
        &mut self,
        fact: &EqualFact,
    ) -> Option<ReciprocalTrigEqualityProof> {
        use ReciprocalTrigEqualityProof as P;
        if matches_equation(fact, sec(num(0)), num(1)) {
            return Some(P::SecZero(SecZeroProof));
        }
        if matches_equation(fact, sec(pi()), neg(num(1))) {
            return Some(P::SecPi(SecPiProof));
        }
        if matches_equation(fact, csc(div_objs(pi(), num(2))), num(1)) {
            return Some(P::CscHalfPi(CscHalfPiProof));
        }
        let mut pending = vec![fact.left.clone(), fact.right.clone()];
        let mut arguments = Vec::new();
        while let Some(obj) = pending.pop() {
            match &obj {
                Obj::TrigOperator(TrigOperator::Sec(v)) => arguments.push(v.arg.as_ref().clone()),
                Obj::TrigOperator(TrigOperator::Csc(v)) => arguments.push(v.arg.as_ref().clone()),
                _ => {}
            }
            if let Some(children) = corresponding_arg_pairs(&obj, &obj) {
                pending.extend(children.into_iter().map(|(child, _)| child));
            }
        }
        for x in arguments {
            if matches_equation(fact, sec(x.clone()), div_objs(num(1), cos(x.clone()))) {
                return Some(P::SecDefinition(SecDefinitionProof));
            }
            if matches_equation(fact, mul_objs(sec(x.clone()), cos(x.clone())), num(1)) {
                return Some(P::SecReciprocal(SecReciprocalProof));
            }
            if matches_equation(
                fact,
                square(sec(x.clone())),
                add_objs(num(1), square(tan(x.clone()))),
            ) {
                return Some(P::SecSquare(SecSquareProof));
            }
            if matches_equation(fact, sec(neg(x.clone())), sec(x.clone())) {
                return Some(P::SecParity(SecParityProof));
            }
            if matches_equation(
                fact,
                sec(add_objs(x.clone(), mul_objs(num(2), pi()))),
                sec(x.clone()),
            ) {
                return Some(P::SecPeriod(SecPeriodProof));
            }
            if matches_equation(fact, sec(add_objs(x.clone(), pi())), neg(sec(x.clone()))) {
                return Some(P::SecHalfTurn(SecHalfTurnProof));
            }
            if matches_equation(fact, csc(x.clone()), div_objs(num(1), sin(x.clone()))) {
                return Some(P::CscDefinition(CscDefinitionProof));
            }
            if matches_equation(fact, mul_objs(csc(x.clone()), sin(x.clone())), num(1)) {
                return Some(P::CscReciprocal(CscReciprocalProof));
            }
            if matches_equation(
                fact,
                square(csc(x.clone())),
                add_objs(num(1), square(cot(x.clone()))),
            ) {
                return Some(P::CscSquare(CscSquareProof));
            }
            if matches_equation(fact, csc(neg(x.clone())), neg(csc(x.clone()))) {
                return Some(P::CscParity(CscParityProof));
            }
            if matches_equation(
                fact,
                csc(add_objs(x.clone(), mul_objs(num(2), pi()))),
                csc(x.clone()),
            ) {
                return Some(P::CscPeriod(CscPeriodProof));
            }
            if matches_equation(fact, csc(add_objs(x.clone(), pi())), neg(csc(x.clone()))) {
                return Some(P::CscHalfTurn(CscHalfTurnProof));
            }
            if matches_equation(
                fact,
                tan(x.clone()),
                mul_objs(sin(x.clone()), sec(x.clone())),
            ) {
                return Some(P::TanThroughSec(TanThroughSecProof));
            }
            if matches_equation(
                fact,
                cot(x.clone()),
                mul_objs(cos(x.clone()), csc(x.clone())),
            ) {
                return Some(P::CotThroughCsc(CotThroughCscProof));
            }
            if matches_equation(
                fact,
                csc(sub_objs(div_objs(pi(), num(2)), x.clone())),
                sec(x.clone()),
            ) {
                return Some(P::CscComplement(CscComplementProof));
            }
        }
        None
    }
}

fn num(n: i32) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.to_string())))
}
fn neg(arg: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(arg) }))
}
fn square(base: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(base),
        exponent: Box::new(num(2)),
    }))
}
// Match the actual checked objects. Algebraic cancellation here could erase
// an unchecked synthetic coth(0), turning 0*coth(0)=cosh(0) into 0=cosh(0).
fn matches_equation(f: &EqualFact, left: Obj, right: Obj) -> bool {
    (f.left.ir() == left.ir() && f.right.ir() == right.ir())
        || (f.right.ir() == left.ir() && f.left.ir() == right.ir())
}
fn sec(arg: Obj) -> Obj {
    Obj::TrigOperator(TrigOperator::Sec(Sec { arg: Box::new(arg) }))
}
fn csc(arg: Obj) -> Obj {
    Obj::TrigOperator(TrigOperator::Csc(Csc { arg: Box::new(arg) }))
}
fn sin(arg: Obj) -> Obj {
    Obj::TrigOperator(TrigOperator::Sin(Sin { arg: Box::new(arg) }))
}
fn cos(arg: Obj) -> Obj {
    Obj::TrigOperator(TrigOperator::Cos(Cos { arg: Box::new(arg) }))
}
fn tan(arg: Obj) -> Obj {
    Obj::TrigOperator(TrigOperator::Tan(Tan { arg: Box::new(arg) }))
}
fn cot(arg: Obj) -> Obj {
    Obj::TrigOperator(TrigOperator::Cot(Cot { arg: Box::new(arg) }))
}
fn pi() -> Obj {
    Obj::Literal(Literal::Pi(Pi))
}

pub enum ReciprocalTrigEqualityProof {
    SecZero(SecZeroProof),
    SecPi(SecPiProof),
    CscHalfPi(CscHalfPiProof),

    SecDefinition(SecDefinitionProof),
    SecReciprocal(SecReciprocalProof),
    SecSquare(SecSquareProof),
    SecParity(SecParityProof),
    SecPeriod(SecPeriodProof),
    SecHalfTurn(SecHalfTurnProof),
    CscDefinition(CscDefinitionProof),
    CscReciprocal(CscReciprocalProof),
    CscSquare(CscSquareProof),
    CscParity(CscParityProof),
    CscPeriod(CscPeriodProof),
    CscHalfTurn(CscHalfTurnProof),
    TanThroughSec(TanThroughSecProof),
    CotThroughCsc(CotThroughCscProof),
    CscComplement(CscComplementProof),
}
pub struct SecDefinitionProof;
pub struct SecReciprocalProof;
pub struct SecSquareProof;
pub struct SecParityProof;
pub struct SecPeriodProof;
pub struct SecHalfTurnProof;
pub struct CscDefinitionProof;
pub struct CscReciprocalProof;
pub struct CscSquareProof;
pub struct CscParityProof;
pub struct CscPeriodProof;
pub struct CscHalfTurnProof;
pub struct TanThroughSecProof;
pub struct CotThroughCscProof;
pub struct CscComplementProof;
impl ReciprocalTrigEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SecZero(_) => "SecZero",
            Self::SecPi(_) => "SecPi",
            Self::CscHalfPi(_) => "CscHalfPi",

            Self::SecDefinition(_) => "SecDefinition",
            Self::SecReciprocal(_) => "SecReciprocal",
            Self::SecSquare(_) => "SecSquare",
            Self::SecParity(_) => "SecParity",
            Self::SecPeriod(_) => "SecPeriod",
            Self::SecHalfTurn(_) => "SecHalfTurn",
            Self::CscDefinition(_) => "CscDefinition",
            Self::CscReciprocal(_) => "CscReciprocal",
            Self::CscSquare(_) => "CscSquare",
            Self::CscParity(_) => "CscParity",
            Self::CscPeriod(_) => "CscPeriod",
            Self::CscHalfTurn(_) => "CscHalfTurn",
            Self::TanThroughSec(_) => "TanThroughSec",
            Self::CotThroughCsc(_) => "CotThroughCsc",
            Self::CscComplement(_) => "CscComplement",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::SecZero(_) => "sec(0)=1",
            Self::SecPi(_) => "sec(pi)=-1",
            Self::CscHalfPi(_) => "csc(pi/2)=1",

            Self::SecDefinition(_) => "sec(x)=1/cos(x)",
            Self::SecReciprocal(_) => "sec(x)*cos(x)=1",
            Self::SecSquare(_) => "sec(x)^2=1+tan(x)^2",
            Self::SecParity(_) => "sec(-x)=sec(x)",
            Self::SecPeriod(_) => "sec(x+2*pi)=sec(x)",
            Self::SecHalfTurn(_) => "sec(x+pi)=-sec(x)",
            Self::CscDefinition(_) => "csc(x)=1/sin(x)",
            Self::CscReciprocal(_) => "csc(x)*sin(x)=1",
            Self::CscSquare(_) => "csc(x)^2=1+cot(x)^2",
            Self::CscParity(_) => "csc(-x)=-csc(x)",
            Self::CscPeriod(_) => "csc(x+2*pi)=csc(x)",
            Self::CscHalfTurn(_) => "csc(x+pi)=-csc(x)",
            Self::TanThroughSec(_) => "tan(x)=sin(x)*sec(x)",
            Self::CotThroughCsc(_) => "cot(x)=cos(x)*csc(x)",
            Self::CscComplement(_) => "csc(pi/2-x)=sec(x)",
        }
    }
}

pub struct SecZeroProof;
pub struct SecPiProof;
pub struct CscHalfPiProof;
