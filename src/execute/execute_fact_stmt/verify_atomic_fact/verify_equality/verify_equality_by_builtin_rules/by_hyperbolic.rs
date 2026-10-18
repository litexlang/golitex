//! Fixed hyperbolic equations. Parent equality WD checks both sides and all domain guards.
use super::super::helper::corresponding_arg_pairs;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
impl Runtime {
    pub(super) fn search_hyperbolic(
        &mut self,
        fact: &EqualFact,
    ) -> Option<HyperbolicEqualityProof> {
        use HyperbolicEqualityProof as P;
        let mut pending = vec![fact.left.clone(), fact.right.clone()];
        let mut arguments = Vec::new();
        while let Some(obj) = pending.pop() {
            match &obj {
                Obj::HyperbolicOperator(HyperbolicOperator::Sinh(v)) => {
                    arguments.push(v.arg.as_ref().clone())
                }
                Obj::HyperbolicOperator(HyperbolicOperator::Cosh(v)) => {
                    arguments.push(v.arg.as_ref().clone())
                }
                Obj::HyperbolicOperator(HyperbolicOperator::Tanh(v)) => {
                    arguments.push(v.arg.as_ref().clone())
                }
                Obj::HyperbolicOperator(HyperbolicOperator::Coth(v)) => {
                    arguments.push(v.arg.as_ref().clone())
                }
                Obj::HyperbolicOperator(HyperbolicOperator::Sech(v)) => {
                    arguments.push(v.arg.as_ref().clone())
                }
                Obj::HyperbolicOperator(HyperbolicOperator::Csch(v)) => {
                    arguments.push(v.arg.as_ref().clone())
                }
                _ => {}
            }
            if let Some(children) = corresponding_arg_pairs(&obj, &obj) {
                pending.extend(children.into_iter().map(|(child, _)| child));
            }
        }
        for x in arguments {
            if matches_equation(
                fact,
                sinh(x.clone()),
                div_objs(sub_objs(exp(x.clone()), exp(neg(x.clone()))), num(2)),
            ) {
                return Some(P::SinhDefinition(SinhDefinitionProof));
            }
            if matches_equation(
                fact,
                cosh(x.clone()),
                div_objs(add_objs(exp(x.clone()), exp(neg(x.clone()))), num(2)),
            ) {
                return Some(P::CoshDefinition(CoshDefinitionProof));
            }
            if matches_equation(
                fact,
                tanh(x.clone()),
                div_objs(sinh(x.clone()), cosh(x.clone())),
            ) {
                return Some(P::TanhDefinition(TanhDefinitionProof));
            }
            if matches_equation(
                fact,
                mul_objs(tanh(x.clone()), cosh(x.clone())),
                sinh(x.clone()),
            ) {
                return Some(P::TanhReciprocal(TanhReciprocalProof));
            }
            if matches_equation(
                fact,
                coth(x.clone()),
                div_objs(cosh(x.clone()), sinh(x.clone())),
            ) {
                return Some(P::CothDefinition(CothDefinitionProof));
            }
            if matches_equation(
                fact,
                mul_objs(coth(x.clone()), sinh(x.clone())),
                cosh(x.clone()),
            ) {
                return Some(P::CothReciprocal(CothReciprocalProof));
            }
            if matches_equation(fact, sech(x.clone()), div_objs(num(1), cosh(x.clone()))) {
                return Some(P::SechDefinition(SechDefinitionProof));
            }
            if matches_equation(fact, mul_objs(sech(x.clone()), cosh(x.clone())), num(1)) {
                return Some(P::SechReciprocal(SechReciprocalProof));
            }
            if matches_equation(fact, csch(x.clone()), div_objs(num(1), sinh(x.clone()))) {
                return Some(P::CschDefinition(CschDefinitionProof));
            }
            if matches_equation(fact, mul_objs(csch(x.clone()), sinh(x.clone())), num(1)) {
                return Some(P::CschReciprocal(CschReciprocalProof));
            }
            if matches_equation(fact, sinh(neg(x.clone())), neg(sinh(x.clone()))) {
                return Some(P::SinhParity(SinhParityProof));
            }
            if matches_equation(fact, cosh(neg(x.clone())), cosh(x.clone())) {
                return Some(P::CoshParity(CoshParityProof));
            }
            if matches_equation(fact, tanh(neg(x.clone())), neg(tanh(x.clone()))) {
                return Some(P::TanhParity(TanhParityProof));
            }
            if matches_equation(fact, coth(neg(x.clone())), neg(coth(x.clone()))) {
                return Some(P::CothParity(CothParityProof));
            }
            if matches_equation(fact, sech(neg(x.clone())), sech(x.clone())) {
                return Some(P::SechParity(SechParityProof));
            }
            if matches_equation(fact, csch(neg(x.clone())), neg(csch(x.clone()))) {
                return Some(P::CschParity(CschParityProof));
            }
            if matches_equation(
                fact,
                sub_objs(square(cosh(x.clone())), square(sinh(x.clone()))),
                num(1),
            ) {
                return Some(P::HyperbolicPythagorean(HyperbolicPythagoreanProof));
            }
            if matches_equation(
                fact,
                exp(x.clone()),
                add_objs(cosh(x.clone()), sinh(x.clone())),
            ) {
                return Some(P::ExpThroughHyperbolic(ExpThroughHyperbolicProof));
            }
            if matches_equation(
                fact,
                exp(neg(x.clone())),
                sub_objs(cosh(x.clone()), sinh(x.clone())),
            ) {
                return Some(P::ExpNegativeThroughHyperbolic(
                    ExpNegativeThroughHyperbolicProof,
                ));
            }
            if matches_equation(
                fact,
                sub_objs(num(1), square(tanh(x.clone()))),
                square(sech(x.clone())),
            ) {
                return Some(P::TanhSechSquare(TanhSechSquareProof));
            }
            if matches_equation(
                fact,
                sub_objs(square(coth(x.clone())), num(1)),
                square(csch(x.clone())),
            ) {
                return Some(P::CothCschSquare(CothCschSquareProof));
            }
            if matches_equation(fact, mul_objs(tanh(x.clone()), coth(x.clone())), num(1)) {
                return Some(P::TanhCothProduct(TanhCothProductProof));
            }
            if matches_equation(
                fact,
                tanh(x.clone()),
                mul_objs(sinh(x.clone()), sech(x.clone())),
            ) {
                return Some(P::TanhThroughSech(TanhThroughSechProof));
            }
            if matches_equation(
                fact,
                coth(x.clone()),
                mul_objs(cosh(x.clone()), csch(x.clone())),
            ) {
                return Some(P::CothThroughCsch(CothThroughCschProof));
            }
            if matches_equation(
                fact,
                sinh(mul_objs(num(2), x.clone())),
                mul_objs(mul_objs(num(2), sinh(x.clone())), cosh(x.clone())),
            ) {
                return Some(P::SinhDoubleAngle(SinhDoubleAngleProof));
            }
            if matches_equation(
                fact,
                cosh(mul_objs(num(2), x.clone())),
                add_objs(square(cosh(x.clone())), square(sinh(x.clone()))),
            ) {
                return Some(P::CoshDoubleAngle(CoshDoubleAngleProof));
            }
            if let Obj::ArithmeticOperator(ArithmeticOperator::Add(pair)) = &x {
                let (x, y) = (&*pair.left, &*pair.right);
                if matches_equation(
                    fact,
                    sinh(add_objs(x.clone(), y.clone())),
                    add_objs(
                        mul_objs(sinh(x.clone()), cosh(y.clone())),
                        mul_objs(cosh(x.clone()), sinh(y.clone())),
                    ),
                ) {
                    return Some(P::SinhAddition(SinhAdditionProof));
                }
                if matches_equation(
                    fact,
                    cosh(add_objs(x.clone(), y.clone())),
                    add_objs(
                        mul_objs(cosh(x.clone()), cosh(y.clone())),
                        mul_objs(sinh(x.clone()), sinh(y.clone())),
                    ),
                ) {
                    return Some(P::CoshAddition(CoshAdditionProof));
                }
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
fn exp(arg: Obj) -> Obj {
    Obj::ExpLogOperator(ExpLogOperator::Exp(Exp { arg: Box::new(arg) }))
}
fn sinh(arg: Obj) -> Obj {
    Obj::HyperbolicOperator(HyperbolicOperator::Sinh(Sinh { arg: Box::new(arg) }))
}
fn cosh(arg: Obj) -> Obj {
    Obj::HyperbolicOperator(HyperbolicOperator::Cosh(Cosh { arg: Box::new(arg) }))
}
fn tanh(arg: Obj) -> Obj {
    Obj::HyperbolicOperator(HyperbolicOperator::Tanh(Tanh { arg: Box::new(arg) }))
}
fn coth(arg: Obj) -> Obj {
    Obj::HyperbolicOperator(HyperbolicOperator::Coth(Coth { arg: Box::new(arg) }))
}
fn sech(arg: Obj) -> Obj {
    Obj::HyperbolicOperator(HyperbolicOperator::Sech(Sech { arg: Box::new(arg) }))
}
fn csch(arg: Obj) -> Obj {
    Obj::HyperbolicOperator(HyperbolicOperator::Csch(Csch { arg: Box::new(arg) }))
}

pub enum HyperbolicEqualityProof {
    SinhDefinition(SinhDefinitionProof),
    CoshDefinition(CoshDefinitionProof),
    TanhDefinition(TanhDefinitionProof),
    TanhReciprocal(TanhReciprocalProof),
    CothDefinition(CothDefinitionProof),
    CothReciprocal(CothReciprocalProof),
    SechDefinition(SechDefinitionProof),
    SechReciprocal(SechReciprocalProof),
    CschDefinition(CschDefinitionProof),
    CschReciprocal(CschReciprocalProof),
    SinhParity(SinhParityProof),
    CoshParity(CoshParityProof),
    TanhParity(TanhParityProof),
    CothParity(CothParityProof),
    SechParity(SechParityProof),
    CschParity(CschParityProof),
    HyperbolicPythagorean(HyperbolicPythagoreanProof),
    ExpThroughHyperbolic(ExpThroughHyperbolicProof),
    ExpNegativeThroughHyperbolic(ExpNegativeThroughHyperbolicProof),
    TanhSechSquare(TanhSechSquareProof),
    CothCschSquare(CothCschSquareProof),
    TanhCothProduct(TanhCothProductProof),
    TanhThroughSech(TanhThroughSechProof),
    CothThroughCsch(CothThroughCschProof),
    SinhDoubleAngle(SinhDoubleAngleProof),
    CoshDoubleAngle(CoshDoubleAngleProof),
    SinhAddition(SinhAdditionProof),
    CoshAddition(CoshAdditionProof),
}
pub struct SinhDefinitionProof;
pub struct CoshDefinitionProof;
pub struct TanhDefinitionProof;
pub struct TanhReciprocalProof;
pub struct CothDefinitionProof;
pub struct CothReciprocalProof;
pub struct SechDefinitionProof;
pub struct SechReciprocalProof;
pub struct CschDefinitionProof;
pub struct CschReciprocalProof;
pub struct SinhParityProof;
pub struct CoshParityProof;
pub struct TanhParityProof;
pub struct CothParityProof;
pub struct SechParityProof;
pub struct CschParityProof;
pub struct HyperbolicPythagoreanProof;
pub struct ExpThroughHyperbolicProof;
pub struct ExpNegativeThroughHyperbolicProof;
pub struct TanhSechSquareProof;
pub struct CothCschSquareProof;
pub struct TanhCothProductProof;
pub struct TanhThroughSechProof;
pub struct CothThroughCschProof;
pub struct SinhDoubleAngleProof;
pub struct CoshDoubleAngleProof;
pub struct SinhAdditionProof;
pub struct CoshAdditionProof;
impl HyperbolicEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SinhDefinition(_) => "SinhDefinition",
            Self::CoshDefinition(_) => "CoshDefinition",
            Self::TanhDefinition(_) => "TanhDefinition",
            Self::TanhReciprocal(_) => "TanhReciprocal",
            Self::CothDefinition(_) => "CothDefinition",
            Self::CothReciprocal(_) => "CothReciprocal",
            Self::SechDefinition(_) => "SechDefinition",
            Self::SechReciprocal(_) => "SechReciprocal",
            Self::CschDefinition(_) => "CschDefinition",
            Self::CschReciprocal(_) => "CschReciprocal",
            Self::SinhParity(_) => "SinhParity",
            Self::CoshParity(_) => "CoshParity",
            Self::TanhParity(_) => "TanhParity",
            Self::CothParity(_) => "CothParity",
            Self::SechParity(_) => "SechParity",
            Self::CschParity(_) => "CschParity",
            Self::HyperbolicPythagorean(_) => "HyperbolicPythagorean",
            Self::ExpThroughHyperbolic(_) => "ExpThroughHyperbolic",
            Self::ExpNegativeThroughHyperbolic(_) => "ExpNegativeThroughHyperbolic",
            Self::TanhSechSquare(_) => "TanhSechSquare",
            Self::CothCschSquare(_) => "CothCschSquare",
            Self::TanhCothProduct(_) => "TanhCothProduct",
            Self::TanhThroughSech(_) => "TanhThroughSech",
            Self::CothThroughCsch(_) => "CothThroughCsch",
            Self::SinhDoubleAngle(_) => "SinhDoubleAngle",
            Self::CoshDoubleAngle(_) => "CoshDoubleAngle",
            Self::SinhAddition(_) => "SinhAddition",
            Self::CoshAddition(_) => "CoshAddition",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::SinhDefinition(_) => "sinh(x)=(exp(x)-exp(-x))/2",
            Self::CoshDefinition(_) => "cosh(x)=(exp(x)+exp(-x))/2",
            Self::TanhDefinition(_) => "tanh(x)=sinh(x)/cosh(x)",
            Self::TanhReciprocal(_) => "tanh(x)*cosh(x)=sinh(x)",
            Self::CothDefinition(_) => "coth(x)=cosh(x)/sinh(x)",
            Self::CothReciprocal(_) => "coth(x)*sinh(x)=cosh(x)",
            Self::SechDefinition(_) => "sech(x)=1/cosh(x)",
            Self::SechReciprocal(_) => "sech(x)*cosh(x)=1",
            Self::CschDefinition(_) => "csch(x)=1/sinh(x)",
            Self::CschReciprocal(_) => "csch(x)*sinh(x)=1",
            Self::SinhParity(_) => "sinh(-x)=-sinh(x)",
            Self::CoshParity(_) => "cosh(-x)=cosh(x)",
            Self::TanhParity(_) => "tanh(-x)=-tanh(x)",
            Self::CothParity(_) => "coth(-x)=-coth(x)",
            Self::SechParity(_) => "sech(-x)=sech(x)",
            Self::CschParity(_) => "csch(-x)=-csch(x)",
            Self::HyperbolicPythagorean(_) => "cosh(x)^2-sinh(x)^2=1",
            Self::ExpThroughHyperbolic(_) => "exp(x)=cosh(x)+sinh(x)",
            Self::ExpNegativeThroughHyperbolic(_) => "exp(-x)=cosh(x)-sinh(x)",
            Self::TanhSechSquare(_) => "1-tanh(x)^2=sech(x)^2",
            Self::CothCschSquare(_) => "coth(x)^2-1=csch(x)^2",
            Self::TanhCothProduct(_) => "tanh(x)*coth(x)=1",
            Self::TanhThroughSech(_) => "tanh(x)=sinh(x)*sech(x)",
            Self::CothThroughCsch(_) => "coth(x)=cosh(x)*csch(x)",
            Self::SinhDoubleAngle(_) => "sinh(2*x)=2*sinh(x)*cosh(x)",
            Self::CoshDoubleAngle(_) => "cosh(2*x)=cosh(x)^2+sinh(x)^2",
            Self::SinhAddition(_) => "sinh(x+y)=sinh(x)*cosh(y)+cosh(x)*sinh(y)",
            Self::CoshAddition(_) => "cosh(x+y)=cosh(x)*cosh(y)+sinh(x)*sinh(y)",
        }
    }
}
