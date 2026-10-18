//! Fixed conjugation equations. Parent equality WD checks both sides and all domain guards.
use super::super::helper::corresponding_arg_pairs;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
impl Runtime {
    pub(super) fn search_conjugation(
        &mut self,
        fact: &EqualFact,
    ) -> Option<ConjugationEqualityProof> {
        use ConjugationEqualityProof as P;
        let mut pending = vec![fact.left.clone(), fact.right.clone()];
        let mut arguments = Vec::new();
        while let Some(obj) = pending.pop() {
            match &obj {
                Obj::ComplexOperator(ComplexOperator::Conjugate(v)) => {
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
                Conjugate::new(x.clone()).into(),
                sub_objs(
                    re(x.clone()),
                    mul_objs(
                        Obj::Literal(Literal::ImaginaryUnit(ImaginaryUnit)),
                        img(x.clone()),
                    ),
                ),
            ) {
                return Some(P::ConjugateDefinition(ConjugateDefinitionProof));
            }
            if matches_equation(fact, Conjugate::new(conjugate(x.clone())).into(), x.clone()) {
                return Some(P::ConjugateInvolution(ConjugateInvolutionProof));
            }
            if matches_equation(fact, re(conjugate(x.clone())), re(x.clone())) {
                return Some(P::ConjugateRealPart(ConjugateRealPartProof));
            }
            if matches_equation(fact, img(conjugate(x.clone())), neg(img(x.clone()))) {
                return Some(P::ConjugateImaginaryPart(ConjugateImaginaryPartProof));
            }
            if matches_equation(fact, cabs(conjugate(x.clone())), cabs(x.clone())) {
                return Some(P::ConjugateModulus(ConjugateModulusProof));
            }
            if matches_equation(
                fact,
                mul_objs(x.clone(), Conjugate::new(x.clone()).into()),
                square(cabs(x.clone())),
            ) {
                return Some(P::ConjugateNorm(ConjugateNormProof));
            }
            if matches_equation(
                fact,
                Conjugate::new(neg(x.clone())).into(),
                neg(Conjugate::new(x.clone()).into()),
            ) {
                return Some(P::ConjugateNegation(ConjugateNegationProof));
            }
            if matches_equation(fact, conjugate(x.clone()), x.clone()) {
                if let Some(real) = self.search_structural_membership(&x, &StandardSet::R) {
                    return Some(P::ConjugateReal(ConjugateRealProof { real }));
                }
            }
            if let Obj::ArithmeticOperator(ArithmeticOperator::Pow(power)) = &x {
                let expected = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                    base: Box::new(conjugate(*power.base.clone())),
                    exponent: power.exponent.clone(),
                }));
                if matches_equation(fact, conjugate(x.clone()), expected) {
                    if let Some(natural_exponent) =
                        self.search_structural_membership(&power.exponent, &StandardSet::N)
                    {
                        return Some(P::ConjugateNaturalPower(ConjugateNaturalPowerProof {
                            natural_exponent,
                        }));
                    }
                }
            }
            if let Obj::ArithmeticOperator(ArithmeticOperator::Add(pair)) = &x {
                let (x, y) = (&*pair.left, &*pair.right);
                if matches_equation(
                    fact,
                    Conjugate::new(add_objs(x.clone(), y.clone())).into(),
                    add_objs(
                        Conjugate::new(x.clone()).into(),
                        Conjugate::new(y.clone()).into(),
                    ),
                ) {
                    return Some(P::ConjugateAdd(ConjugateAddProof));
                }
            }
            if let Obj::ArithmeticOperator(ArithmeticOperator::Sub(pair)) = &x {
                let (x, y) = (&*pair.left, &*pair.right);
                if matches_equation(
                    fact,
                    Conjugate::new(sub_objs(x.clone(), y.clone())).into(),
                    sub_objs(
                        Conjugate::new(x.clone()).into(),
                        Conjugate::new(y.clone()).into(),
                    ),
                ) {
                    return Some(P::ConjugateSub(ConjugateSubProof));
                }
            }
            if let Obj::ArithmeticOperator(ArithmeticOperator::Mul(pair)) = &x {
                let (x, y) = (&*pair.left, &*pair.right);
                if matches_equation(
                    fact,
                    Conjugate::new(mul_objs(x.clone(), y.clone())).into(),
                    mul_objs(
                        Conjugate::new(x.clone()).into(),
                        Conjugate::new(y.clone()).into(),
                    ),
                ) {
                    return Some(P::ConjugateMul(ConjugateMulProof));
                }
            }
            if let Obj::ArithmeticOperator(ArithmeticOperator::Div(pair)) = &x {
                let (x, y) = (&*pair.left, &*pair.right);
                if matches_equation(
                    fact,
                    Conjugate::new(div_objs(x.clone(), y.clone())).into(),
                    div_objs(
                        Conjugate::new(x.clone()).into(),
                        Conjugate::new(y.clone()).into(),
                    ),
                ) {
                    return Some(P::ConjugateDiv(ConjugateDivProof));
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
fn conjugate(arg: Obj) -> Obj {
    Obj::ComplexOperator(ComplexOperator::Conjugate(Conjugate { arg: Box::new(arg) }))
}
fn re(arg: Obj) -> Obj {
    Obj::ComplexOperator(ComplexOperator::RealPart(RealPart { arg: Box::new(arg) }))
}
fn img(arg: Obj) -> Obj {
    Obj::ComplexOperator(ComplexOperator::ImaginaryPart(ImaginaryPart {
        arg: Box::new(arg),
    }))
}
fn cabs(arg: Obj) -> Obj {
    Obj::ComplexOperator(ComplexOperator::ComplexAbs(ComplexAbs {
        arg: Box::new(arg),
    }))
}

pub enum ConjugationEqualityProof {
    ConjugateDefinition(ConjugateDefinitionProof),
    ConjugateInvolution(ConjugateInvolutionProof),
    ConjugateRealPart(ConjugateRealPartProof),
    ConjugateImaginaryPart(ConjugateImaginaryPartProof),
    ConjugateModulus(ConjugateModulusProof),
    ConjugateNorm(ConjugateNormProof),
    ConjugateNegation(ConjugateNegationProof),
    ConjugateAdd(ConjugateAddProof),
    ConjugateSub(ConjugateSubProof),
    ConjugateMul(ConjugateMulProof),
    ConjugateDiv(ConjugateDivProof),
    ConjugateReal(ConjugateRealProof),
    ConjugateNaturalPower(ConjugateNaturalPowerProof),
}
pub struct ConjugateDefinitionProof;
pub struct ConjugateInvolutionProof;
pub struct ConjugateRealPartProof;
pub struct ConjugateImaginaryPartProof;
pub struct ConjugateModulusProof;
pub struct ConjugateNormProof;
pub struct ConjugateNegationProof;
pub struct ConjugateAddProof;
pub struct ConjugateSubProof;
pub struct ConjugateMulProof;
pub struct ConjugateDivProof;
pub struct ConjugateRealProof {
    pub real: StructuralMembershipProof,
}
pub struct ConjugateNaturalPowerProof {
    pub natural_exponent: StructuralMembershipProof,
}
impl ConjugationEqualityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::ConjugateDefinition(_) => "ConjugateDefinition",
            Self::ConjugateInvolution(_) => "ConjugateInvolution",
            Self::ConjugateRealPart(_) => "ConjugateRealPart",
            Self::ConjugateImaginaryPart(_) => "ConjugateImaginaryPart",
            Self::ConjugateModulus(_) => "ConjugateModulus",
            Self::ConjugateNorm(_) => "ConjugateNorm",
            Self::ConjugateNegation(_) => "ConjugateNegation",
            Self::ConjugateAdd(_) => "ConjugateAdd",
            Self::ConjugateSub(_) => "ConjugateSub",
            Self::ConjugateMul(_) => "ConjugateMul",
            Self::ConjugateDiv(_) => "ConjugateDiv",
            Self::ConjugateReal(_) => "ConjugateReal",
            Self::ConjugateNaturalPower(_) => "ConjugateNaturalPower",
        }
    }
    pub fn law(&self) -> &'static str {
        match self {
            Self::ConjugateDefinition(_) => "conj(z)=re(z)-i*img(z)",
            Self::ConjugateInvolution(_) => "conj(conj(z))=z",
            Self::ConjugateRealPart(_) => "re(conj(z))=re(z)",
            Self::ConjugateImaginaryPart(_) => "img(conj(z))=-img(z)",
            Self::ConjugateModulus(_) => "C_abs(conj(z))=C_abs(z)",
            Self::ConjugateNorm(_) => "z*conj(z)=C_abs(z)^2",
            Self::ConjugateNegation(_) => "conj(-z)=-conj(z)",
            Self::ConjugateAdd(_) => "conj(z + w)=conj(z) + conj(w)",
            Self::ConjugateSub(_) => "conj(z - w)=conj(z) - conj(w)",
            Self::ConjugateMul(_) => "conj(z * w)=conj(z) * conj(w)",
            Self::ConjugateDiv(_) => "conj(z / w)=conj(z) / conj(w)",
            Self::ConjugateReal(_) => "x in R => conj(x)=x",
            Self::ConjugateNaturalPower(_) => "n in N => conj(z^n)=conj(z)^n",
        }
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/native_latex_operations/tests.rs"]
mod native_latex_operations_tests;
