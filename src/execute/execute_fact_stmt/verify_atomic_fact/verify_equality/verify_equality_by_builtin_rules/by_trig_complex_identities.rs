//! Structural trig/complex leaves and consumers of stored coordinate facts.
use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact};
use crate::ast::obj::{
    ArithmeticOperator as A, ComplexAbs, ComplexOperator as C, ImaginaryPart, Literal, Number, Obj,
    RealPart, StandardSet, TrigOperator as T,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub enum TrigComplexIdentityProof {
    SinNegation,
    CosNegation,
    SinPiShift,
    CosPiShift,
    SinDoubleAngle,
    ComplexReconstruction,
    RealPartAddition,
    ImaginaryPartAddition,
    RealPartSubtraction,
    ImaginaryPartSubtraction,
    ComplexPowerCoordinates {
        natural: VerifyFactResult,
    },
    ComplexModulusZero {
        premise: Box<EqualFactSearchedProof>,
        complex: VerifyFactResult,
    },
    ComplexCoordinatesEqual {
        real: Box<EqualFactSearchedProof>,
        imaginary: Box<EqualFactSearchedProof>,
        domains: Vec<VerifyFactResult>,
    },
}
impl TrigComplexIdentityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SinNegation => "SinNegation",
            Self::CosNegation => "CosNegation",
            Self::SinPiShift => "SinPiShift",
            Self::CosPiShift => "CosPiShift",
            Self::SinDoubleAngle => "SinDoubleAngle",
            Self::ComplexReconstruction => "ComplexReconstruction",
            Self::RealPartAddition => "RealPartAddition",
            Self::ImaginaryPartAddition => "ImaginaryPartAddition",
            Self::RealPartSubtraction => "RealPartSubtraction",
            Self::ImaginaryPartSubtraction => "ImaginaryPartSubtraction",
            Self::ComplexModulusZero { .. } => "ComplexModulusZero",
            Self::ComplexCoordinatesEqual { .. } => "ComplexCoordinatesEqual",
            Self::ComplexPowerCoordinates { .. } => "ComplexPowerCoordinates",
        }
    }
}
impl Runtime {
    pub(super) fn search_trig_complex_identity(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<TrigComplexIdentityProof>> {
        use TrigComplexIdentityProof as P;
        // Trig/coordinate operators have already passed the whole equality WD.
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            for sine in [true, false] {
                if let Some(arg) = trig_arg(left, sine) {
                    if let Some(x) = neg_arg(arg) {
                        let target = if sine { neg_arg(right) } else { Some(right) };
                        if target
                            .and_then(|r| trig_arg(r, sine))
                            .is_some_and(|r| same(r, x))
                        {
                            return Ok(Some(if sine { P::SinNegation } else { P::CosNegation }));
                        }
                    }
                    // sin(x+pi)=-sin(x), cos(x+pi)=-cos(x).
                    if let Obj::ArithmeticOperator(A::Add(sum)) = arg {
                        for (x, pi) in [(&*sum.left, &*sum.right), (&*sum.right, &*sum.left)] {
                            if matches!(pi, Obj::Literal(Literal::Pi(_)))
                                && neg_arg(right)
                                    .and_then(|r| trig_arg(r, sine))
                                    .is_some_and(|r| same(r, x))
                            {
                                return Ok(Some(if sine { P::SinPiShift } else { P::CosPiShift }));
                            }
                        }
                    }
                    if sine {
                        if let Some(x) = doubled_arg(arg) {
                            let expected = mul(number("2"), mul(sin(x), cos(x)));
                            if crate::rational_expression::objs_equal_by_rational_expression_evaluation(right,&expected) {
                                return Ok(Some(P::SinDoubleAngle));
                            }
                        }
                    }
                }
            }
            // z = re(z)+img(z)*i, with either scalar multiplication order.
            if let Obj::ArithmeticOperator(A::Add(sum)) = right {
                for (real, imag) in [(&*sum.left, &*sum.right), (&*sum.right, &*sum.left)] {
                    if coordinate(real, true).is_some_and(|z| same(z, left)) {
                        if let Obj::ArithmeticOperator(A::Mul(product)) = imag {
                            for (part, unit) in [
                                (&*product.left, &*product.right),
                                (&*product.right, &*product.left),
                            ] {
                                if matches!(unit, Obj::Literal(Literal::ImaginaryUnit(_)))
                                    && coordinate(part, false).is_some_and(|z| same(z, left))
                                {
                                    return Ok(Some(P::ComplexReconstruction));
                                }
                            }
                        }
                    }
                }
            }
            // Coordinates are additive real-linear maps.
            for real in [true, false] {
                if let Some(arg) = coordinate(left, real) {
                    // z^(n+1)=z^n*z gives the two coordinate recurrences.
                    if let Obj::ArithmeticOperator(A::Pow(power)) = arg {
                        if let Obj::ArithmeticOperator(A::Add(next)) = &*power.exponent {
                            for (n, one) in
                                [(&*next.left, &*next.right), (&*next.right, &*next.left)]
                            {
                                if !matches!(one,Obj::Literal(Literal::Number(v)) if v.normalized_value=="1")
                                {
                                    continue;
                                }
                                let previous =
                                    Obj::ArithmeticOperator(A::Pow(crate::ast::obj::Pow {
                                        base: power.base.clone(),
                                        exponent: Box::new(n.clone()),
                                    }));
                                let expected = if real {
                                    Obj::ArithmeticOperator(A::Sub(crate::ast::obj::Sub {
                                        left: Box::new(mul(
                                            part(&previous, true),
                                            part(&power.base, true),
                                        )),
                                        right: Box::new(mul(
                                            part(&previous, false),
                                            part(&power.base, false),
                                        )),
                                    }))
                                } else {
                                    Obj::ArithmeticOperator(A::Add(crate::ast::obj::Add {
                                        left: Box::new(mul(
                                            part(&previous, true),
                                            part(&power.base, false),
                                        )),
                                        right: Box::new(mul(
                                            part(&previous, false),
                                            part(&power.base, true),
                                        )),
                                    }))
                                };
                                if !crate::rational_expression::objs_equal_by_rational_expression_evaluation(right,&expected) {continue;}
                                let natural = Fact::AtomicFact(AtomicFact::InFact(InFact {
                                    fact_id: self.global_ids.allocate_fact_id(),
                                    element: n.clone(),
                                    set: Obj::StandardSet(StandardSet::N),
                                    line_file: None,
                                }));
                                let natural =
                                    self.verify_builtin_rule_premise(&natural, state.clone())?;
                                if !natural.is_failed() {
                                    return Ok(Some(P::ComplexPowerCoordinates { natural }));
                                }
                            }
                        }
                    }
                    for subtraction in [false, true] {
                        if let (Some((a, b)), Some((x, y))) =
                            (binary(arg, subtraction), binary(right, subtraction))
                        {
                            if coordinate(x, real).is_some_and(|v| same(v, a))
                                && coordinate(y, real).is_some_and(|v| same(v, b))
                            {
                                return Ok(Some(match (real, subtraction) {
                                    (true, false) => P::RealPartAddition,
                                    (false, false) => P::ImaginaryPartAddition,
                                    (true, true) => P::RealPartSubtraction,
                                    (false, true) => P::ImaginaryPartSubtraction,
                                }));
                            }
                        }
                    }
                }
            }
            if is_zero(right) {
                let modulus = Obj::ComplexOperator(C::ComplexAbs(ComplexAbs {
                    arg: Box::new(left.clone()),
                }));
                if let Some(premise) = self.lookup_known_obj_equality(&modulus, &number("0")) {
                    let complex = self.identity_complex_member(left, state.clone())?;
                    if !complex.is_failed() {
                        return Ok(Some(P::ComplexModulusZero {
                            premise: Box::new(premise),
                            complex,
                        }));
                    }
                }
            }
        }
        // Both stored coordinate equalities are required; real-part equality
        // alone never proves equality of complex numbers.
        if let Some(real) =
            self.lookup_known_obj_equality(&part(&fact.left, true), &part(&fact.right, true))
        {
            if let Some(imaginary) =
                self.lookup_known_obj_equality(&part(&fact.left, false), &part(&fact.right, false))
            {
                let domains = vec![
                    self.identity_complex_member(&fact.left, state.clone())?,
                    self.identity_complex_member(&fact.right, state)?,
                ];
                if domains.iter().all(|r| !r.is_failed()) {
                    return Ok(Some(P::ComplexCoordinatesEqual {
                        real: Box::new(real),
                        imaginary: Box::new(imaginary),
                        domains,
                    }));
                }
            }
        }
        Ok(None)
    }
    fn identity_complex_member(
        &mut self,
        obj: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let fact = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: obj.clone(),
            set: Obj::StandardSet(StandardSet::C),
            line_file: None,
        }));
        self.verify_builtin_rule_premise(&fact, state)
    }
}
fn same(a: &Obj, b: &Obj) -> bool {
    a.ir() == b.ir()
}
fn number(v: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(v.into())))
}
fn is_zero(o: &Obj) -> bool {
    matches!(o,Obj::Literal(Literal::Number(v)) if v.normalized_value=="0")
}
fn neg_arg(o: &Obj) -> Option<&Obj> {
    match o {
        Obj::ArithmeticOperator(A::Neg(v)) => Some(&v.arg),
        Obj::ArithmeticOperator(A::Sub(v)) if is_zero(&v.left) => Some(&v.right),
        _ => None,
    }
}
fn trig_arg(o: &Obj, sine: bool) -> Option<&Obj> {
    match (o, sine) {
        (Obj::TrigOperator(T::Sin(v)), true) => Some(&v.arg),
        (Obj::TrigOperator(T::Cos(v)), false) => Some(&v.arg),
        _ => None,
    }
}
fn coordinate(o: &Obj, real: bool) -> Option<&Obj> {
    match (o, real) {
        (Obj::ComplexOperator(C::RealPart(v)), true) => Some(&v.arg),
        (Obj::ComplexOperator(C::ImaginaryPart(v)), false) => Some(&v.arg),
        _ => None,
    }
}
fn part(o: &Obj, real: bool) -> Obj {
    if real {
        Obj::ComplexOperator(C::RealPart(RealPart {
            arg: Box::new(o.clone()),
        }))
    } else {
        Obj::ComplexOperator(C::ImaginaryPart(ImaginaryPart {
            arg: Box::new(o.clone()),
        }))
    }
}
fn binary(o: &Obj, sub: bool) -> Option<(&Obj, &Obj)> {
    match (o, sub) {
        (Obj::ArithmeticOperator(A::Add(v)), false) => Some((&v.left, &v.right)),
        (Obj::ArithmeticOperator(A::Sub(v)), true) => Some((&v.left, &v.right)),
        _ => None,
    }
}
fn doubled_arg(o: &Obj) -> Option<&Obj> {
    match o {
        Obj::ArithmeticOperator(A::Add(v)) if same(&v.left, &v.right) => Some(&v.left),
        Obj::ArithmeticOperator(A::Mul(v)) => {
            for (a, b) in [(&*v.left, &*v.right), (&*v.right, &*v.left)] {
                if matches!(a,Obj::Literal(Literal::Number(n)) if n.normalized_value=="2") {
                    return Some(b);
                }
            }
            None
        }
        _ => None,
    }
}
fn mul(a: Obj, b: Obj) -> Obj {
    Obj::ArithmeticOperator(A::Mul(crate::ast::obj::Mul {
        left: Box::new(a),
        right: Box::new(b),
    }))
}
fn sin(x: &Obj) -> Obj {
    Obj::TrigOperator(T::Sin(crate::ast::obj::Sin {
        arg: Box::new(x.clone()),
    }))
}
fn cos(x: &Obj) -> Obj {
    Obj::TrigOperator(T::Cos(crate::ast::obj::Cos {
        arg: Box::new(x.clone()),
    }))
}
