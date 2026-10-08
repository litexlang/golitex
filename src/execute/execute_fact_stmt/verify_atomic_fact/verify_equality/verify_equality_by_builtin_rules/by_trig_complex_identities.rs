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
    SinThreeAngleSum(SinThreeAngleSumProof),
    TanAddition(TanAdditionProof),
    ComplexModulusCoordinates(ComplexModulusCoordinatesProof),
    RealPartQuotient(RealPartQuotientProof),
    ImaginaryPartQuotient(ImaginaryPartQuotientProof),
    TanCotProduct(super::by_trig_quotient_relations::TanCotProductBuiltinRuleProof),
    TanSquareReciprocalCosine(super::by_trig_quotient_relations::TanSquareReciprocalCosineBuiltinRuleProof),
    SinHalfPiShift(SinHalfPiShiftProof),
    CosHalfPiShift(CosHalfPiShiftProof),
    CosDoubleAngle(CosDoubleAngleBuiltinRuleProof),
    SinPiReflection(SinPiReflectionBuiltinRuleProof),
    CosPiReflection(CosPiReflectionBuiltinRuleProof),
    SinHalfPiReflection(SinHalfPiReflectionBuiltinRuleProof),
    CosHalfPiReflection(CosHalfPiReflectionBuiltinRuleProof),
    PeriodicTrig(super::by_periodic_trig::PeriodicTrigBuiltinRuleProof),
    NumericComplexModulus(super::by_numeric_complex_modulus::NumericComplexModulusBuiltinRuleProof),
    SinNegation,
    CosNegation,
    SinPiShift,
    CosPiShift,
    SinDoubleAngle,
    SinDifference,
    CosDifference,
    ComplexModulusProduct,
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
// Fixed three-angle expansion; this does not reintroduce recursive trig search.
pub struct SinThreeAngleSumProof {
    pub first: Obj,
    pub second: Obj,
    pub third: Obj,
}
impl SinThreeAngleSumProof {
    pub fn new(first: Obj, second: Obj, third: Obj) -> Self { Self { first, second, third } }
}
// Parent WD owns cos(x), cos(y), cos(x+y) and the tangent-sum denominator.
pub struct TanAdditionProof;
// Parent equality WD checks z in C and the principal-root radicand.
// Example: C_abs(z)=sqrt(re(z)^2+img(z)^2).
pub struct ComplexModulusCoordinatesProof;
// Parent equality WD checks z/w and the squared-modulus denominator.
// Example: re(z/w)=(re(z)*re(w)+img(z)*img(w))/C_abs(w)^2.
pub struct RealPartQuotientProof;
pub struct ImaginaryPartQuotientProof;
pub struct SinHalfPiShiftProof;
pub struct CosHalfPiShiftProof;
pub enum CosDoubleAngleForm {
    CosineSquareMinusSineSquare,
    OneMinusTwiceSineSquare,
    TwiceCosineSquareMinusOne,
}
pub struct CosDoubleAngleBuiltinRuleProof {
    pub angle: Obj,
    pub form: CosDoubleAngleForm,
}
impl CosDoubleAngleBuiltinRuleProof {
    pub fn new(angle: Obj, form: CosDoubleAngleForm) -> Self { Self { angle, form } }
}
pub struct SinPiReflectionBuiltinRuleProof { pub angle: Obj }
impl SinPiReflectionBuiltinRuleProof {
    pub fn new(angle: Obj) -> Self { Self { angle } }
}
pub struct CosPiReflectionBuiltinRuleProof { pub angle: Obj }
impl CosPiReflectionBuiltinRuleProof {
    pub fn new(angle: Obj) -> Self { Self { angle } }
}
pub struct SinHalfPiReflectionBuiltinRuleProof { pub angle: Obj }
impl SinHalfPiReflectionBuiltinRuleProof {
    pub fn new(angle: Obj) -> Self { Self { angle } }
}
pub struct CosHalfPiReflectionBuiltinRuleProof { pub angle: Obj }
impl CosHalfPiReflectionBuiltinRuleProof {
    pub fn new(angle: Obj) -> Self { Self { angle } }
}
impl TrigComplexIdentityProof {
    pub fn rule_id(&self) -> &'static str {
        match self {
            Self::SinThreeAngleSum(_) => "SinThreeAngleSum",
            Self::TanAddition(_) => "TanAddition",
            Self::ComplexModulusCoordinates(_) => "ComplexModulusCoordinates",
            Self::RealPartQuotient(_) => "RealPartQuotient",
            Self::ImaginaryPartQuotient(_) => "ImaginaryPartQuotient",
            Self::TanCotProduct(_) => "TanCotProduct",
            Self::TanSquareReciprocalCosine(_) => "TanSquareReciprocalCosine",
            Self::SinHalfPiShift(_) => "SinHalfPiShift",
            Self::CosHalfPiShift(_) => "CosHalfPiShift",
            Self::CosDoubleAngle(_) => "CosDoubleAngle",
            Self::SinPiReflection(_) => "SinPiReflection",
            Self::CosPiReflection(_) => "CosPiReflection",
            Self::SinHalfPiReflection(_) => "SinHalfPiReflection",
            Self::CosHalfPiReflection(_) => "CosHalfPiReflection",
            Self::PeriodicTrig(_) => "PeriodicTrig",
            Self::NumericComplexModulus(_) => "NumericComplexModulus",
            Self::SinNegation => "SinNegation",
            Self::CosNegation => "CosNegation",
            Self::SinPiShift => "SinPiShift",
            Self::CosPiShift => "CosPiShift",
            Self::SinDoubleAngle => "SinDoubleAngle",
            Self::SinDifference => "SinDifference",
            Self::CosDifference => "CosDifference",
            Self::ComplexModulusProduct => "ComplexModulusProduct",
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
        if let Some(proof) = super::by_numeric_complex_modulus::numeric_complex_modulus(fact) {
            return Ok(Some(P::NumericComplexModulus(proof)));
        }
        for (left, right) in [(&fact.left, &fact.right), (&fact.right, &fact.left)] {
            // sin(x+y+z) has a fixed four-term expansion for real arguments.
            // Support the two explicit Add-tree associations, not longer sums.
            if let Obj::TrigOperator(T::Sin(sine)) = left {
                if let Obj::ArithmeticOperator(A::Add(sum)) = &*sine.arg {
                    let triple = match (&*sum.left, &*sum.right) {
                        (Obj::ArithmeticOperator(A::Add(pair)), third) => Some((&*pair.left, &*pair.right, third)),
                        (first, Obj::ArithmeticOperator(A::Add(pair))) => Some((first, &*pair.left, &*pair.right)),
                        _ => None,
                    };
                    if let Some((x,y,z)) = triple {
                        let first = mul(mul(sin(x),cos(y)),cos(z));
                        let second = mul(mul(cos(x),sin(y)),cos(z));
                        let third = mul(mul(cos(x),cos(y)),sin(z));
                        let negative = mul(mul(sin(x),sin(y)),sin(z));
                        let expected = subtract(add(add(first,second),third),negative);
                        if crate::rational_expression::objs_equal_by_rational_expression_evaluation(right,&expected) {
                            return Ok(Some(P::SinThreeAngleSum(SinThreeAngleSumProof::new(x.clone(),y.clone(),z.clone()))));
                        }
                    }
                }
            }
            // tan(x+y)=(tan(x)+tan(y))/(1-tan(x)*tan(y)).
            if let Obj::TrigOperator(T::Tan(tangent)) = left {
                if let Obj::ArithmeticOperator(A::Add(sum)) = &*tangent.arg {
                    let x = Obj::TrigOperator(T::Tan(crate::ast::obj::Tan { arg: sum.left.clone() }));
                    let y = Obj::TrigOperator(T::Tan(crate::ast::obj::Tan { arg: sum.right.clone() }));
                    let expected = Obj::ArithmeticOperator(A::Div(crate::ast::obj::Div {
                        left: Box::new(add(x.clone(),y.clone())),
                        right: Box::new(subtract(number("1"),mul(x,y))),
                    }));
                    if crate::rational_expression::objs_equal_by_rational_expression_evaluation(right,&expected) {
                        return Ok(Some(P::TanAddition(TanAdditionProof)));
                    }
                }
            }

            if let Some(proof) = super::by_trig_quotient_relations::trig_quotient_relation(left, right) {
                return Ok(Some(proof));
            }
            if let Some(proof) = self.periodic_trig_value(left, state.clone())? {
                if crate::rational_expression::objs_equal_by_rational_expression_evaluation(&proof.value, right) {
                    return Ok(Some(P::PeriodicTrig(proof)));
                }
            }
            for sine in [true, false] {
                if let Some(arg) = trig_arg(left, sine) {
                    // Real reflections: sin(pi-x)=sin(x), cos(pi-x)=-cos(x),
                    // sin(pi/2-x)=cos(x), cos(pi/2-x)=sin(x). Parent WD owns R.
                    for half_turn in [true, false] {
                        if let Some(x) = super::helper::pi_reflection_argument(arg, half_turn) {
                            let expected = match (sine, half_turn) {
                                (true, true) | (false, false) => sin(x),
                                (true, false) => cos(x),
                                (false, true) => Obj::ArithmeticOperator(A::Neg(crate::ast::obj::Neg {
                                    arg: Box::new(cos(x)),
                                })),
                            };
                            if crate::rational_expression::objs_equal_by_rational_expression_evaluation(right, &expected) {
                                return Ok(Some(match (sine, half_turn) {
                                    (true, true) => P::SinPiReflection(SinPiReflectionBuiltinRuleProof::new(x.clone())),
                                    (false, true) => P::CosPiReflection(CosPiReflectionBuiltinRuleProof::new(x.clone())),
                                    (true, false) => P::SinHalfPiReflection(SinHalfPiReflectionBuiltinRuleProof::new(x.clone())),
                                    (false, false) => P::CosHalfPiReflection(CosHalfPiReflectionBuiltinRuleProof::new(x.clone())),
                                }));
                            }
                        }
                    }
                    // cos(2*x) has three equivalent fixed real double-angle forms.
                    // No trig expansion search: only compare RHS rational expressions.
                    if !sine {
                        if let Some(x) = doubled_arg(arg) {
                            use CosDoubleAngleForm as F;
                            for (expected, form) in [
                                (subtract(square(cos(x)), square(sin(x))), F::CosineSquareMinusSineSquare),
                                (subtract(number("1"), mul(number("2"), square(sin(x)))), F::OneMinusTwiceSineSquare),
                                (subtract(mul(number("2"), square(cos(x))), number("1")), F::TwiceCosineSquareMinusOne),
                            ] {
                                if crate::rational_expression::objs_equal_by_rational_expression_evaluation(right, &expected) {
                                    return Ok(Some(P::CosDoubleAngle(CosDoubleAngleBuiltinRuleProof::new(x.clone(), form))));
                                }
                            }
                        }
                    }
                    // Real quarter-turn: sin(x+pi/2)=cos(x), cos(x+pi/2)=-sin(x).
                    // The whole equality WD establishes real arguments and defined arithmetic.
                    if let Obj::ArithmeticOperator(A::Add(sum)) = arg {
                        for (x, shift) in [(&*sum.left, &*sum.right), (&*sum.right, &*sum.left)] {
                            let Some(coefficient) = crate::rational_expression::pi_multiple::pi_coefficient(shift) else { continue; };
                            if !crate::rational_expression::objs_equal_by_rational_expression_evaluation(&coefficient, &number("0.5")) { continue; }
                            let expected = if sine { cos(x) } else {
                                Obj::ArithmeticOperator(A::Neg(crate::ast::obj::Neg { arg: Box::new(sin(x)) }))
                            };
                            if crate::rational_expression::objs_equal_by_rational_expression_evaluation(right, &expected) {
                                return Ok(Some(if sine { P::SinHalfPiShift(SinHalfPiShiftProof) } else { P::CosHalfPiShift(CosHalfPiShiftProof) }));
                            }
                        }
                    }
                    // Difference-angle identities over the real arguments checked by WD.
                    // sin(x-y)=sin(x)cos(y)-cos(x)sin(y), with the dual cosine sum.
                    if let Obj::ArithmeticOperator(A::Sub(difference)) = arg {
                        let (x, y) = (&*difference.left, &*difference.right);
                        let expected = if sine {
                            Obj::ArithmeticOperator(A::Sub(crate::ast::obj::Sub {
                                left: Box::new(mul(sin(x), cos(y))),
                                right: Box::new(mul(cos(x), sin(y))),
                            }))
                        } else {
                            Obj::ArithmeticOperator(A::Add(crate::ast::obj::Add {
                                left: Box::new(mul(cos(x), cos(y))),
                                right: Box::new(mul(sin(x), sin(y))),
                            }))
                        };
                        if crate::rational_expression::objs_equal_by_rational_expression_evaluation(right, &expected) {
                            return Ok(Some(if sine { P::SinDifference } else { P::CosDifference }));
                        }
                    }
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
            // The complex modulus is multiplicative: |z*w|=|z|*|w|.
            // The complete equality WD checks both complex arguments.
            if let Obj::ComplexOperator(C::ComplexAbs(abs)) = left {
                let radicand = Obj::ArithmeticOperator(A::Add(crate::ast::obj::Add {
                    left: Box::new(square(part(&abs.arg, true))),
                    right: Box::new(square(part(&abs.arg, false))),
                }));
                if let Obj::ExpLogOperator(crate::ast::obj::ExpLogOperator::Sqrt(root)) = right {
                    if crate::rational_expression::objs_equal_by_rational_expression_evaluation(&root.arg, &radicand) {
                        return Ok(Some(P::ComplexModulusCoordinates(ComplexModulusCoordinatesProof)));
                    }
                }
                if let Obj::ArithmeticOperator(A::Mul(product)) = &*abs.arg {
                    let expected = mul(modulus(&product.left), modulus(&product.right));
                    if crate::rational_expression::objs_equal_by_rational_expression_evaluation(right, &expected) {
                        return Ok(Some(P::ComplexModulusProduct));
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
                    // Multiply z/w by the conjugate of w; the two coordinate
                    // numerators differ by a sign. Never confuse re with img.
                    if let Obj::ArithmeticOperator(A::Div(quotient)) = arg {
                        let first = mul(part(&quotient.left, real), part(&quotient.right, true));
                        let second = mul(part(&quotient.left, !real), part(&quotient.right, false));
                        let numerator = if real {
                            Obj::ArithmeticOperator(A::Add(crate::ast::obj::Add { left: Box::new(first), right: Box::new(second) }))
                        } else { subtract(first, second) };
                        let expected = Obj::ArithmeticOperator(A::Div(crate::ast::obj::Div {
                            left: Box::new(numerator), right: Box::new(square(modulus(&quotient.right))),
                        }));
                        if crate::rational_expression::objs_equal_by_rational_expression_evaluation(right, &expected) {
                            return Ok(Some(if real { P::RealPartQuotient(RealPartQuotientProof) }
                                else { P::ImaginaryPartQuotient(ImaginaryPartQuotientProof) }));
                        }
                    }
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
fn subtract(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(A::Sub(crate::ast::obj::Sub {
        left: Box::new(left), right: Box::new(right),
    }))
}
fn square(base: Obj) -> Obj {
    Obj::ArithmeticOperator(A::Pow(crate::ast::obj::Pow {
        base: Box::new(base), exponent: Box::new(number("2")),
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
fn modulus(x: &Obj) -> Obj {
    Obj::ComplexOperator(C::ComplexAbs(ComplexAbs { arg: Box::new(x.clone()) }))
}

fn add(left: Obj, right: Obj) -> Obj {
    Obj::ArithmeticOperator(A::Add(crate::ast::obj::Add { left: Box::new(left), right: Box::new(right) }))
}
