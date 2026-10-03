//! Exact closed complex coordinates. No symbolic atom or approximate value.
use super::exact_rational::EvalRational;
use crate::ast::obj::{
    Add, ArithmeticOperator as A, ComplexOperator, ExpLogOperator, ImaginaryUnit, Literal, Mul, Neg, Obj, Sqrt, Sub,
};

// Coordinate arithmetic makes a+b*i, b*i+a and either subtraction order agree.
// Example: 3-4*i has coordinates (3,-4), so its principal modulus is 5.
pub(crate) fn exact_complex_coordinates(obj: &Obj) -> Option<(EvalRational, EvalRational)> {
    coordinates(obj, 0)
}

pub(crate) fn exact_complex_value(obj: &Obj) -> Option<Obj> {
    let (real, imaginary) = exact_complex_coordinates(obj)?;
    if imaginary.is_zero() { return Some(real.to_obj()); }
    let (numerator, denominator) = imaginary.parts();
    let magnitude = EvalRational::new(numerator.checked_abs()?, denominator)?;
    let unit = Obj::Literal(Literal::ImaginaryUnit(ImaginaryUnit));
    let term = if magnitude == EvalRational::new(1, 1)? { unit } else {
        Obj::ArithmeticOperator(A::Mul(Mul {
            left: Box::new(magnitude.to_obj()), right: Box::new(unit),
        }))
    };
    Some(if real.is_zero() {
        if imaginary.is_negative() { Obj::ArithmeticOperator(A::Neg(Neg { arg: Box::new(term) })) }
        else { term }
    } else if imaginary.is_negative() {
        Obj::ArithmeticOperator(A::Sub(Sub { left: Box::new(real.to_obj()), right: Box::new(term) }))
    } else {
        Obj::ArithmeticOperator(A::Add(Add { left: Box::new(real.to_obj()), right: Box::new(term) }))
    })
}

pub(crate) fn exact_modulus_radicand(
    obj: &Obj,
) -> Option<(EvalRational, EvalRational, EvalRational)> {
    let (real, imaginary) = exact_complex_coordinates(obj)?;
    let squared = real.mul(&real)?.add(&imaginary.mul(&imaginary)?)?;
    Some((real, imaginary, squared))
}

pub(crate) fn exact_modulus_value(obj: &Obj) -> Option<Obj> {
    let Obj::ComplexOperator(ComplexOperator::ComplexAbs(abs)) = obj else {
        return None;
    };
    let (_, _, squared) = exact_modulus_radicand(&abs.arg)?;
    Some(principal_root(&squared))
}

pub(crate) fn principal_root(squared: &EvalRational) -> Obj {
    match squared.exact_sqrt() {
        Some(value) => value.to_obj(),
        None => Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt {
            arg: Box::new(squared.to_obj()),
        })),
    }
}

fn coordinates(obj: &Obj, depth: usize) -> Option<(EvalRational, EvalRational)> {
    if depth > 64 {
        return None;
    }
    if let Some(real) = EvalRational::from_obj(obj) {
        return Some((real, EvalRational::new(0, 1)?));
    }
    match obj {
        Obj::Literal(Literal::ImaginaryUnit(_)) => {
            Some((EvalRational::new(0, 1)?, EvalRational::new(1, 1)?))
        }
        Obj::ArithmeticOperator(A::Neg(neg)) => {
            let (real, imaginary) = coordinates(&neg.arg, depth + 1)?;
            let zero = EvalRational::new(0, 1)?;
            Some((zero.sub(&real)?, zero.sub(&imaginary)?))
        }
        Obj::ArithmeticOperator(A::Add(add)) => {
            let (ar, ai) = coordinates(&add.left, depth + 1)?;
            let (br, bi) = coordinates(&add.right, depth + 1)?;
            Some((ar.add(&br)?, ai.add(&bi)?))
        }
        Obj::ArithmeticOperator(A::Sub(sub)) => {
            let (ar, ai) = coordinates(&sub.left, depth + 1)?;
            let (br, bi) = coordinates(&sub.right, depth + 1)?;
            Some((ar.sub(&br)?, ai.sub(&bi)?))
        }
        Obj::ArithmeticOperator(A::Mul(mul)) => {
            let (ar, ai) = coordinates(&mul.left, depth + 1)?;
            let (br, bi) = coordinates(&mul.right, depth + 1)?;
            Some((
                ar.mul(&br)?.sub(&ai.mul(&bi)?)?,
                ar.mul(&bi)?.add(&ai.mul(&br)?)?,
            ))
        }
        Obj::ArithmeticOperator(A::Div(div)) => {
            let (ar, ai) = coordinates(&div.left, depth + 1)?;
            let (br, bi) = coordinates(&div.right, depth + 1)?;
            let denominator = br.mul(&br)?.add(&bi.mul(&bi)?)?;
            Some((
                ar.mul(&br)?.add(&ai.mul(&bi)?)?.div(&denominator)?,
                ai.mul(&br)?.sub(&ar.mul(&bi)?)?.div(&denominator)?,
            ))
        }
        Obj::ArithmeticOperator(A::Pow(power)) => {
            let base = coordinates(&power.base, depth + 1)?;
            let exponent = EvalRational::from_obj(&power.exponent)?.to_i128_if_integer()?;
            complex_integer_power(base, exponent)
        }
        _ => None,
    }
}

// Finite repeated squaring; reciprocal uses the exact nonzero norm. Overflow,
// noninteger exponents and zero negative powers return no certificate.
fn complex_integer_power(
    mut base: (EvalRational, EvalRational),
    exponent: i128,
) -> Option<(EvalRational, EvalRational)> {
    let mut magnitude = usize::try_from(exponent.checked_abs()?).ok()?;
    if exponent < 0 {
        let norm = base.0.mul(&base.0)?.add(&base.1.mul(&base.1)?)?;
        base = (
            base.0.div(&norm)?,
            EvalRational::new(0, 1)?.sub(&base.1)?.div(&norm)?,
        );
    }
    let mut value = (EvalRational::new(1, 1)?, EvalRational::new(0, 1)?);
    while magnitude != 0 {
        if magnitude & 1 == 1 {
            value = multiply_coordinates(&value, &base)?;
        }
        magnitude >>= 1;
        if magnitude != 0 {
            base = multiply_coordinates(&base, &base)?;
        }
    }
    Some(value)
}

fn multiply_coordinates(
    left: &(EvalRational, EvalRational),
    right: &(EvalRational, EvalRational),
) -> Option<(EvalRational, EvalRational)> {
    Some((
        left.0.mul(&right.0)?.sub(&left.1.mul(&right.1)?)?,
        left.0.mul(&right.1)?.add(&left.1.mul(&right.0)?)?,
    ))
}
