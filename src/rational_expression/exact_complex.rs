//! Exact closed complex coordinates. No symbolic atom or approximate value.
use crate::ast::obj::{ArithmeticOperator as A, ComplexOperator, ExpLogOperator, Literal, Obj, Sqrt};
use super::exact_rational::EvalRational;

// Coordinate arithmetic makes a+b*i, b*i+a and either subtraction order agree.
// Example: 3-4*i has coordinates (3,-4), so its principal modulus is 5.
pub(crate) fn exact_complex_coordinates(obj: &Obj) -> Option<(EvalRational, EvalRational)> {
    coordinates(obj, 0)
}

pub(crate) fn exact_modulus_radicand(obj: &Obj) -> Option<(EvalRational, EvalRational, EvalRational)> {
    let (real, imaginary) = exact_complex_coordinates(obj)?;
    let squared = real.mul(&real)?.add(&imaginary.mul(&imaginary)?)?;
    Some((real, imaginary, squared))
}

pub(crate) fn exact_modulus_value(obj: &Obj) -> Option<Obj> {
    let Obj::ComplexOperator(ComplexOperator::ComplexAbs(abs)) = obj else { return None; };
    let (_, _, squared) = exact_modulus_radicand(&abs.arg)?;
    Some(principal_root(&squared))
}

pub(crate) fn principal_root(squared: &EvalRational) -> Obj {
    match squared.exact_sqrt() {
        Some(value) => value.to_obj(),
        None => Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg: Box::new(squared.to_obj()) })),
    }
}

fn coordinates(obj: &Obj, depth: usize) -> Option<(EvalRational, EvalRational)> {
    if depth > 64 { return None; }
    if let Some(real) = EvalRational::from_obj(obj) {
        return Some((real, EvalRational::new(0, 1)?));
    }
    match obj {
        Obj::Literal(Literal::ImaginaryUnit(_)) => Some((EvalRational::new(0, 1)?, EvalRational::new(1, 1)?)),
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
            Some((ar.mul(&br)?.sub(&ai.mul(&bi)?)?, ar.mul(&bi)?.add(&ai.mul(&br)?)?))
        }
        Obj::ArithmeticOperator(A::Div(div)) => {
            let (ar, ai) = coordinates(&div.left, depth + 1)?;
            let (br, bi) = coordinates(&div.right, depth + 1)?;
            let denominator = br.mul(&br)?.add(&bi.mul(&bi)?)?;
            Some((ar.mul(&br)?.add(&ai.mul(&bi)?)?.div(&denominator)?, ai.mul(&br)?.sub(&ar.mul(&bi)?)?.div(&denominator)?))
        }
        _ => None,
    }
}
