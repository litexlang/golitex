use crate::new_pipeline::ast::obj::{
    Abs, Add, Arcsin, Ceil, ComplexAbs, Cos, Cot, Div, Exp, Factorial, Floor, Gcd, ImaginaryPart,
    Lcm, Ln, Log, Max, Min, Mod, Mul, Obj, Pow, Quot, RealPart, Sign, Sin, Sqrt, Sub, Tan,
};

use super::super::InstCtx;
use super::super::error::InstError;

macro_rules! unary {
    ($ctx:expr, $inner:expr, $cons:ident) => {
        Ok(Obj::$cons($cons {
            arg: Box::new($ctx.inst_obj($inner)?),
        }))
    };
}

macro_rules! binary {
    ($ctx:expr, $left:expr, $right:expr, $cons:ident) => {
        Ok(Obj::$cons($cons {
            left: Box::new($ctx.inst_obj($left)?),
            right: Box::new($ctx.inst_obj($right)?),
        }))
    };
}

pub fn inst_add(ctx: &mut InstCtx<'_>, a: &Add) -> Result<Obj, InstError> {
    binary!(ctx, &a.left, &a.right, Add)
}

pub fn inst_sub(ctx: &mut InstCtx<'_>, a: &Sub) -> Result<Obj, InstError> {
    binary!(ctx, &a.left, &a.right, Sub)
}

pub fn inst_mul(ctx: &mut InstCtx<'_>, a: &Mul) -> Result<Obj, InstError> {
    binary!(ctx, &a.left, &a.right, Mul)
}

pub fn inst_div(ctx: &mut InstCtx<'_>, a: &Div) -> Result<Obj, InstError> {
    binary!(ctx, &a.left, &a.right, Div)
}

pub fn inst_mod(ctx: &mut InstCtx<'_>, a: &Mod) -> Result<Obj, InstError> {
    binary!(ctx, &a.left, &a.right, Mod)
}

pub fn inst_quot(ctx: &mut InstCtx<'_>, a: &Quot) -> Result<Obj, InstError> {
    binary!(ctx, &a.left, &a.right, Quot)
}

pub fn inst_gcd(ctx: &mut InstCtx<'_>, a: &Gcd) -> Result<Obj, InstError> {
    binary!(ctx, &a.left, &a.right, Gcd)
}

pub fn inst_lcm(ctx: &mut InstCtx<'_>, a: &Lcm) -> Result<Obj, InstError> {
    binary!(ctx, &a.left, &a.right, Lcm)
}

pub fn inst_min(ctx: &mut InstCtx<'_>, a: &Min) -> Result<Obj, InstError> {
    binary!(ctx, &a.left, &a.right, Min)
}

pub fn inst_max(ctx: &mut InstCtx<'_>, a: &Max) -> Result<Obj, InstError> {
    binary!(ctx, &a.left, &a.right, Max)
}

pub fn inst_pow(ctx: &mut InstCtx<'_>, a: &Pow) -> Result<Obj, InstError> {
    Ok(Obj::Pow(Pow {
        base: Box::new(ctx.inst_obj(&a.base)?),
        exponent: Box::new(ctx.inst_obj(&a.exponent)?),
    }))
}

pub fn inst_log(ctx: &mut InstCtx<'_>, a: &Log) -> Result<Obj, InstError> {
    Ok(Obj::Log(Log {
        base: Box::new(ctx.inst_obj(&a.base)?),
        arg: Box::new(ctx.inst_obj(&a.arg)?),
    }))
}

pub fn inst_floor(ctx: &mut InstCtx<'_>, a: &Floor) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Floor)
}

pub fn inst_ceil(ctx: &mut InstCtx<'_>, a: &Ceil) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Ceil)
}

pub fn inst_exp(ctx: &mut InstCtx<'_>, a: &Exp) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Exp)
}

pub fn inst_ln(ctx: &mut InstCtx<'_>, a: &Ln) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Ln)
}

pub fn inst_sign(ctx: &mut InstCtx<'_>, a: &Sign) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Sign)
}

pub fn inst_factorial(ctx: &mut InstCtx<'_>, a: &Factorial) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Factorial)
}

pub fn inst_abs(ctx: &mut InstCtx<'_>, a: &Abs) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Abs)
}

pub fn inst_sin(ctx: &mut InstCtx<'_>, a: &Sin) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Sin)
}

pub fn inst_arcsin(ctx: &mut InstCtx<'_>, a: &Arcsin) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Arcsin)
}

pub fn inst_cos(ctx: &mut InstCtx<'_>, a: &Cos) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Cos)
}

pub fn inst_tan(ctx: &mut InstCtx<'_>, a: &Tan) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Tan)
}

pub fn inst_cot(ctx: &mut InstCtx<'_>, a: &Cot) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Cot)
}

pub fn inst_real_part(ctx: &mut InstCtx<'_>, a: &RealPart) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, RealPart)
}

pub fn inst_imaginary_part(ctx: &mut InstCtx<'_>, a: &ImaginaryPart) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, ImaginaryPart)
}

pub fn inst_complex_abs(ctx: &mut InstCtx<'_>, a: &ComplexAbs) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, ComplexAbs)
}

pub fn inst_sqrt(ctx: &mut InstCtx<'_>, a: &Sqrt) -> Result<Obj, InstError> {
    unary!(ctx, &a.arg, Sqrt)
}
