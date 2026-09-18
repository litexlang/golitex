use crate::new_pipeline::ast::obj::{
    Abs, Add, Arcsin, Ceil, ComplexAbs, Cos, Cot, Div, Exp, Factorial, Floor, Gcd, ImaginaryPart,
    Lcm, Ln, Log, Max, Min, Mod, Mul, Obj, Pow, Quot, RealPart, Sign, Sin, Sqrt, Sub, Tan,
};
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;

// Same-shape child pairs for MatchingOneArgByOne (legacy same_shape peel).
// None = different constructors / unsupported shape. Empty Vec = no children.
pub(super) fn corresponding_arg_pairs(left: &Obj, right: &Obj) -> Option<Vec<(Obj, Obj)>> {
    macro_rules! binary {
        ($l:expr, $r:expr) => {
            Some(vec![
                ($l.left.as_ref().clone(), $r.left.as_ref().clone()),
                ($l.right.as_ref().clone(), $r.right.as_ref().clone()),
            ])
        };
    }
    macro_rules! unary {
        ($l:expr, $r:expr) => {
            Some(vec![($l.arg.as_ref().clone(), $r.arg.as_ref().clone())])
        };
    }

    match (left, right) {
        (Obj::Add(l), Obj::Add(r)) => binary!(l, r),
        (Obj::Sub(l), Obj::Sub(r)) => binary!(l, r),
        (Obj::Mul(l), Obj::Mul(r)) => binary!(l, r),
        (Obj::Div(l), Obj::Div(r)) => binary!(l, r),
        (Obj::Mod(l), Obj::Mod(r)) => binary!(l, r),
        (Obj::Quot(l), Obj::Quot(r)) => binary!(l, r),
        (Obj::Gcd(l), Obj::Gcd(r)) => binary!(l, r),
        (Obj::Lcm(l), Obj::Lcm(r)) => binary!(l, r),
        (Obj::Min(l), Obj::Min(r)) => binary!(l, r),
        (Obj::Max(l), Obj::Max(r)) => binary!(l, r),
        (Obj::Pow(l), Obj::Pow(r)) => Some(vec![
            (l.base.as_ref().clone(), r.base.as_ref().clone()),
            (l.exponent.as_ref().clone(), r.exponent.as_ref().clone()),
        ]),
        (Obj::Log(l), Obj::Log(r)) => Some(vec![
            (l.base.as_ref().clone(), r.base.as_ref().clone()),
            (l.arg.as_ref().clone(), r.arg.as_ref().clone()),
        ]),
        (Obj::Abs(l), Obj::Abs(r)) => unary!(l, r),
        (Obj::Floor(l), Obj::Floor(r)) => unary!(l, r),
        (Obj::Ceil(l), Obj::Ceil(r)) => unary!(l, r),
        (Obj::Exp(l), Obj::Exp(r)) => unary!(l, r),
        (Obj::Ln(l), Obj::Ln(r)) => unary!(l, r),
        (Obj::Sign(l), Obj::Sign(r)) => unary!(l, r),
        (Obj::Factorial(l), Obj::Factorial(r)) => unary!(l, r),
        (Obj::Sqrt(l), Obj::Sqrt(r)) => unary!(l, r),
        (Obj::Sin(l), Obj::Sin(r)) => unary!(l, r),
        (Obj::Cos(l), Obj::Cos(r)) => unary!(l, r),
        (Obj::Tan(l), Obj::Tan(r)) => unary!(l, r),
        (Obj::Cot(l), Obj::Cot(r)) => unary!(l, r),
        (Obj::Arcsin(l), Obj::Arcsin(r)) => unary!(l, r),
        (Obj::RealPart(l), Obj::RealPart(r)) => unary!(l, r),
        (Obj::ImaginaryPart(l), Obj::ImaginaryPart(r)) => unary!(l, r),
        (Obj::ComplexAbs(l), Obj::ComplexAbs(r)) => unary!(l, r),
        _ => None,
    }
}

// Replace every subtree whose IR equals `from_ir` with `to` (top-down).
// Owned by ClosedNumericEqualSubstitution only — not a global resolve_obj,
// and not a general known-equality congruence rewrite.
pub(super) fn replace_obj_matching_ir(obj: &Obj, from_ir: &ObjIR, to: &Obj) -> Obj {
    if &obj.ir() == from_ir {
        return to.clone();
    }
    match obj {
        Obj::Add(a) => Obj::Add(Add {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Sub(a) => Obj::Sub(Sub {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Mul(a) => Obj::Mul(Mul {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Div(a) => Obj::Div(Div {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Pow(a) => Obj::Pow(Pow {
            base: Box::new(replace_obj_matching_ir(&a.base, from_ir, to)),
            exponent: Box::new(replace_obj_matching_ir(&a.exponent, from_ir, to)),
        }),
        Obj::Abs(a) => Obj::Abs(Abs {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Floor(a) => Obj::Floor(Floor {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Ceil(a) => Obj::Ceil(Ceil {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Exp(a) => Obj::Exp(Exp {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Ln(a) => Obj::Ln(Ln {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Sign(a) => Obj::Sign(Sign {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Factorial(a) => Obj::Factorial(Factorial {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Sqrt(a) => Obj::Sqrt(Sqrt {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Sin(a) => Obj::Sin(Sin {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Cos(a) => Obj::Cos(Cos {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        Obj::Tan(a) => Obj::Tan(Tan {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        }),
        _ => obj.clone(),
    }
}
