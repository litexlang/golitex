use crate::new_pipeline::ast::obj::{
    Abs, Add, Ceil, Cos, Div, Exp, Factorial, Floor, Ln, Mul, Obj, Pow, Sign, Sin, Sqrt, Sub, Tan,
};
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;

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
