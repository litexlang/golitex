use crate::obj::{Obj};

pub struct SyntacticVerifier {
}

impl SyntacticVerifier {
    pub fn equal_literally(left: &Obj, right: &Obj) -> bool {
        match left {
            Obj::AtomWithoutPkg(a) => match right {
                Obj::AtomWithoutPkg(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::AtomWithPkg(a) => match right {
                Obj::AtomWithPkg(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::FnObj(f) => match right {
                Obj::FnObj(g) => f.to_string() == g.to_string(),
                _ => false,
            },
            Obj::Number(n) => match right {
                Obj::Number(m) => n.to_string() == m.to_string(),
                _ => false,
            },
            Obj::Add(a) => match right {
                Obj::Add(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Sub(a) => match right {
                Obj::Sub(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Mul(a) => match right {
                Obj::Mul(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Div(a) => match right {
                Obj::Div(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Mod(a) => match right {
                Obj::Mod(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Pow(a) => match right {
                Obj::Pow(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Union(a) => match right {
                Obj::Union(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Intersect(a) => match right {
                Obj::Intersect(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::SetMinus(a) => match right {
                Obj::SetMinus(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::DisjointUnion(a) => match right {
                Obj::DisjointUnion(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Cup(a) => match right {
                Obj::Cup(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Cap(a) => match right {
                Obj::Cap(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::ListSet(a) => match right {
                Obj::ListSet(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::SetBuilder(a) => match right {
                Obj::SetBuilder(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::FnSetWithoutDom(a) => match right {
                Obj::FnSetWithoutDom(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::FnSetWithDom(a) => match right {
                Obj::FnSetWithDom(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::NPosObj(_) => match right {
                Obj::NPosObj(_) => true,
                _ => false,
            },
            Obj::NObj(_) => match right {
                Obj::NObj(_) => true,
                _ => false,
            },
            Obj::QObj(_) => match right {
                Obj::QObj(_) => true,
                _ => false,
            },
            Obj::ZObj(_) => match right {
                Obj::ZObj(_) => true,
                _ => false,
            },
            Obj::RObj(_) => match right {
                Obj::RObj(_) => true,
                _ => false,
            },
            Obj::InstSetTemplateObj(a) => match right {
                Obj::InstSetTemplateObj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Cart(a) => match right {
                Obj::Cart(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::SetDim(a) => match right {
                Obj::SetDim(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Proj(a) => match right {
                Obj::Proj(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Dim(a) => match right {
                Obj::Dim(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Tuple(a) => match right {
                Obj::Tuple(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Count(a) => match right {
                Obj::Count(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Range(a) => match right {
                Obj::Range(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::ClosedRange(a) => match right {
                Obj::ClosedRange(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Val(a) => match right {
                Obj::Val(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::PowerSet(a) => match right {
                Obj::PowerSet(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::Choose(a) => match right {
                Obj::Choose(b) => a.to_string() == b.to_string(),
                _ => false,
            },
            Obj::ObjAtIndex(a) => match right {
                Obj::ObjAtIndex(b) => a.to_string() == b.to_string(),
                _ => false,
            },
        }
    }
}