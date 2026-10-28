//! Structural destructuring for fixed elementary identities; no proof search.
use crate::prelude::*;

pub(super) fn min_args(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Min(p)) => Some((&p.left, &p.right)),
        _ => None,
    }
}
pub(super) fn max_args(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Max(p)) => Some((&p.left, &p.right)),
        _ => None,
    }
}
pub(super) fn add_args(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => Some((&p.left, &p.right)),
        _ => None,
    }
}
pub(super) fn mul_args(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => Some((&p.left, &p.right)),
        _ => None,
    }
}
pub(super) fn gcd_args(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Gcd(p)) => Some((&p.left, &p.right)),
        _ => None,
    }
}
pub(super) fn neg_arg(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(p)) => Some(&p.arg),
        _ => None,
    }
}
pub(super) fn union_args(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::SetOperator(SetOperator::Union(p)) => Some((&p.left, &p.right)),
        _ => None,
    }
}
pub(super) fn intersect_args(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::SetOperator(SetOperator::Intersect(p)) => Some((&p.left, &p.right)),
        _ => None,
    }
}
pub(super) fn cart_args(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ProductShape(ProductShape::Cart(p)) if p.args.len() == 2 => {
            Some((&p.args[0], &p.args[1]))
        }
        _ => None,
    }
}
pub(super) fn power_set_arg(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::SetOperator(SetOperator::PowerSet(p)) => Some(&p.set),
        _ => None,
    }
}
pub(super) fn same(a: &Obj, b: &Obj) -> bool {
    a.ir() == b.ir()
}

pub(super) fn number(n: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.into())))
}
pub(super) fn add(a: &Obj, b: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(a.clone()),
        right: Box::new(b.clone()),
    }))
}
pub(super) fn sub(a: &Obj, b: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
        left: Box::new(a.clone()),
        right: Box::new(b.clone()),
    }))
}
