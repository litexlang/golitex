use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::ast::obj::{AtomObj, Obj};
use crate::new_pipeline::runtime::FactId;

pub fn ast_obj_eq(a: &Obj, b: &Obj) -> bool {
    match (a, b) {
        (Obj::Number(x), Obj::Number(y)) => x.normalized_value == y.normalized_value,
        (Obj::Atom(AtomObj::Identifier(x)), Obj::Atom(AtomObj::Identifier(y))) => {
            x.atom_id == y.atom_id
        }
        (
            Obj::Atom(AtomObj::IdentifierWithMod(x)),
            Obj::Atom(AtomObj::IdentifierWithMod(y)),
        ) => x.atom_id == y.atom_id,
        (Obj::Add(x), Obj::Add(y)) => {
            ast_obj_eq(x.left.as_ref(), y.left.as_ref())
                && ast_obj_eq(x.right.as_ref(), y.right.as_ref())
        }
        (Obj::Sub(x), Obj::Sub(y)) => {
            ast_obj_eq(x.left.as_ref(), y.left.as_ref())
                && ast_obj_eq(x.right.as_ref(), y.right.as_ref())
        }
        (Obj::Mul(x), Obj::Mul(y)) => {
            ast_obj_eq(x.left.as_ref(), y.left.as_ref())
                && ast_obj_eq(x.right.as_ref(), y.right.as_ref())
        }
        (Obj::Div(x), Obj::Div(y)) => {
            ast_obj_eq(x.left.as_ref(), y.left.as_ref())
                && ast_obj_eq(x.right.as_ref(), y.right.as_ref())
        }
        _ => a == b,
    }
}

// Same proposition, ignoring FactId / line_file.
pub fn atomic_fact_proposition_eq(a: &AtomicFact, b: &AtomicFact) -> bool {
    use AtomicFact::*;
    match (a, b) {
        (IsSetFact(x), IsSetFact(y)) => ast_obj_eq(&x.set, &y.set),
        (IsNonemptySetFact(x), IsNonemptySetFact(y)) => ast_obj_eq(&x.set, &y.set),
        (IsFiniteSetFact(x), IsFiniteSetFact(y)) => ast_obj_eq(&x.set, &y.set),
        (InFact(x), InFact(y)) => {
            ast_obj_eq(&x.element, &y.element) && ast_obj_eq(&x.set, &y.set)
        }
        (EqualFact(x), EqualFact(y)) => {
            ast_obj_eq(&x.left, &y.left) && ast_obj_eq(&x.right, &y.right)
        }
        (NotEqualFact(x), NotEqualFact(y)) => {
            ast_obj_eq(&x.left, &y.left) && ast_obj_eq(&x.right, &y.right)
        }
        (LessFact(x), LessFact(y)) => {
            ast_obj_eq(&x.left, &y.left) && ast_obj_eq(&x.right, &y.right)
        }
        (GreaterFact(x), GreaterFact(y)) => {
            ast_obj_eq(&x.left, &y.left) && ast_obj_eq(&x.right, &y.right)
        }
        (LessEqualFact(x), LessEqualFact(y)) => {
            ast_obj_eq(&x.left, &y.left) && ast_obj_eq(&x.right, &y.right)
        }
        (GreaterEqualFact(x), GreaterEqualFact(y)) => {
            ast_obj_eq(&x.left, &y.left) && ast_obj_eq(&x.right, &y.right)
        }
        (SubsetFact(x), SubsetFact(y)) => {
            ast_obj_eq(&x.left, &y.left) && ast_obj_eq(&x.right, &y.right)
        }
        (SupersetFact(x), SupersetFact(y)) => {
            ast_obj_eq(&x.left, &y.left) && ast_obj_eq(&x.right, &y.right)
        }
        _ => false,
    }
}

pub fn atomic_fact_id(fact: &AtomicFact) -> FactId {
    match fact {
        AtomicFact::NormalAtomicFact(f) => f.fact_id,
        AtomicFact::EqualFact(f) => f.fact_id,
        AtomicFact::LessFact(f) => f.fact_id,
        AtomicFact::GreaterFact(f) => f.fact_id,
        AtomicFact::LessEqualFact(f) => f.fact_id,
        AtomicFact::GreaterEqualFact(f) => f.fact_id,
        AtomicFact::IsSetFact(f) => f.fact_id,
        AtomicFact::IsNonemptySetFact(f) => f.fact_id,
        AtomicFact::IsFiniteSetFact(f) => f.fact_id,
        AtomicFact::InFact(f) => f.fact_id,
        AtomicFact::IsCartFact(f) => f.fact_id,
        AtomicFact::IsTupleFact(f) => f.fact_id,
        AtomicFact::SubsetFact(f) => f.fact_id,
        AtomicFact::SupersetFact(f) => f.fact_id,
        AtomicFact::NotNormalAtomicFact(f) => f.fact_id,
        AtomicFact::NotEqualFact(f) => f.fact_id,
        AtomicFact::NotLessFact(f) => f.fact_id,
        AtomicFact::NotGreaterFact(f) => f.fact_id,
        AtomicFact::NotLessEqualFact(f) => f.fact_id,
        AtomicFact::NotGreaterEqualFact(f) => f.fact_id,
        AtomicFact::NotIsSetFact(f) => f.fact_id,
        AtomicFact::NotIsNonemptySetFact(f) => f.fact_id,
        AtomicFact::NotIsFiniteSetFact(f) => f.fact_id,
        AtomicFact::NotInFact(f) => f.fact_id,
        AtomicFact::NotIsCartFact(f) => f.fact_id,
        AtomicFact::NotIsTupleFact(f) => f.fact_id,
        AtomicFact::NotSubsetFact(f) => f.fact_id,
        AtomicFact::NotSupersetFact(f) => f.fact_id,
        AtomicFact::FnEqualInFact(f) => f.fact_id,
        AtomicFact::FnEqualFact(f) => f.fact_id,
    }
}

// Stable structural key for WD lookup (tracer surface only).
pub fn ast_obj_key(obj: &Obj) -> String {
    match obj {
        Obj::Number(n) => format!("num:{}", n.normalized_value),
        Obj::Atom(AtomObj::Identifier(id)) => format!("id:{}", id.name),
        Obj::Add(add) => format!(
            "add({},{})",
            ast_obj_key(add.left.as_ref()),
            ast_obj_key(add.right.as_ref())
        ),
        Obj::Sub(sub) => format!(
            "sub({},{})",
            ast_obj_key(sub.left.as_ref()),
            ast_obj_key(sub.right.as_ref())
        ),
        Obj::Mul(mul) => format!(
            "mul({},{})",
            ast_obj_key(mul.left.as_ref()),
            ast_obj_key(mul.right.as_ref())
        ),
        Obj::Div(div) => format!(
            "div({},{})",
            ast_obj_key(div.left.as_ref()),
            ast_obj_key(div.right.as_ref())
        ),
        _ => format!("unsupported:{obj:?}"),
    }
}
