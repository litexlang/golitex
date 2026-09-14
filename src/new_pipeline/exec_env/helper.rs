use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{AtomObj, Obj};
use crate::new_pipeline::runtime::FactId;

const EQUAL: &str = "=";
const LESS: &str = "<";
const GREATER: &str = ">";
const LESS_EQUAL: &str = "<=";
const GREATER_EQUAL: &str = ">=";
const IN: &str = "in";
const IS_SET: &str = "is_set";
const IS_NONEMPTY_SET: &str = "is_nonempty_set";
const IS_FINITE_SET: &str = "is_finite_set";
const IS_CART: &str = "is_cart";
const IS_TUPLE: &str = "is_tuple";
const SUBSET: &str = "subset";
const SUPERSET: &str = "superset";
const FN_EQ: &str = "fn_eq";
const FN_EQ_IN: &str = "fn_eq_in";

pub fn ast_obj_eq(a: &Obj, b: &Obj) -> bool {
    match (a, b) {
        (Obj::Number(x), Obj::Number(y)) => x.normalized_value == y.normalized_value,
        (Obj::Atom(AtomObj::Identifier(x)), Obj::Atom(AtomObj::Identifier(y))) => {
            x.identifier_id == y.identifier_id
        }
        (
            Obj::Atom(AtomObj::IdentifierWithMod(x)),
            Obj::Atom(AtomObj::IdentifierWithMod(y)),
        ) => x.identifier_id == y.identifier_id,
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

pub fn atomic_name_key(name: &AtomicName) -> String {
    match name {
        AtomicName::WithoutMod(name) => name.clone(),
        AtomicName::WithMod(module, name) => format!("{module}::{name}"),
    }
}

// Predicate-family key shared by a fact and its negation (e.g. both use `in`).
pub fn atomic_fact_key(fact: &AtomicFact) -> String {
    match fact {
        AtomicFact::NormalAtomicFact(f) => atomic_name_key(&f.predicate),
        AtomicFact::NotNormalAtomicFact(f) => atomic_name_key(&f.predicate),
        AtomicFact::EqualFact(_) | AtomicFact::NotEqualFact(_) => EQUAL.to_string(),
        AtomicFact::LessFact(_) | AtomicFact::NotLessFact(_) => LESS.to_string(),
        AtomicFact::GreaterFact(_) | AtomicFact::NotGreaterFact(_) => GREATER.to_string(),
        AtomicFact::LessEqualFact(_) | AtomicFact::NotLessEqualFact(_) => LESS_EQUAL.to_string(),
        AtomicFact::GreaterEqualFact(_) | AtomicFact::NotGreaterEqualFact(_) => {
            GREATER_EQUAL.to_string()
        }
        AtomicFact::IsSetFact(_) | AtomicFact::NotIsSetFact(_) => IS_SET.to_string(),
        AtomicFact::IsNonemptySetFact(_) | AtomicFact::NotIsNonemptySetFact(_) => {
            IS_NONEMPTY_SET.to_string()
        }
        AtomicFact::IsFiniteSetFact(_) | AtomicFact::NotIsFiniteSetFact(_) => {
            IS_FINITE_SET.to_string()
        }
        AtomicFact::InFact(_) | AtomicFact::NotInFact(_) => IN.to_string(),
        AtomicFact::IsCartFact(_) | AtomicFact::NotIsCartFact(_) => IS_CART.to_string(),
        AtomicFact::IsTupleFact(_) | AtomicFact::NotIsTupleFact(_) => IS_TUPLE.to_string(),
        AtomicFact::SubsetFact(_) | AtomicFact::NotSubsetFact(_) => SUBSET.to_string(),
        AtomicFact::SupersetFact(_) | AtomicFact::NotSupersetFact(_) => SUPERSET.to_string(),
        AtomicFact::FnEqualInFact(_) => FN_EQ_IN.to_string(),
        AtomicFact::FnEqualFact(_) => FN_EQ.to_string(),
    }
}

pub fn atomic_fact_has_positive_polarity(fact: &AtomicFact) -> bool {
    !matches!(
        fact,
        AtomicFact::NotNormalAtomicFact(_)
            | AtomicFact::NotEqualFact(_)
            | AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::NotIsSetFact(_)
            | AtomicFact::NotIsNonemptySetFact(_)
            | AtomicFact::NotIsFiniteSetFact(_)
            | AtomicFact::NotInFact(_)
            | AtomicFact::NotIsCartFact(_)
            | AtomicFact::NotIsTupleFact(_)
            | AtomicFact::NotSubsetFact(_)
            | AtomicFact::NotSupersetFact(_)
    )
}

pub fn atomic_fact_args_ref(fact: &AtomicFact) -> Vec<&Obj> {
    match fact {
        AtomicFact::NormalAtomicFact(f) => f.body.iter().collect(),
        AtomicFact::NotNormalAtomicFact(f) => f.body.iter().collect(),
        AtomicFact::EqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::LessFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotLessFact(f) => vec![&f.left, &f.right],
        AtomicFact::GreaterFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotGreaterFact(f) => vec![&f.left, &f.right],
        AtomicFact::LessEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotLessEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::GreaterEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotGreaterEqualFact(f) => vec![&f.left, &f.right],
        AtomicFact::IsSetFact(f) => vec![&f.set],
        AtomicFact::NotIsSetFact(f) => vec![&f.set],
        AtomicFact::IsNonemptySetFact(f) => vec![&f.set],
        AtomicFact::NotIsNonemptySetFact(f) => vec![&f.set],
        AtomicFact::IsFiniteSetFact(f) => vec![&f.set],
        AtomicFact::NotIsFiniteSetFact(f) => vec![&f.set],
        AtomicFact::InFact(f) => vec![&f.element, &f.set],
        AtomicFact::NotInFact(f) => vec![&f.element, &f.set],
        AtomicFact::IsCartFact(f) => vec![&f.set],
        AtomicFact::NotIsCartFact(f) => vec![&f.set],
        AtomicFact::IsTupleFact(f) => vec![&f.set],
        AtomicFact::NotIsTupleFact(f) => vec![&f.set],
        AtomicFact::SubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::SupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::FnEqualInFact(f) => vec![&f.left, &f.right, &f.set],
        AtomicFact::FnEqualFact(f) => vec![&f.left, &f.right],
    }
}
