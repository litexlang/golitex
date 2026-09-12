use crate::new_pipeline::ast::obj::{AtomObj, Obj};

pub fn ast_obj_eq(a: &Obj, b: &Obj) -> bool {
    match (a, b) {
        (Obj::Number(x), Obj::Number(y)) => x.normalized_value == y.normalized_value,
        (Obj::Atom(AtomObj::Identifier(x)), Obj::Atom(AtomObj::Identifier(y))) => x.name == y.name,
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
        _ => false,
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
