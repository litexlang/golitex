use crate::new_pipeline::ast::obj::{FnObj, FnObjHead, IdentifierObj, Literal, Obj, Number};
use crate::new_pipeline::ast::stmt::DefAlgoStmt;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use std::collections::HashSet;

pub const MAX_EVAL_DEPTH: usize = 64;

pub fn is_number_literal(obj: &Obj) -> bool {
    matches!(obj, Obj::Literal(Literal::Number(_)))
}

pub fn number_literal_key(obj: &Obj) -> Option<String> {
    match obj {
        Obj::Literal(Literal::Number(Number { normalized_value })) => {
            Some(normalized_value.clone())
        }
        _ => None,
    }
}

pub fn fn_obj_plain_name(fn_obj: &FnObj) -> Option<String> {
    match fn_obj.head.as_ref() {
        FnObjHead::Identifier(IdentifierObj::Plain { name, .. }) => Some(name.clone()),
        _ => None,
    }
}

pub fn flatten_fn_obj_args(fn_obj: &FnObj) -> Vec<Obj> {
    let mut out = Vec::new();
    for group in &fn_obj.body {
        for arg in group {
            out.push(arg.as_ref().clone());
        }
    }
    out
}

pub fn algo_call_key(fn_name: &str, evaluated_args: &[Obj]) -> Option<String> {
    let mut parts = Vec::with_capacity(evaluated_args.len());
    for arg in evaluated_args {
        parts.push(number_literal_key(arg)?);
    }
    Some(format!("{fn_name}({})", parts.join(",")))
}

pub fn build_algo_param_subst(
    algo: &DefAlgoStmt,
    evaluated_args: &[Obj],
) -> Option<std::collections::HashMap<IdentifierId, Obj>> {
    if algo.param_bindings.len() != evaluated_args.len() {
        return None;
    }
    let mut map = std::collections::HashMap::new();
    for (name, arg) in algo.param_bindings.iter().zip(evaluated_args.iter()) {
        let id = find_plain_id_in_algo_stmt(algo, name)?;
        map.insert(id, arg.clone());
    }
    Some(map)
}

fn find_plain_id_in_algo_stmt(stmt: &DefAlgoStmt, name: &str) -> Option<IdentifierId> {
    use crate::new_pipeline::ast::fact::atomic_fact_args_ref;
    for case in &stmt.cases {
        for obj in atomic_fact_args_ref(&case.condition) {
            if let Some(id) = find_plain_id_in_obj(obj, name) {
                return Some(id);
            }
        }
        if let Some(id) = find_plain_id_in_obj(&case.return_stmt.value, name) {
            return Some(id);
        }
    }
    if let Some(default) = &stmt.default_return {
        if let Some(id) = find_plain_id_in_obj(&default.value, name) {
            return Some(id);
        }
    }
    None
}

fn find_plain_id_in_obj(obj: &Obj, name: &str) -> Option<IdentifierId> {
    match obj {
        Obj::Identifier(IdentifierObj::Plain { id, name: n }) if n == name => Some(*id),
        Obj::FnObj(f) => {
            for group in &f.body {
                for arg in group {
                    if let Some(id) = find_plain_id_in_obj(arg, name) {
                        return Some(id);
                    }
                }
            }
            None
        }
        Obj::ArithmeticOperator(op) => {
            use crate::new_pipeline::ast::obj::ArithmeticOperator::*;
            let kids: Vec<&Obj> = match op {
                Add(a) | Sub(a) | Mul(a) | Div(a) | Min(a) | Max(a) => {
                    vec![a.left.as_ref(), a.right.as_ref()]
                }
                Neg(a) | Abs(a) | Floor(a) | Ceil(a) | Sign(a) => vec![a.arg.as_ref()],
                Pow(a) => vec![a.base.as_ref(), a.exponent.as_ref()],
            };
            for kid in kids {
                if let Some(id) = find_plain_id_in_obj(kid, name) {
                    return Some(id);
                }
            }
            None
        }
        _ => None,
    }
}

pub type ActiveAlgoCalls = HashSet<String>;
