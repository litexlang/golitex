use crate::prelude::*;
use std::collections::HashSet;

pub fn nested_obj_binder_normalized_key<'a>(
    text: &str,
    objs: impl IntoIterator<Item = &'a Obj>,
) -> String {
    let mut bindings = Vec::new();
    let mut seen = HashSet::new();
    for obj in objs {
        collect_obj_binder_bindings(obj, &mut bindings, &mut seen, 0);
    }

    let mut normalized = text.to_string();
    for (binding, canonical) in &bindings {
        let original = format!("#{}#{}", binding.id().value(), binding.name());
        normalized = normalized.replace(&original, &canonical);
    }
    normalized
}

pub fn objs_equal_with_nested_binder_alpha_equivalence(left: &Obj, right: &Obj) -> bool {
    obj_equality_key(left) == obj_equality_key(right)
}

pub fn obj_equality_key(obj: &Obj) -> String {
    nested_obj_binder_normalized_key(&obj.to_string(), std::iter::once(obj))
}

fn collect_obj_binder_bindings(
    obj: &Obj,
    bindings: &mut Vec<(SymbolBinding, String)>,
    seen: &mut HashSet<SymbolId>,
    depth: usize,
) {
    match obj {
        Obj::Atom(_)
        | Obj::Number(_)
        | Obj::ImaginaryUnit(_)
        | Obj::EulerNumber(_)
        | Obj::Pi(_)
        | Obj::StandardSet(_) => {}
        Obj::FnObj(x) => {
            collect_fn_obj_head_binder_bindings(x.head.as_ref(), bindings, seen, depth);
            for group in &x.body {
                for arg in group {
                    collect_obj_binder_bindings(arg, bindings, seen, depth);
                }
            }
        }
        Obj::Add(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Sub(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Mul(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Div(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Mod(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Gcd(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Lcm(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Min(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Max(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Union(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Intersect(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::SetMinus(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::SetDiff(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::MatrixAdd(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::MatrixSub(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::MatrixMul(x) => collect_two(&x.left, &x.right, bindings, seen, depth),
        Obj::Pow(x) => collect_two(&x.base, &x.exponent, bindings, seen, depth),
        Obj::MatrixScalarMul(x) => collect_two(&x.scalar, &x.matrix, bindings, seen, depth),
        Obj::MatrixPow(x) => collect_two(&x.base, &x.exponent, bindings, seen, depth),
        Obj::Abs(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Floor(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Ceil(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Exp(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Ln(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Sign(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Factorial(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Sin(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Cos(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Tan(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Cot(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::RealPart(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::ImaginaryPart(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::ComplexAbs(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Sqrt(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::Log(x) => {
            collect_obj_binder_bindings(&x.base, bindings, seen, depth);
            collect_obj_binder_bindings(&x.arg, bindings, seen, depth);
        }
        Obj::BigUnion(x) => collect_obj_binder_bindings(&x.left, bindings, seen, depth),
        Obj::BigIntersect(x) => collect_obj_binder_bindings(&x.left, bindings, seen, depth),
        Obj::PowerSet(x) => collect_obj_binder_bindings(&x.set, bindings, seen, depth),
        Obj::SeqSet(x) => collect_obj_binder_bindings(&x.set, bindings, seen, depth),
        Obj::FiniteSetSize(x) => collect_obj_binder_bindings(&x.set, bindings, seen, depth),
        Obj::FiniteSetMax(x) => collect_obj_binder_bindings(&x.set, bindings, seen, depth),
        Obj::FiniteSetMin(x) => collect_obj_binder_bindings(&x.set, bindings, seen, depth),
        Obj::FnRange(x) => collect_obj_binder_bindings(&x.function, bindings, seen, depth),
        Obj::TupleDim(x) => collect_obj_binder_bindings(&x.arg, bindings, seen, depth),
        Obj::CartDim(x) => collect_obj_binder_bindings(&x.set, bindings, seen, depth),
        Obj::Proj(x) => {
            collect_obj_binder_bindings(&x.set, bindings, seen, depth);
            collect_obj_binder_bindings(&x.dim, bindings, seen, depth);
        }
        Obj::ListSet(x) => {
            for value in &x.list {
                collect_obj_binder_bindings(value, bindings, seen, depth);
            }
        }
        Obj::SetBuilder(x) => {
            push_binding(&x.param_binding, bindings, seen, depth, 0);
            collect_obj_binder_bindings(&x.param_set, bindings, seen, depth);
            for fact in &x.facts {
                for arg in fact.get_args_from_fact_ref() {
                    collect_obj_binder_bindings(arg, bindings, seen, depth + 1);
                }
            }
        }
        Obj::FnSet(x) => collect_fn_set_body_binder_bindings(&x.body, bindings, seen, depth),
        Obj::AnonymousFn(x) => {
            collect_fn_set_body_binder_bindings(&x.body, bindings, seen, depth);
            collect_obj_binder_bindings(&x.equal_to, bindings, seen, depth + 1);
        }
        Obj::Cart(x) => {
            for value in &x.args {
                collect_obj_binder_bindings(value, bindings, seen, depth);
            }
        }
        Obj::Tuple(x) => {
            for value in &x.args {
                collect_obj_binder_bindings(value, bindings, seen, depth);
            }
        }
        Obj::GeneralCart(x) => {
            collect_obj_binder_bindings(&x.index_set, bindings, seen, depth);
            collect_obj_binder_bindings(&x.family_set, bindings, seen, depth);
            collect_obj_binder_bindings(&x.family_fn, bindings, seen, depth);
        }
        Obj::Sum(x) => {
            collect_obj_binder_bindings(&x.start, bindings, seen, depth);
            collect_obj_binder_bindings(&x.end, bindings, seen, depth);
            collect_obj_binder_bindings(&x.func, bindings, seen, depth);
        }
        Obj::Product(x) => {
            collect_obj_binder_bindings(&x.start, bindings, seen, depth);
            collect_obj_binder_bindings(&x.end, bindings, seen, depth);
            collect_obj_binder_bindings(&x.func, bindings, seen, depth);
        }
        Obj::SumOfFiniteSet(x) => {
            collect_obj_binder_bindings(&x.set, bindings, seen, depth);
            collect_obj_binder_bindings(&x.func, bindings, seen, depth);
        }
        Obj::ProductOfFiniteSet(x) => {
            collect_obj_binder_bindings(&x.set, bindings, seen, depth);
            collect_obj_binder_bindings(&x.func, bindings, seen, depth);
        }
        Obj::Range(x) => {
            collect_obj_binder_bindings(&x.start, bindings, seen, depth);
            collect_obj_binder_bindings(&x.end, bindings, seen, depth);
        }
        Obj::ClosedRange(x) => {
            collect_obj_binder_bindings(&x.start, bindings, seen, depth);
            collect_obj_binder_bindings(&x.end, bindings, seen, depth);
        }
        Obj::FiniteSeqSet(x) => {
            collect_obj_binder_bindings(&x.set, bindings, seen, depth);
            collect_obj_binder_bindings(&x.n, bindings, seen, depth);
        }
        Obj::FiniteSeqListObj(x) => {
            for value in &x.objs {
                collect_obj_binder_bindings(value, bindings, seen, depth);
            }
        }
        Obj::MatrixSet(x) => {
            collect_obj_binder_bindings(&x.set, bindings, seen, depth);
            collect_obj_binder_bindings(&x.row_len, bindings, seen, depth);
            collect_obj_binder_bindings(&x.col_len, bindings, seen, depth);
        }
        Obj::MatrixListObj(x) => {
            for row in &x.rows {
                for value in row {
                    collect_obj_binder_bindings(value, bindings, seen, depth);
                }
            }
        }
        Obj::ObjAtIndex(x) => {
            collect_obj_binder_bindings(&x.obj, bindings, seen, depth);
            collect_obj_binder_bindings(&x.index, bindings, seen, depth);
        }
        Obj::StructObj(x) => {
            for param in &x.params {
                collect_obj_binder_bindings(param, bindings, seen, depth);
            }
        }
        Obj::ObjAsStructInstanceWithFieldAccess(x) => {
            for param in &x.struct_obj.params {
                collect_obj_binder_bindings(param, bindings, seen, depth);
            }
            collect_obj_binder_bindings(&x.obj, bindings, seen, depth);
        }
        Obj::InstantiatedTemplateObj(x) => {
            for arg in &x.args {
                collect_obj_binder_bindings(arg, bindings, seen, depth);
            }
        }
        Obj::OneSideInfinityIntervalObj(x) => {
            collect_obj_binder_bindings(x.start(), bindings, seen, depth);
        }
        Obj::IntervalObj(x) => {
            collect_obj_binder_bindings(x.start(), bindings, seen, depth);
            collect_obj_binder_bindings(x.end(), bindings, seen, depth);
        }
        Obj::Replacement(x) => {
            collect_obj_binder_bindings(&x.source_set, bindings, seen, depth);
        }
    }
}

fn collect_fn_set_body_binder_bindings(
    body: &FnSetBody,
    bindings: &mut Vec<(SymbolBinding, String)>,
    seen: &mut HashSet<SymbolId>,
    depth: usize,
) {
    let mut position = 0;
    for group in body.params_def_with_set.iter() {
        for binding in &group.params {
            push_binding(binding, bindings, seen, depth, position);
            position += 1;
        }
        collect_obj_binder_bindings(group.set_obj(), bindings, seen, depth + 1);
    }
    for fact in &body.dom_facts {
        for arg in fact.get_args_from_fact_ref() {
            collect_obj_binder_bindings(arg, bindings, seen, depth + 1);
        }
    }
    collect_obj_binder_bindings(&body.ret_set, bindings, seen, depth + 1);
}

fn collect_two(
    left: &Obj,
    right: &Obj,
    bindings: &mut Vec<(SymbolBinding, String)>,
    seen: &mut HashSet<SymbolId>,
    depth: usize,
) {
    collect_obj_binder_bindings(left, bindings, seen, depth);
    collect_obj_binder_bindings(right, bindings, seen, depth);
}

fn collect_fn_obj_head_binder_bindings(
    head: &FnObjHead,
    bindings: &mut Vec<(SymbolBinding, String)>,
    seen: &mut HashSet<SymbolId>,
    depth: usize,
) {
    match head {
        FnObjHead::AnonymousFnLiteral(x) => {
            collect_fn_set_body_binder_bindings(&x.body, bindings, seen, depth);
            collect_obj_binder_bindings(&x.equal_to, bindings, seen, depth + 1);
        }
        FnObjHead::FiniteSeqListObj(x) => {
            for value in &x.objs {
                collect_obj_binder_bindings(value, bindings, seen, depth);
            }
        }
        FnObjHead::ObjAtIndex(x) => {
            collect_obj_binder_bindings(&x.obj, bindings, seen, depth);
            collect_obj_binder_bindings(&x.index, bindings, seen, depth);
        }
        FnObjHead::ObjAsStructInstanceWithFieldAccess(x) => {
            for param in &x.struct_obj.params {
                collect_obj_binder_bindings(param, bindings, seen, depth);
            }
            collect_obj_binder_bindings(&x.obj, bindings, seen, depth);
        }
        FnObjHead::InstantiatedTemplateObj(x) => {
            for arg in &x.args {
                collect_obj_binder_bindings(arg, bindings, seen, depth);
            }
        }
        FnObjHead::MatrixOperator(x) => collect_obj_binder_bindings(x, bindings, seen, depth),
        FnObjHead::Identifier(_)
        | FnObjHead::IdentifierWithMod(_)
        | FnObjHead::Forall(_)
        | FnObjHead::DefHeader(_)
        | FnObjHead::Exist(_)
        | FnObjHead::SetBuilder(_)
        | FnObjHead::FnSet(_)
        | FnObjHead::DefStructField(_)
        | FnObjHead::Induc(_)
        | FnObjHead::DefAlgo(_)
        | FnObjHead::TupleIndex(_)
        | FnObjHead::CartIndex(_) => {}
    }
}

fn push_binding(
    binding: &SymbolBinding,
    bindings: &mut Vec<(SymbolBinding, String)>,
    seen: &mut HashSet<SymbolId>,
    depth: usize,
    position: usize,
) {
    if seen.insert(binding.id()) {
        bindings.push((
            binding.clone(),
            format!("#alpha_obj_{}_{}#", depth, position),
        ));
    }
}
