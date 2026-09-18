use crate::new_pipeline::ast::obj::{
    Abs, Add, Ceil, Cos, Div, Exp, Factorial, Floor, FnObj, FnObjHead, Gcd, IntervalObj, Lcm, Ln,
    Max, Min, Mod, Mul, Obj, OneSideInfinityIntervalObj, Pow, Quot, Sign, Sin, Sqrt, Sub, Tan,
};
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;

// Same-shape child pairs for MatchingOneArgByOne (legacy same_shape peel).
// None = different constructors / unsupported shape / binder-carrying shape.
// Empty Vec = no children (should not succeed Matching; caller treats as miss).
//
// Covered: numeric ops, FnObj application layers, sets/tuples/carts, ranges,
// sums/products/reduces, struct params / field access, ObjAtIndex, etc.
// Not covered (intentional): Identifier/Number/StandardSet leaves; SetBuilder /
// AnonymousFn / FnSet (binders); InstantiatedTemplateObj (legacy also skips).
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
    macro_rules! slice_pairs {
        ($l:expr, $r:expr) => {{
            if $l.len() != $r.len() {
                return None;
            }
            Some(
                $l.iter()
                    .zip($r.iter())
                    .map(|(a, b)| (a.as_ref().clone(), b.as_ref().clone()))
                    .collect(),
            )
        }};
    }
    macro_rules! obj_slice_pairs {
        ($l:expr, $r:expr) => {{
            if $l.len() != $r.len() {
                return None;
            }
            Some(
                $l.iter()
                    .zip($r.iter())
                    .map(|(a, b)| (a.clone(), b.clone()))
                    .collect(),
            )
        }};
    }

    match (left, right) {
        (Obj::FnObj(l), Obj::FnObj(r)) => fn_obj_corresponding_arg_pairs(l, r),

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

        (Obj::Union(l), Obj::Union(r)) => binary!(l, r),
        (Obj::Intersect(l), Obj::Intersect(r)) => binary!(l, r),
        (Obj::SetMinus(l), Obj::SetMinus(r)) => binary!(l, r),
        (Obj::BigUnion(l), Obj::BigUnion(r)) => {
            Some(vec![(l.left.as_ref().clone(), r.left.as_ref().clone())])
        }
        (Obj::BigIntersect(l), Obj::BigIntersect(r)) => {
            Some(vec![(l.left.as_ref().clone(), r.left.as_ref().clone())])
        }
        (Obj::PowerSet(l), Obj::PowerSet(r)) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::CartDim(l), Obj::CartDim(r)) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::TupleDim(l), Obj::TupleDim(r)) => unary!(l, r),
        (Obj::FiniteSetSize(l), Obj::FiniteSetSize(r)) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::FiniteSetMax(l), Obj::FiniteSetMax(r)) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::FiniteSetMin(l), Obj::FiniteSetMin(r)) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::FnRange(l), Obj::FnRange(r)) => Some(vec![
            (l.function.as_ref().clone(), r.function.as_ref().clone()),
        ]),
        (Obj::Replacement(l), Obj::Replacement(r)) => {
            if l.prop_name.to_string() != r.prop_name.to_string() {
                return None;
            }
            Some(vec![
                (l.source_set.as_ref().clone(), r.source_set.as_ref().clone()),
            ])
        }
        (Obj::Range(l), Obj::Range(r)) => Some(vec![
            (l.start.as_ref().clone(), r.start.as_ref().clone()),
            (l.end.as_ref().clone(), r.end.as_ref().clone()),
        ]),
        (Obj::ClosedRange(l), Obj::ClosedRange(r)) => Some(vec![
            (l.start.as_ref().clone(), r.start.as_ref().clone()),
            (l.end.as_ref().clone(), r.end.as_ref().clone()),
        ]),
        (Obj::Sum(l), Obj::Sum(r)) => Some(vec![
            (l.start.as_ref().clone(), r.start.as_ref().clone()),
            (l.end.as_ref().clone(), r.end.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
        ]),
        (Obj::SumOfFiniteSet(l), Obj::SumOfFiniteSet(r)) => Some(vec![
            (l.set.as_ref().clone(), r.set.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
        ]),
        (Obj::Product(l), Obj::Product(r)) => Some(vec![
            (l.start.as_ref().clone(), r.start.as_ref().clone()),
            (l.end.as_ref().clone(), r.end.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
        ]),
        (Obj::ProductOfFiniteSet(l), Obj::ProductOfFiniteSet(r)) => Some(vec![
            (l.set.as_ref().clone(), r.set.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
        ]),
        (Obj::Reduce(l), Obj::Reduce(r)) => Some(vec![
            (l.start.as_ref().clone(), r.start.as_ref().clone()),
            (l.end.as_ref().clone(), r.end.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
            (l.op.as_ref().clone(), r.op.as_ref().clone()),
            (l.seed.as_ref().clone(), r.seed.as_ref().clone()),
        ]),
        (Obj::FiniteSetReduce(l), Obj::FiniteSetReduce(r)) => Some(vec![
            (l.set.as_ref().clone(), r.set.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
            (l.op.as_ref().clone(), r.op.as_ref().clone()),
            (l.seed.as_ref().clone(), r.seed.as_ref().clone()),
        ]),
        (Obj::IntervalObj(l), Obj::IntervalObj(r)) => interval_obj_pairs(l, r),
        (Obj::OneSideInfinityIntervalObj(l), Obj::OneSideInfinityIntervalObj(r)) => {
            one_side_interval_pairs(l, r)
        }
        (Obj::FiniteSeqSet(l), Obj::FiniteSeqSet(r)) => Some(vec![
            (l.set.as_ref().clone(), r.set.as_ref().clone()),
            (l.n.as_ref().clone(), r.n.as_ref().clone()),
        ]),
        (Obj::SeqSet(l), Obj::SeqSet(r)) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::FiniteSeqListObj(l), Obj::FiniteSeqListObj(r)) => slice_pairs!(l.objs, r.objs),
        (Obj::Proj(l), Obj::Proj(r)) => Some(vec![
            (l.set.as_ref().clone(), r.set.as_ref().clone()),
            (l.dim.as_ref().clone(), r.dim.as_ref().clone()),
        ]),
        (Obj::ObjAtIndex(l), Obj::ObjAtIndex(r)) => Some(vec![
            (l.obj.as_ref().clone(), r.obj.as_ref().clone()),
            (l.index.as_ref().clone(), r.index.as_ref().clone()),
        ]),
        (Obj::Tuple(l), Obj::Tuple(r)) => slice_pairs!(l.args, r.args),
        (Obj::ListSet(l), Obj::ListSet(r)) => slice_pairs!(l.list, r.list),
        (Obj::Cart(l), Obj::Cart(r)) => slice_pairs!(l.args, r.args),
        (Obj::GeneralCart(l), Obj::GeneralCart(r)) => Some(vec![
            (l.index_set.as_ref().clone(), r.index_set.as_ref().clone()),
            (l.family_set.as_ref().clone(), r.family_set.as_ref().clone()),
            (l.family_fn.as_ref().clone(), r.family_fn.as_ref().clone()),
        ]),
        (Obj::IndexUnion(l), Obj::IndexUnion(r)) => Some(vec![
            (l.index_set.as_ref().clone(), r.index_set.as_ref().clone()),
            (l.ambient_set.as_ref().clone(), r.ambient_set.as_ref().clone()),
            (l.family_fn.as_ref().clone(), r.family_fn.as_ref().clone()),
        ]),
        (Obj::IndexIntersect(l), Obj::IndexIntersect(r)) => Some(vec![
            (l.index_set.as_ref().clone(), r.index_set.as_ref().clone()),
            (l.ambient_set.as_ref().clone(), r.ambient_set.as_ref().clone()),
            (l.family_fn.as_ref().clone(), r.family_fn.as_ref().clone()),
        ]),
        (Obj::StructObj(l), Obj::StructObj(r)) => {
            if l.name.to_string() != r.name.to_string() {
                return None;
            }
            obj_slice_pairs!(l.params, r.params)
        }
        (
            Obj::ObjAsStructInstanceWithFieldAccess(l),
            Obj::ObjAsStructInstanceWithFieldAccess(r),
        ) => {
            if l.field_name != r.field_name {
                return None;
            }
            Some(vec![(l.obj.as_ref().clone(), r.obj.as_ref().clone())])
        }

        // Leaves / binders / templates: no constructor peel.
        _ => None,
    }
}

// Replace every subtree whose IR equals `from_ir` with `to` (top-down).
// Owned by ClosedNumericEqualSubstitution only — not a global resolve_obj,
// and not a general known-equality congruence rewrite.
pub(crate) fn replace_obj_matching_ir(obj: &Obj, from_ir: &ObjIR, to: &Obj) -> Obj {
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
        Obj::Mod(a) => Obj::Mod(Mod {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Quot(a) => Obj::Quot(Quot {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Gcd(a) => Obj::Gcd(Gcd {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Lcm(a) => Obj::Lcm(Lcm {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Min(a) => Obj::Min(Min {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        }),
        Obj::Max(a) => Obj::Max(Max {
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

fn fn_obj_corresponding_arg_pairs(left: &FnObj, right: &FnObj) -> Option<Vec<(Obj, Obj)>> {
    // Legacy: peel shared suffix application groups, then compare prefixes.
    // Flatten into one certificate: outermost-group args first, then prefix.
    let mut left_group_count = left.body.len();
    let mut right_group_count = right.body.len();
    let mut pairs = Vec::new();
    let mut peeled = false;
    while left_group_count > 0 && right_group_count > 0 {
        let left_group = &left.body[left_group_count - 1];
        let right_group = &right.body[right_group_count - 1];
        if left_group.len() != right_group.len() {
            return None;
        }
        for (l_arg, r_arg) in left_group.iter().zip(right_group.iter()) {
            pairs.push((l_arg.as_ref().clone(), r_arg.as_ref().clone()));
        }
        left_group_count -= 1;
        right_group_count -= 1;
        peeled = true;
    }
    if !peeled {
        return None;
    }
    pairs.push((
        fn_obj_prefix_obj(left, left_group_count),
        fn_obj_prefix_obj(right, right_group_count),
    ));
    Some(pairs)
}

fn fn_obj_prefix_obj(fo: &FnObj, groups_to_keep: usize) -> Obj {
    if groups_to_keep == 0 {
        return fn_obj_head_as_obj(fo.head.as_ref());
    }
    Obj::FnObj(FnObj {
        head: fo.head.clone(),
        body: fo.body[..groups_to_keep].to_vec(),
    })
}

fn fn_obj_head_as_obj(head: &FnObjHead) -> Obj {
    match head {
        FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
        FnObjHead::AnonymousFnLiteral(a) => Obj::AnonymousFn(a.as_ref().clone()),
        FnObjHead::FiniteSeqListObj(v) => Obj::FiniteSeqListObj(v.clone()),
        FnObjHead::ObjAtIndex(v) => Obj::ObjAtIndex(v.clone()),
        FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => {
            Obj::ObjAsStructInstanceWithFieldAccess(v.clone())
        }
        FnObjHead::InstantiatedTemplateObj(v) => Obj::InstantiatedTemplateObj(v.clone()),
    }
}

fn interval_obj_pairs(left: &IntervalObj, right: &IntervalObj) -> Option<Vec<(Obj, Obj)>> {
    use IntervalObj::*;
    let (l, r) = match (left, right) {
        (LeftOpenRightOpen(l), LeftOpenRightOpen(r))
        | (LeftOpenRightClosed(l), LeftOpenRightClosed(r))
        | (LeftClosedRightOpen(l), LeftClosedRightOpen(r))
        | (LeftClosedRightClosed(l), LeftClosedRightClosed(r)) => (l, r),
        _ => return None,
    };
    Some(vec![
        (l.start.as_ref().clone(), r.start.as_ref().clone()),
        (l.end.as_ref().clone(), r.end.as_ref().clone()),
    ])
}

fn one_side_interval_pairs(
    left: &OneSideInfinityIntervalObj,
    right: &OneSideInfinityIntervalObj,
) -> Option<Vec<(Obj, Obj)>> {
    use OneSideInfinityIntervalObj::*;
    let (l, r) = match (left, right) {
        (LeftOpen(l), LeftOpen(r))
        | (LeftClosed(l), LeftClosed(r))
        | (RightOpen(l), RightOpen(r))
        | (RightClosed(l), RightClosed(r)) => (l, r),
        _ => return None,
    };
    Some(vec![(l.start.as_ref().clone(), r.start.as_ref().clone())])
}
