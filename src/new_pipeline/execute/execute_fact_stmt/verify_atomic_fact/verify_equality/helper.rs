use crate::new_pipeline::ast::obj::{Abs, Add, Arccos, Arccot, Arcsin, Arctan, Ceil, Cos, Cot, Div, Exp, Factorial, Floor, FnObj, FnObjHead, Gcd, IntervalObj, Lcm, Ln, Max, Min, Mod, Mul, Neg, Obj, OneSideInfinityIntervalObj, Pow, Quot, Sign, Sin, Sqrt, Sub, Tan, ArithmeticOperator, ComplexOperator, ExpLogOperator, FiniteSetStat, FunctionSpace, IntegerOperator, IteratedOperator, ProductShape, SetFormer, SetOperator, StructAndFieldAccessObj, TrigOperator};
use crate::new_pipeline::exec_env::known_fact_memory::ObjIR;

// Same-shape child pairs for MatchingOneArgByOne (legacy same_shape peel).
// None = different constructors / unsupported shape / binder-carrying shape.
// Empty Vec = no children (should not succeed Matching; caller treats as miss).
//
// Covered: numeric ops, FnObj application layers, sets/tuples/carts, ranges,
// sums/products/reduces, struct params / field access, ObjAtIndex, etc.
// Not covered (intentional): Identifier/Number/StandardSet leaves; SetBuilder /
// AnonymousFn / FnSet (binders); InstantiatedTemplateObj (legacy also skips).
pub(crate) fn corresponding_arg_pairs(left: &Obj, right: &Obj) -> Option<Vec<(Obj, Obj)>> {
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

        (Obj::ArithmeticOperator(ArithmeticOperator::Add(l)), Obj::ArithmeticOperator(ArithmeticOperator::Add(r))) => binary!(l, r),
        (Obj::ArithmeticOperator(ArithmeticOperator::Sub(l)), Obj::ArithmeticOperator(ArithmeticOperator::Sub(r))) => binary!(l, r),
        (Obj::ArithmeticOperator(ArithmeticOperator::Neg(l)), Obj::ArithmeticOperator(ArithmeticOperator::Neg(r))) => unary!(l, r),
        (Obj::ArithmeticOperator(ArithmeticOperator::Mul(l)), Obj::ArithmeticOperator(ArithmeticOperator::Mul(r))) => binary!(l, r),
        (Obj::ArithmeticOperator(ArithmeticOperator::Div(l)), Obj::ArithmeticOperator(ArithmeticOperator::Div(r))) => binary!(l, r),
        (Obj::IntegerOperator(IntegerOperator::Mod(l)), Obj::IntegerOperator(IntegerOperator::Mod(r))) => binary!(l, r),
        (Obj::IntegerOperator(IntegerOperator::Quot(l)), Obj::IntegerOperator(IntegerOperator::Quot(r))) => binary!(l, r),
        (Obj::IntegerOperator(IntegerOperator::Gcd(l)), Obj::IntegerOperator(IntegerOperator::Gcd(r))) => binary!(l, r),
        (Obj::IntegerOperator(IntegerOperator::Lcm(l)), Obj::IntegerOperator(IntegerOperator::Lcm(r))) => binary!(l, r),
        (Obj::ArithmeticOperator(ArithmeticOperator::Min(l)), Obj::ArithmeticOperator(ArithmeticOperator::Min(r))) => binary!(l, r),
        (Obj::ArithmeticOperator(ArithmeticOperator::Max(l)), Obj::ArithmeticOperator(ArithmeticOperator::Max(r))) => binary!(l, r),
        (Obj::ArithmeticOperator(ArithmeticOperator::Pow(l)), Obj::ArithmeticOperator(ArithmeticOperator::Pow(r))) => Some(vec![
            (l.base.as_ref().clone(), r.base.as_ref().clone()),
            (l.exponent.as_ref().clone(), r.exponent.as_ref().clone()),
        ]),
        (Obj::ExpLogOperator(ExpLogOperator::Log(l)), Obj::ExpLogOperator(ExpLogOperator::Log(r))) => Some(vec![
            (l.base.as_ref().clone(), r.base.as_ref().clone()),
            (l.arg.as_ref().clone(), r.arg.as_ref().clone()),
        ]),
        (Obj::ArithmeticOperator(ArithmeticOperator::Abs(l)), Obj::ArithmeticOperator(ArithmeticOperator::Abs(r))) => unary!(l, r),
        (Obj::ArithmeticOperator(ArithmeticOperator::Floor(l)), Obj::ArithmeticOperator(ArithmeticOperator::Floor(r))) => unary!(l, r),
        (Obj::ArithmeticOperator(ArithmeticOperator::Ceil(l)), Obj::ArithmeticOperator(ArithmeticOperator::Ceil(r))) => unary!(l, r),
        (Obj::ExpLogOperator(ExpLogOperator::Exp(l)), Obj::ExpLogOperator(ExpLogOperator::Exp(r))) => unary!(l, r),
        (Obj::ExpLogOperator(ExpLogOperator::Ln(l)), Obj::ExpLogOperator(ExpLogOperator::Ln(r))) => unary!(l, r),
        (Obj::ArithmeticOperator(ArithmeticOperator::Sign(l)), Obj::ArithmeticOperator(ArithmeticOperator::Sign(r))) => unary!(l, r),
        (Obj::IntegerOperator(IntegerOperator::Factorial(l)), Obj::IntegerOperator(IntegerOperator::Factorial(r))) => unary!(l, r),
        (Obj::ExpLogOperator(ExpLogOperator::Sqrt(l)), Obj::ExpLogOperator(ExpLogOperator::Sqrt(r))) => unary!(l, r),
        (Obj::TrigOperator(TrigOperator::Sin(l)), Obj::TrigOperator(TrigOperator::Sin(r))) => unary!(l, r),
        (Obj::TrigOperator(TrigOperator::Cos(l)), Obj::TrigOperator(TrigOperator::Cos(r))) => unary!(l, r),
        (Obj::TrigOperator(TrigOperator::Tan(l)), Obj::TrigOperator(TrigOperator::Tan(r))) => unary!(l, r),
        (Obj::TrigOperator(TrigOperator::Cot(l)), Obj::TrigOperator(TrigOperator::Cot(r))) => unary!(l, r),
        (Obj::TrigOperator(TrigOperator::Arcsin(l)), Obj::TrigOperator(TrigOperator::Arcsin(r))) => unary!(l, r),
        (Obj::TrigOperator(TrigOperator::Arccos(l)), Obj::TrigOperator(TrigOperator::Arccos(r))) => unary!(l, r),
        (Obj::TrigOperator(TrigOperator::Arctan(l)), Obj::TrigOperator(TrigOperator::Arctan(r))) => unary!(l, r),
        (Obj::TrigOperator(TrigOperator::Arccot(l)), Obj::TrigOperator(TrigOperator::Arccot(r))) => unary!(l, r),
        (Obj::ComplexOperator(ComplexOperator::RealPart(l)), Obj::ComplexOperator(ComplexOperator::RealPart(r))) => unary!(l, r),
        (Obj::ComplexOperator(ComplexOperator::ImaginaryPart(l)), Obj::ComplexOperator(ComplexOperator::ImaginaryPart(r))) => unary!(l, r),
        (Obj::ComplexOperator(ComplexOperator::ComplexAbs(l)), Obj::ComplexOperator(ComplexOperator::ComplexAbs(r))) => unary!(l, r),

        (Obj::SetOperator(SetOperator::Union(l)), Obj::SetOperator(SetOperator::Union(r))) => binary!(l, r),
        (Obj::SetOperator(SetOperator::Intersect(l)), Obj::SetOperator(SetOperator::Intersect(r))) => binary!(l, r),
        (Obj::SetOperator(SetOperator::SetMinus(l)), Obj::SetOperator(SetOperator::SetMinus(r))) => binary!(l, r),
        (Obj::SetOperator(SetOperator::FamilyUnion(l)), Obj::SetOperator(SetOperator::FamilyUnion(r))) => {
            Some(vec![(l.left.as_ref().clone(), r.left.as_ref().clone())])
        }
        (Obj::SetOperator(SetOperator::FamilyIntersect(l)), Obj::SetOperator(SetOperator::FamilyIntersect(r))) => {
            Some(vec![(l.left.as_ref().clone(), r.left.as_ref().clone())])
        }
        (Obj::SetOperator(SetOperator::PowerSet(l)), Obj::SetOperator(SetOperator::PowerSet(r))) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::ProductShape(ProductShape::CartDim(l)), Obj::ProductShape(ProductShape::CartDim(r))) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::ProductShape(ProductShape::TupleDim(l)), Obj::ProductShape(ProductShape::TupleDim(r))) => unary!(l, r),
        (Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(l)), Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(r))) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(l)), Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(r))) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(l)), Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(r))) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::FunctionSpace(FunctionSpace::FnRange(l)), Obj::FunctionSpace(FunctionSpace::FnRange(r))) => Some(vec![
            (l.function.as_ref().clone(), r.function.as_ref().clone()),
        ]),
        (Obj::SetFormer(SetFormer::Range(l)), Obj::SetFormer(SetFormer::Range(r))) => Some(vec![
            (l.start.as_ref().clone(), r.start.as_ref().clone()),
            (l.end.as_ref().clone(), r.end.as_ref().clone()),
        ]),
        (Obj::SetFormer(SetFormer::ClosedRange(l)), Obj::SetFormer(SetFormer::ClosedRange(r))) => Some(vec![
            (l.start.as_ref().clone(), r.start.as_ref().clone()),
            (l.end.as_ref().clone(), r.end.as_ref().clone()),
        ]),
        (Obj::IteratedOperator(IteratedOperator::Sum(l)), Obj::IteratedOperator(IteratedOperator::Sum(r))) => Some(vec![
            (l.start.as_ref().clone(), r.start.as_ref().clone()),
            (l.end.as_ref().clone(), r.end.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
        ]),
        (Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(l)), Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(r))) => Some(vec![
            (l.set.as_ref().clone(), r.set.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
        ]),
        (Obj::IteratedOperator(IteratedOperator::Product(l)), Obj::IteratedOperator(IteratedOperator::Product(r))) => Some(vec![
            (l.start.as_ref().clone(), r.start.as_ref().clone()),
            (l.end.as_ref().clone(), r.end.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
        ]),
        (Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(l)), Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(r))) => Some(vec![
            (l.set.as_ref().clone(), r.set.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
        ]),
        (Obj::IteratedOperator(IteratedOperator::Reduce(l)), Obj::IteratedOperator(IteratedOperator::Reduce(r))) => Some(vec![
            (l.start.as_ref().clone(), r.start.as_ref().clone()),
            (l.end.as_ref().clone(), r.end.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
            (l.op.as_ref().clone(), r.op.as_ref().clone()),
            (l.seed.as_ref().clone(), r.seed.as_ref().clone()),
        ]),
        (Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(l)), Obj::IteratedOperator(IteratedOperator::FiniteSetReduce(r))) => Some(vec![
            (l.set.as_ref().clone(), r.set.as_ref().clone()),
            (l.func.as_ref().clone(), r.func.as_ref().clone()),
            (l.op.as_ref().clone(), r.op.as_ref().clone()),
            (l.seed.as_ref().clone(), r.seed.as_ref().clone()),
        ]),
        (Obj::SetFormer(SetFormer::IntervalObj(l)), Obj::SetFormer(SetFormer::IntervalObj(r))) => interval_obj_pairs(l, r),
        (Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(l)), Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(r))) => {
            one_side_interval_pairs(l, r)
        }
        (Obj::SetFormer(SetFormer::FiniteSeqSet(l)), Obj::SetFormer(SetFormer::FiniteSeqSet(r))) => Some(vec![
            (l.set.as_ref().clone(), r.set.as_ref().clone()),
            (l.n.as_ref().clone(), r.n.as_ref().clone()),
        ]),
        (Obj::SetFormer(SetFormer::SeqSet(l)), Obj::SetFormer(SetFormer::SeqSet(r))) => {
            Some(vec![(l.set.as_ref().clone(), r.set.as_ref().clone())])
        }
        (Obj::ProductShape(ProductShape::Proj(l)), Obj::ProductShape(ProductShape::Proj(r))) => Some(vec![
            (l.set.as_ref().clone(), r.set.as_ref().clone()),
            (l.dim.as_ref().clone(), r.dim.as_ref().clone()),
        ]),
        (Obj::ProductShape(ProductShape::ObjAtIndex(l)), Obj::ProductShape(ProductShape::ObjAtIndex(r))) => Some(vec![
            (l.obj.as_ref().clone(), r.obj.as_ref().clone()),
            (l.index.as_ref().clone(), r.index.as_ref().clone()),
        ]),
        (Obj::ProductShape(ProductShape::Tuple(l)), Obj::ProductShape(ProductShape::Tuple(r))) => slice_pairs!(l.args, r.args),
        (Obj::SetFormer(SetFormer::ListSet(l)), Obj::SetFormer(SetFormer::ListSet(r))) => slice_pairs!(l.list, r.list),
        (Obj::ProductShape(ProductShape::Cart(l)), Obj::ProductShape(ProductShape::Cart(r))) => slice_pairs!(l.args, r.args),
        (Obj::SetOperator(SetOperator::IndexCart(l)), Obj::SetOperator(SetOperator::IndexCart(r))) => Some(vec![
            (l.index_set.as_ref().clone(), r.index_set.as_ref().clone()),
            (l.family_set.as_ref().clone(), r.family_set.as_ref().clone()),
            (l.family_fn.as_ref().clone(), r.family_fn.as_ref().clone()),
        ]),
        (Obj::SetOperator(SetOperator::IndexUnion(l)), Obj::SetOperator(SetOperator::IndexUnion(r))) => Some(vec![
            (l.index_set.as_ref().clone(), r.index_set.as_ref().clone()),
            (l.ambient_set.as_ref().clone(), r.ambient_set.as_ref().clone()),
            (l.family_fn.as_ref().clone(), r.family_fn.as_ref().clone()),
        ]),
        (Obj::SetOperator(SetOperator::IndexIntersect(l)), Obj::SetOperator(SetOperator::IndexIntersect(r))) => Some(vec![
            (l.index_set.as_ref().clone(), r.index_set.as_ref().clone()),
            (l.ambient_set.as_ref().clone(), r.ambient_set.as_ref().clone()),
            (l.family_fn.as_ref().clone(), r.family_fn.as_ref().clone()),
        ]),
        (Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(l)), Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::StructObj(r))) => {
            if l.name.to_string() != r.name.to_string() {
                return None;
            }
            obj_slice_pairs!(l.params, r.params)
        }
        (
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(l)),
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(r)),
        ) => {
            if l.fields != r.fields {
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
        Obj::ArithmeticOperator(ArithmeticOperator::Add(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Neg(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Div(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        })),
        Obj::IntegerOperator(IntegerOperator::Mod(a)) => Obj::IntegerOperator(IntegerOperator::Mod(Mod {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        })),
        Obj::IntegerOperator(IntegerOperator::Quot(a)) => Obj::IntegerOperator(IntegerOperator::Quot(Quot {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        })),
        Obj::IntegerOperator(IntegerOperator::Gcd(a)) => Obj::IntegerOperator(IntegerOperator::Gcd(Gcd {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        })),
        Obj::IntegerOperator(IntegerOperator::Lcm(a)) => Obj::IntegerOperator(IntegerOperator::Lcm(Lcm {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Min(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Min(Min {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Max(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
            left: Box::new(replace_obj_matching_ir(&a.left, from_ir, to)),
            right: Box::new(replace_obj_matching_ir(&a.right, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Pow(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: Box::new(replace_obj_matching_ir(&a.base, from_ir, to)),
            exponent: Box::new(replace_obj_matching_ir(&a.exponent, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Floor(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Ceil(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Ceil(Ceil {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::ExpLogOperator(ExpLogOperator::Exp(a)) => Obj::ExpLogOperator(ExpLogOperator::Exp(Exp {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::ExpLogOperator(ExpLogOperator::Ln(a)) => Obj::ExpLogOperator(ExpLogOperator::Ln(Ln {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::ArithmeticOperator(ArithmeticOperator::Sign(a)) => Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::IntegerOperator(IntegerOperator::Factorial(a)) => Obj::IntegerOperator(IntegerOperator::Factorial(Factorial {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::ExpLogOperator(ExpLogOperator::Sqrt(a)) => Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::TrigOperator(TrigOperator::Sin(a)) => Obj::TrigOperator(TrigOperator::Sin(Sin {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::TrigOperator(TrigOperator::Cos(a)) => Obj::TrigOperator(TrigOperator::Cos(Cos {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::TrigOperator(TrigOperator::Tan(a)) => Obj::TrigOperator(TrigOperator::Tan(Tan {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::TrigOperator(TrigOperator::Cot(a)) => Obj::TrigOperator(TrigOperator::Cot(Cot {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::TrigOperator(TrigOperator::Arcsin(a)) => Obj::TrigOperator(TrigOperator::Arcsin(Arcsin {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::TrigOperator(TrigOperator::Arccos(a)) => Obj::TrigOperator(TrigOperator::Arccos(Arccos {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::TrigOperator(TrigOperator::Arctan(a)) => Obj::TrigOperator(TrigOperator::Arctan(Arctan {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
        Obj::TrigOperator(TrigOperator::Arccot(a)) => Obj::TrigOperator(TrigOperator::Arccot(Arccot {
            arg: Box::new(replace_obj_matching_ir(&a.arg, from_ir, to)),
        })),
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
        FnObjHead::AnonymousFnLiteral(a) => Obj::FunctionSpace(FunctionSpace::AnonymousFn(a.as_ref().clone())),
        FnObjHead::FieldAccess(v) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(v.clone()))
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
        (LowerOpen(l), LowerOpen(r))
        | (LowerClosed(l), LowerClosed(r))
        | (UpperOpen(l), UpperOpen(r))
        | (UpperClosed(l), UpperClosed(r)) => (l, r),
        _ => return None,
    };
    Some(vec![(l.start.as_ref().clone(), r.start.as_ref().clone())])
}
