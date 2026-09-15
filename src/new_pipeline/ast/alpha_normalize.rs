//! Alpha-normalize binder-carrying objects at construction.
//!
//! Surface keeps user letters for display. Alpha uses `□N` for ops / ir / known-memory keys.
//! Example: surface `{x R: x $in {y R: y > 0}}`,
//! alpha `{□0 R: □0 $in {□1 R: □1 > 0}}`.

use std::collections::HashMap;

use super::fact::{
    AndChainAtomicFact, AndFact, AtomicFact, ChainFact, EqualFact, FnEqualFact, FnEqualInFact,
    GreaterEqualFact, GreaterFact, InFact, IsCartFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact,
    IsTupleFact, LessEqualFact, LessFact, NormalAtomicFact, NotEqualFact, NotGreaterEqualFact,
    NotGreaterFact, NotInFact, NotIsCartFact, NotIsFiniteSetFact, NotIsNonemptySetFact, NotIsSetFact,
    NotIsTupleFact, NotLessEqualFact, NotLessFact, NotNormalAtomicFact, NotSubsetFact, NotSupersetFact,
    OrFact, QuantifierFreeFact, SubsetFact, SupersetFact,
};
use super::names::AtomicName;
use super::obj::*;
use super::param::{SetBoundParameterGroup, SetBoundParameterList};

type RenameEnv = HashMap<String, String>;

pub fn new_set_builder(
    param_binding: Identifier,
    param_set: Obj,
    facts: Vec<QuantifierFreeFact>,
) -> Obj {
    let surface = SetBuilderBody {
        param_binding,
        param_set: Box::new(param_set),
        facts,
    };
    let mut counter = 0usize;
    let alpha = alpha_normalize_set_builder_body(surface.clone(), &RenameEnv::new(), &mut counter);
    Obj::SetBuilder(SetBuilder { surface, alpha })
}

pub fn new_fn_set(
    set_bound_parameters: SetBoundParameterList,
    dom_facts: Vec<QuantifierFreeFact>,
    ret_set: Obj,
) -> Obj {
    let surface = FnSetBody {
        set_bound_parameters,
        dom_facts,
        ret_set: Box::new(ret_set),
    };
    let mut counter = 0usize;
    let alpha = alpha_normalize_fn_set_body(surface.clone(), &RenameEnv::new(), &mut counter).0;
    Obj::FnSet(FnSet { surface, alpha })
}

pub fn new_anonymous_fn(
    set_bound_parameters: SetBoundParameterList,
    dom_facts: Vec<QuantifierFreeFact>,
    ret_set: Obj,
    equal_to: Obj,
) -> Obj {
    let surface = AnonymousFnBody {
        body: FnSetBody {
            set_bound_parameters,
            dom_facts,
            ret_set: Box::new(ret_set),
        },
        equal_to: Box::new(equal_to),
    };
    let mut counter = 0usize;
    let alpha = alpha_normalize_anonymous_fn_body(surface.clone(), &RenameEnv::new(), &mut counter);
    Obj::AnonymousFn(AnonymousFn { surface, alpha })
}

fn alpha_normalize_set_builder_body(
    body: SetBuilderBody,
    env: &RenameEnv,
    counter: &mut usize,
) -> SetBuilderBody {
    let param_set = Box::new(alpha_normalize_obj(*body.param_set, env, counter));
    let old_name = body.param_binding.name;
    let slot = binder_slot_name(*counter);
    *counter += 1;
    let mut env2 = env.clone();
    env2.insert(old_name, slot.clone());
    let facts = body
        .facts
        .into_iter()
        .map(|f| alpha_normalize_qf_fact(f, &env2, counter))
        .collect();
    SetBuilderBody {
        param_binding: Identifier::new(slot),
        param_set,
        facts,
    }
}

fn alpha_normalize_fn_set_body(
    body: FnSetBody,
    env: &RenameEnv,
    counter: &mut usize,
) -> (FnSetBody, RenameEnv) {
    let mut env2 = env.clone();
    let mut groups = Vec::new();
    for group in body.set_bound_parameters.groups {
        let param_type = Box::new(alpha_normalize_obj(*group.param_type, &env2, counter));
        let mut params = Vec::new();
        for p in group.params {
            let old_name = p.name;
            let slot = binder_slot_name(*counter);
            *counter += 1;
            env2.insert(old_name, slot.clone());
            params.push(Identifier::new(slot));
        }
        groups.push(SetBoundParameterGroup {
            params,
            param_type,
        });
    }
    let dom_facts = body
        .dom_facts
        .into_iter()
        .map(|f| alpha_normalize_qf_fact(f, &env2, counter))
        .collect();
    let ret_set = Box::new(alpha_normalize_obj(*body.ret_set, &env2, counter));
    (
        FnSetBody {
            set_bound_parameters: SetBoundParameterList { groups },
            dom_facts,
            ret_set,
        },
        env2,
    )
}

fn alpha_normalize_anonymous_fn_body(
    anon: AnonymousFnBody,
    env: &RenameEnv,
    counter: &mut usize,
) -> AnonymousFnBody {
    let (body, env_after) = alpha_normalize_fn_set_body(anon.body, env, counter);
    let equal_to = Box::new(alpha_normalize_obj(*anon.equal_to, &env_after, counter));
    AnonymousFnBody { body, equal_to }
}

fn map_interval(s: IntervalObjStruct, env: &RenameEnv, counter: &mut usize) -> IntervalObjStruct {
    IntervalObjStruct {
        start: Box::new(alpha_normalize_obj(*s.start, env, counter)),
        end: Box::new(alpha_normalize_obj(*s.end, env, counter)),
    }
}

fn alpha_normalize_struct_obj(s: StructObj, env: &RenameEnv, counter: &mut usize) -> StructObj {
    StructObj {
        name: s.name,
        params: s
            .params
            .into_iter()
            .map(|o| alpha_normalize_obj(o, env, counter))
            .collect(),
    }
}

fn alpha_normalize_fn_obj_head(head: FnObjHead, env: &RenameEnv, counter: &mut usize) -> FnObjHead {
    match head {
        FnObjHead::Identifier(id) => FnObjHead::Identifier(rename_identifier_obj(id, env)),
        FnObjHead::AnonymousFnLiteral(a) => {
            let alpha = alpha_normalize_anonymous_fn_body(a.surface.clone(), env, counter);
            FnObjHead::AnonymousFnLiteral(Box::new(AnonymousFn {
                surface: a.surface,
                alpha,
            }))
        }
        FnObjHead::FiniteSeqListObj(FiniteSeqListObj { objs }) => {
            FnObjHead::FiniteSeqListObj(FiniteSeqListObj {
                objs: objs
                    .into_iter()
                    .map(|o| Box::new(alpha_normalize_obj(*o, env, counter)))
                    .collect(),
            })
        }
        FnObjHead::ObjAtIndex(ObjAtIndex { obj, index }) => FnObjHead::ObjAtIndex(ObjAtIndex {
            obj: Box::new(alpha_normalize_obj(*obj, env, counter)),
            index: Box::new(alpha_normalize_obj(*index, env, counter)),
        }),
        FnObjHead::ObjAsStructInstanceWithFieldAccess(v) => {
            FnObjHead::ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccess {
                obj: Box::new(alpha_normalize_obj(*v.obj, env, counter)),
                field_name: v.field_name,
                resolved_struct_carrier: v
                    .resolved_struct_carrier
                    .map(|s| Box::new(alpha_normalize_struct_obj(*s, env, counter))),
            })
        }
        FnObjHead::InstantiatedTemplateObj(InstantiatedTemplateObj {
            template_name,
            args,
        }) => FnObjHead::InstantiatedTemplateObj(InstantiatedTemplateObj {
            template_name,
            args: args
                .into_iter()
                .map(|o| alpha_normalize_obj(o, env, counter))
                .collect(),
        }),
    }
}

fn rename_identifier_obj(id: IdentifierObj, env: &RenameEnv) -> IdentifierObj {
    match id.name {
        AtomicName::Plain { name } => match env.get(&name) {
            Some(slot) => IdentifierObj::plain(slot.clone()),
            None => IdentifierObj::plain(name),
        },
        other => IdentifierObj::new(other),
    }
}

fn alpha_normalize_obj(obj: Obj, env: &RenameEnv, counter: &mut usize) -> Obj {
    match obj {
        Obj::Identifier(id) => Obj::Identifier(rename_identifier_obj(id, env)),
        Obj::FnObj(FnObj { head, body }) => Obj::FnObj(FnObj {
            head: Box::new(alpha_normalize_fn_obj_head(*head, env, counter)),
            body: body
                .into_iter()
                .map(|g| {
                    g.into_iter()
                        .map(|o| Box::new(alpha_normalize_obj(*o, env, counter)))
                        .collect()
                })
                .collect(),
        }),
        Obj::Number(x) => Obj::Number(x),
        Obj::ImaginaryUnit(x) => Obj::ImaginaryUnit(x),
        Obj::EulerNumber(x) => Obj::EulerNumber(x),
        Obj::Pi(x) => Obj::Pi(x),
        Obj::Add(Add { left, right }) => Obj::Add(Add {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Sub(Sub { left, right }) => Obj::Sub(Sub {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Mul(Mul { left, right }) => Obj::Mul(Mul {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Div(Div { left, right }) => Obj::Div(Div {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Mod(Mod { left, right }) => Obj::Mod(Mod {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Quot(Quot { left, right }) => Obj::Quot(Quot {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Gcd(Gcd { left, right }) => Obj::Gcd(Gcd {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Lcm(Lcm { left, right }) => Obj::Lcm(Lcm {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Floor(Floor { arg }) => Obj::Floor(Floor {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Ceil(Ceil { arg }) => Obj::Ceil(Ceil {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Min(Min { left, right }) => Obj::Min(Min {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Max(Max { left, right }) => Obj::Max(Max {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Exp(Exp { arg }) => Obj::Exp(Exp {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Ln(Ln { arg }) => Obj::Ln(Ln {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Sign(Sign { arg }) => Obj::Sign(Sign {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Factorial(Factorial { arg }) => Obj::Factorial(Factorial {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Pow(Pow { base, exponent }) => Obj::Pow(Pow {
                base: Box::new(alpha_normalize_obj(*base, env, counter)),
                exponent: Box::new(alpha_normalize_obj(*exponent, env, counter)),
            }),
        Obj::Abs(Abs { arg }) => Obj::Abs(Abs {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Sin(Sin { arg }) => Obj::Sin(Sin {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Arcsin(Arcsin { arg }) => Obj::Arcsin(Arcsin {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Cos(Cos { arg }) => Obj::Cos(Cos {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Tan(Tan { arg }) => Obj::Tan(Tan {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Cot(Cot { arg }) => Obj::Cot(Cot {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::RealPart(RealPart { arg }) => Obj::RealPart(RealPart {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::ImaginaryPart(ImaginaryPart { arg }) => Obj::ImaginaryPart(ImaginaryPart {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::ComplexAbs(ComplexAbs { arg }) => Obj::ComplexAbs(ComplexAbs {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Sqrt(Sqrt { arg }) => Obj::Sqrt(Sqrt {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Log(Log { base, arg }) => Obj::Log(Log {
                base: Box::new(alpha_normalize_obj(*base, env, counter)),
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Union(Union { left, right }) => Obj::Union(Union {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::Intersect(Intersect { left, right }) => Obj::Intersect(Intersect {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::SetMinus(SetMinus { left, right }) => Obj::SetMinus(SetMinus {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
                right: Box::new(alpha_normalize_obj(*right, env, counter)),
            }),
        Obj::BigUnion(BigUnion { left }) => Obj::BigUnion(BigUnion {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
            }),
        Obj::BigIntersect(BigIntersect { left }) => Obj::BigIntersect(BigIntersect {
                left: Box::new(alpha_normalize_obj(*left, env, counter)),
            }),
        Obj::IndexUnion(IndexUnion { index_set, ambient_set, family_fn }) => Obj::IndexUnion(IndexUnion {
                index_set: Box::new(alpha_normalize_obj(*index_set, env, counter)),
                ambient_set: Box::new(alpha_normalize_obj(*ambient_set, env, counter)),
                family_fn: Box::new(alpha_normalize_obj(*family_fn, env, counter)),
            }),
        Obj::IndexIntersect(IndexIntersect { index_set, ambient_set, family_fn }) => Obj::IndexIntersect(IndexIntersect {
                index_set: Box::new(alpha_normalize_obj(*index_set, env, counter)),
                ambient_set: Box::new(alpha_normalize_obj(*ambient_set, env, counter)),
                family_fn: Box::new(alpha_normalize_obj(*family_fn, env, counter)),
            }),
        Obj::PowerSet(PowerSet { set }) => Obj::PowerSet(PowerSet {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
            }),
        Obj::GeneralCart(GeneralCart { index_set, family_set, family_fn }) => Obj::GeneralCart(GeneralCart {
                index_set: Box::new(alpha_normalize_obj(*index_set, env, counter)),
                family_set: Box::new(alpha_normalize_obj(*family_set, env, counter)),
                family_fn: Box::new(alpha_normalize_obj(*family_fn, env, counter)),
            }),
        Obj::ListSet(ListSet { list }) => Obj::ListSet(ListSet {
                list: list.into_iter().map(|o| Box::new(alpha_normalize_obj(*o, env, counter))).collect(),
            }),
        Obj::SetBuilder(sb) => {
            let alpha = alpha_normalize_set_builder_body(sb.surface.clone(), env, counter);
            Obj::SetBuilder(SetBuilder {
                surface: sb.surface,
                alpha,
            })
        }
        Obj::FnSet(fn_set) => {
            let alpha = alpha_normalize_fn_set_body(fn_set.surface.clone(), env, counter).0;
            Obj::FnSet(FnSet {
                surface: fn_set.surface,
                alpha,
            })
        }
        Obj::AnonymousFn(anon) => {
            let alpha = alpha_normalize_anonymous_fn_body(anon.surface.clone(), env, counter);
            Obj::AnonymousFn(AnonymousFn {
                surface: anon.surface,
                alpha,
            })
        }
        Obj::Cart(Cart { args }) => Obj::Cart(Cart {
                args: args.into_iter().map(|o| Box::new(alpha_normalize_obj(*o, env, counter))).collect(),
            }),
        Obj::CartDim(CartDim { set }) => Obj::CartDim(CartDim {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
            }),
        Obj::Proj(Proj { set, dim }) => Obj::Proj(Proj {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
                dim: Box::new(alpha_normalize_obj(*dim, env, counter)),
            }),
        Obj::TupleDim(TupleDim { arg }) => Obj::TupleDim(TupleDim {
                arg: Box::new(alpha_normalize_obj(*arg, env, counter)),
            }),
        Obj::Tuple(Tuple { args }) => Obj::Tuple(Tuple {
                args: args.into_iter().map(|o| Box::new(alpha_normalize_obj(*o, env, counter))).collect(),
            }),
        Obj::FiniteSetSize(FiniteSetSize { set }) => Obj::FiniteSetSize(FiniteSetSize {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
            }),
        Obj::FiniteSetMax(FiniteSetMax { set }) => Obj::FiniteSetMax(FiniteSetMax {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
            }),
        Obj::FiniteSetMin(FiniteSetMin { set }) => Obj::FiniteSetMin(FiniteSetMin {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
            }),
        Obj::FnRange(FnRange { function }) => Obj::FnRange(FnRange {
                function: Box::new(alpha_normalize_obj(*function, env, counter)),
            }),
        Obj::Replacement(Replacement { prop_name, source_set }) => Obj::Replacement(Replacement {
                prop_name: prop_name,
                source_set: Box::new(alpha_normalize_obj(*source_set, env, counter)),
            }),
        Obj::Sum(Sum { start, end, func }) => Obj::Sum(Sum {
                start: Box::new(alpha_normalize_obj(*start, env, counter)),
                end: Box::new(alpha_normalize_obj(*end, env, counter)),
                func: Box::new(alpha_normalize_obj(*func, env, counter)),
            }),
        Obj::SumOfFiniteSet(SumOfFiniteSet { set, func }) => Obj::SumOfFiniteSet(SumOfFiniteSet {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
                func: Box::new(alpha_normalize_obj(*func, env, counter)),
            }),
        Obj::Product(Product { start, end, func }) => Obj::Product(Product {
                start: Box::new(alpha_normalize_obj(*start, env, counter)),
                end: Box::new(alpha_normalize_obj(*end, env, counter)),
                func: Box::new(alpha_normalize_obj(*func, env, counter)),
            }),
        Obj::ProductOfFiniteSet(ProductOfFiniteSet { set, func }) => Obj::ProductOfFiniteSet(ProductOfFiniteSet {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
                func: Box::new(alpha_normalize_obj(*func, env, counter)),
            }),
        Obj::Reduce(Reduce { start, end, func, op, seed }) => Obj::Reduce(Reduce {
                start: Box::new(alpha_normalize_obj(*start, env, counter)),
                end: Box::new(alpha_normalize_obj(*end, env, counter)),
                func: Box::new(alpha_normalize_obj(*func, env, counter)),
                op: Box::new(alpha_normalize_obj(*op, env, counter)),
                seed: Box::new(alpha_normalize_obj(*seed, env, counter)),
            }),
        Obj::FiniteSetReduce(FiniteSetReduce { set, func, op, seed }) => Obj::FiniteSetReduce(FiniteSetReduce {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
                func: Box::new(alpha_normalize_obj(*func, env, counter)),
                op: Box::new(alpha_normalize_obj(*op, env, counter)),
                seed: Box::new(alpha_normalize_obj(*seed, env, counter)),
            }),
        Obj::Range(Range { start, end }) => Obj::Range(Range {
                start: Box::new(alpha_normalize_obj(*start, env, counter)),
                end: Box::new(alpha_normalize_obj(*end, env, counter)),
            }),
        Obj::ClosedRange(ClosedRange { start, end }) => Obj::ClosedRange(ClosedRange {
                start: Box::new(alpha_normalize_obj(*start, env, counter)),
                end: Box::new(alpha_normalize_obj(*end, env, counter)),
            }),
        Obj::FiniteSeqSet(FiniteSeqSet { set, n }) => Obj::FiniteSeqSet(FiniteSeqSet {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
                n: Box::new(alpha_normalize_obj(*n, env, counter)),
            }),
        Obj::SeqSet(SeqSet { set }) => Obj::SeqSet(SeqSet {
                set: Box::new(alpha_normalize_obj(*set, env, counter)),
            }),
        Obj::FiniteSeqListObj(FiniteSeqListObj { objs }) => Obj::FiniteSeqListObj(FiniteSeqListObj {
                objs: objs.into_iter().map(|o| Box::new(alpha_normalize_obj(*o, env, counter))).collect(),
            }),
        Obj::ObjAtIndex(ObjAtIndex { obj, index }) => Obj::ObjAtIndex(ObjAtIndex {
                obj: Box::new(alpha_normalize_obj(*obj, env, counter)),
                index: Box::new(alpha_normalize_obj(*index, env, counter)),
            }),
        Obj::StandardSet(x) => Obj::StandardSet(x),
        Obj::StructObj(s) => Obj::StructObj(alpha_normalize_struct_obj(s, env, counter)),
        Obj::ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccess { obj, field_name, resolved_struct_carrier }) => Obj::ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccess {
                obj: Box::new(alpha_normalize_obj(*obj, env, counter)),
                field_name: field_name,
                resolved_struct_carrier: resolved_struct_carrier.map(|s| Box::new(alpha_normalize_struct_obj(*s, env, counter))),
            }),
        Obj::InstantiatedTemplateObj(InstantiatedTemplateObj { template_name, args }) => Obj::InstantiatedTemplateObj(InstantiatedTemplateObj {
                template_name: template_name,
                args: args.into_iter().map(|o| alpha_normalize_obj(o, env, counter)).collect(),
            }),
        Obj::OneSideInfinityIntervalObj(v) => Obj::OneSideInfinityIntervalObj(match v {
            OneSideInfinityIntervalObj::LeftOpen(s) => OneSideInfinityIntervalObj::LeftOpen(OneSideInfinityIntervalObjStruct { start: Box::new(alpha_normalize_obj(*s.start, env, counter)) }),
            OneSideInfinityIntervalObj::LeftClosed(s) => OneSideInfinityIntervalObj::LeftClosed(OneSideInfinityIntervalObjStruct { start: Box::new(alpha_normalize_obj(*s.start, env, counter)) }),
            OneSideInfinityIntervalObj::RightOpen(s) => OneSideInfinityIntervalObj::RightOpen(OneSideInfinityIntervalObjStruct { start: Box::new(alpha_normalize_obj(*s.start, env, counter)) }),
            OneSideInfinityIntervalObj::RightClosed(s) => OneSideInfinityIntervalObj::RightClosed(OneSideInfinityIntervalObjStruct { start: Box::new(alpha_normalize_obj(*s.start, env, counter)) }),
        }),
        Obj::IntervalObj(v) => Obj::IntervalObj(match v {
            IntervalObj::LeftOpenRightOpen(s) => IntervalObj::LeftOpenRightOpen(map_interval(s, env, counter)),
            IntervalObj::LeftOpenRightClosed(s) => IntervalObj::LeftOpenRightClosed(map_interval(s, env, counter)),
            IntervalObj::LeftClosedRightOpen(s) => IntervalObj::LeftClosedRightOpen(map_interval(s, env, counter)),
            IntervalObj::LeftClosedRightClosed(s) => IntervalObj::LeftClosedRightClosed(map_interval(s, env, counter)),
        }),
    }
}

fn alpha_normalize_qf_fact(
    fact: QuantifierFreeFact,
    env: &RenameEnv,
    counter: &mut usize,
) -> QuantifierFreeFact {
    match fact {
        QuantifierFreeFact::AtomicFact(a) => {
            QuantifierFreeFact::AtomicFact(alpha_normalize_atomic_fact(a, env, counter))
        }
        QuantifierFreeFact::AndFact(AndFact {
            fact_id,
            facts,
            line_file,
        }) => QuantifierFreeFact::AndFact(AndFact {
            fact_id,
            facts: facts
                .into_iter()
                .map(|a| alpha_normalize_atomic_fact(a, env, counter))
                .collect(),
            line_file,
        }),
        QuantifierFreeFact::ChainFact(ChainFact {
            fact_id,
            objs,
            prop_names,
            line_file,
        }) => QuantifierFreeFact::ChainFact(ChainFact {
            fact_id,
            objs: objs
                .into_iter()
                .map(|o| alpha_normalize_obj(o, env, counter))
                .collect(),
            prop_names,
            line_file,
        }),
        QuantifierFreeFact::OrFact(OrFact {
            fact_id,
            facts,
            line_file,
        }) => QuantifierFreeFact::OrFact(OrFact {
            fact_id,
            facts: facts
                .into_iter()
                .map(|f| alpha_normalize_and_chain(f, env, counter))
                .collect(),
            line_file,
        }),
    }
}

fn alpha_normalize_and_chain(
    fact: AndChainAtomicFact,
    env: &RenameEnv,
    counter: &mut usize,
) -> AndChainAtomicFact {
    match fact {
        AndChainAtomicFact::AtomicFact(a) => {
            AndChainAtomicFact::AtomicFact(alpha_normalize_atomic_fact(a, env, counter))
        }
        AndChainAtomicFact::AndFact(AndFact {
            fact_id,
            facts,
            line_file,
        }) => AndChainAtomicFact::AndFact(AndFact {
            fact_id,
            facts: facts
                .into_iter()
                .map(|a| alpha_normalize_atomic_fact(a, env, counter))
                .collect(),
            line_file,
        }),
        AndChainAtomicFact::ChainFact(ChainFact {
            fact_id,
            objs,
            prop_names,
            line_file,
        }) => AndChainAtomicFact::ChainFact(ChainFact {
            fact_id,
            objs: objs
                .into_iter()
                .map(|o| alpha_normalize_obj(o, env, counter))
                .collect(),
            prop_names,
            line_file,
        }),
    }
}

fn alpha_normalize_atomic_fact(
    fact: AtomicFact,
    env: &RenameEnv,
    counter: &mut usize,
) -> AtomicFact {
    match fact {
        AtomicFact::NormalAtomicFact(NormalAtomicFact { fact_id, predicate, body, line_file }) => AtomicFact::NormalAtomicFact(NormalAtomicFact {
            fact_id, predicate, body: body.into_iter().map(|o| alpha_normalize_obj(o, env, counter)).collect(), line_file,
        }),
        AtomicFact::EqualFact(EqualFact { fact_id, left, right, line_file }) => AtomicFact::EqualFact(EqualFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::LessFact(LessFact { fact_id, left, right, line_file }) => AtomicFact::LessFact(LessFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::GreaterFact(GreaterFact { fact_id, left, right, line_file }) => AtomicFact::GreaterFact(GreaterFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::LessEqualFact(LessEqualFact { fact_id, left, right, line_file }) => AtomicFact::LessEqualFact(LessEqualFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::GreaterEqualFact(GreaterEqualFact { fact_id, left, right, line_file }) => AtomicFact::GreaterEqualFact(GreaterEqualFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::IsSetFact(IsSetFact { fact_id, set, line_file }) => AtomicFact::IsSetFact(IsSetFact {
            fact_id, set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::IsNonemptySetFact(IsNonemptySetFact { fact_id, set, line_file }) => AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
            fact_id, set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::IsFiniteSetFact(IsFiniteSetFact { fact_id, set, line_file }) => AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id, set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::InFact(InFact { fact_id, element, set, line_file }) => AtomicFact::InFact(InFact {
            fact_id, element: alpha_normalize_obj(element, env, counter), set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::IsCartFact(IsCartFact { fact_id, set, line_file }) => AtomicFact::IsCartFact(IsCartFact {
            fact_id, set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::IsTupleFact(IsTupleFact { fact_id, set, line_file }) => AtomicFact::IsTupleFact(IsTupleFact {
            fact_id, set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::SubsetFact(SubsetFact { fact_id, left, right, line_file }) => AtomicFact::SubsetFact(SubsetFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::SupersetFact(SupersetFact { fact_id, left, right, line_file }) => AtomicFact::SupersetFact(SupersetFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact { fact_id, predicate, body, line_file }) => AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact {
            fact_id, predicate, body: body.into_iter().map(|o| alpha_normalize_obj(o, env, counter)).collect(), line_file,
        }),
        AtomicFact::NotEqualFact(NotEqualFact { fact_id, left, right, line_file }) => AtomicFact::NotEqualFact(NotEqualFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::NotLessFact(NotLessFact { fact_id, left, right, line_file }) => AtomicFact::NotLessFact(NotLessFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::NotGreaterFact(NotGreaterFact { fact_id, left, right, line_file }) => AtomicFact::NotGreaterFact(NotGreaterFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::NotLessEqualFact(NotLessEqualFact { fact_id, left, right, line_file }) => AtomicFact::NotLessEqualFact(NotLessEqualFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact { fact_id, left, right, line_file }) => AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::NotIsSetFact(NotIsSetFact { fact_id, set, line_file }) => AtomicFact::NotIsSetFact(NotIsSetFact {
            fact_id, set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact { fact_id, set, line_file }) => AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact {
            fact_id, set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact { fact_id, set, line_file }) => AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact {
            fact_id, set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::NotInFact(NotInFact { fact_id, element, set, line_file }) => AtomicFact::NotInFact(NotInFact {
            fact_id, element: alpha_normalize_obj(element, env, counter), set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::NotIsCartFact(NotIsCartFact { fact_id, set, line_file }) => AtomicFact::NotIsCartFact(NotIsCartFact {
            fact_id, set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::NotIsTupleFact(NotIsTupleFact { fact_id, set, line_file }) => AtomicFact::NotIsTupleFact(NotIsTupleFact {
            fact_id, set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::NotSubsetFact(NotSubsetFact { fact_id, left, right, line_file }) => AtomicFact::NotSubsetFact(NotSubsetFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::NotSupersetFact(NotSupersetFact { fact_id, left, right, line_file }) => AtomicFact::NotSupersetFact(NotSupersetFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
        AtomicFact::FnEqualInFact(FnEqualInFact { fact_id, left, right, set, line_file }) => AtomicFact::FnEqualInFact(FnEqualInFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), set: alpha_normalize_obj(set, env, counter), line_file,
        }),
        AtomicFact::FnEqualFact(FnEqualFact { fact_id, left, right, line_file }) => AtomicFact::FnEqualFact(FnEqualFact {
            fact_id, left: alpha_normalize_obj(left, env, counter), right: alpha_normalize_obj(right, env, counter), line_file,
        }),
    }
}
