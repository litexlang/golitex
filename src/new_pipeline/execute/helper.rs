//! Shared execute helpers (substitution, …).

use std::collections::HashMap;

use crate::new_pipeline::ast::fact::{
    AndChainAtomicFact, AndFact, AtomicFact, ChainFact, EqualFact, Fact, FnEqualFact, FnEqualInFact,
    GreaterEqualFact, GreaterFact, InFact, IsCartFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact,
    IsTupleFact, LessEqualFact, LessFact, NormalAtomicFact, NotEqualFact, NotGreaterEqualFact,
    NotGreaterFact, NotInFact, NotIsCartFact, NotIsFiniteSetFact, NotIsNonemptySetFact, NotIsSetFact,
    NotIsTupleFact, NotLessEqualFact, NotLessFact, NotNormalAtomicFact, NotSubsetFact,
    NotSupersetFact, OrFact, QuantifierFreeFact, SubsetFact, SupersetFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{
    Abs, Add, Arcsin, BigIntersect, BigUnion, Cart, CartDim, Ceil, ComplexAbs, Cos, Cot, Div, Exp,
    Factorial, FiniteSetMax, FiniteSetMin, FiniteSetSize, Floor, FnRange, Gcd, ImaginaryPart,
    Intersect, Lcm, ListSet, Ln, Log, Max, Min, Mod, Mul, Obj, Pow, PowerSet, Proj, Quot, RealPart,
    SetMinus, Sign, Sin, Sqrt, Sub, Tan, Tuple, TupleDim, Union,
};
use crate::new_pipeline::runtime::FactId;

// Replace plain binder names in a quantifier-free fact. Soft miss → None.
pub fn substitute_quantifier_free_fact(
    fact: &QuantifierFreeFact,
    subst: &HashMap<String, Obj>,
    next_fact_id: &mut dyn FnMut() -> FactId,
) -> Option<Fact> {
    match fact {
        QuantifierFreeFact::AtomicFact(a) => Some(Fact::AtomicFact(substitute_atomic_fact(
            a,
            subst,
            next_fact_id,
        )?)),
        QuantifierFreeFact::AndFact(a) => {
            let mut facts = Vec::with_capacity(a.facts.len());
            for f in &a.facts {
                facts.push(substitute_atomic_fact(f, subst, next_fact_id)?);
            }
            Some(Fact::AndFact(AndFact {
                fact_id: next_fact_id(),
                facts,
                line_file: a.line_file.clone(),
            }))
        }
        QuantifierFreeFact::ChainFact(c) => {
            Some(Fact::ChainFact(substitute_chain_fact(c, subst, next_fact_id)?))
        }
        QuantifierFreeFact::OrFact(o) => {
            let mut facts = Vec::with_capacity(o.facts.len());
            for f in &o.facts {
                facts.push(substitute_and_chain_atomic(f, subst, next_fact_id)?);
            }
            Some(Fact::OrFact(OrFact {
                fact_id: next_fact_id(),
                facts,
                line_file: o.line_file.clone(),
            }))
        }
    }
}

fn substitute_chain_fact(
    fact: &ChainFact,
    subst: &HashMap<String, Obj>,
    next_fact_id: &mut dyn FnMut() -> FactId,
) -> Option<ChainFact> {
    let mut objs = Vec::with_capacity(fact.objs.len());
    for o in &fact.objs {
        objs.push(substitute_obj(o, subst)?);
    }
    Some(ChainFact {
        fact_id: next_fact_id(),
        objs,
        prop_names: fact.prop_names.clone(),
        line_file: fact.line_file.clone(),
    })
}

fn substitute_and_chain_atomic(
    fact: &AndChainAtomicFact,
    subst: &HashMap<String, Obj>,
    next_fact_id: &mut dyn FnMut() -> FactId,
) -> Option<AndChainAtomicFact> {
    match fact {
        AndChainAtomicFact::AtomicFact(a) => Some(AndChainAtomicFact::AtomicFact(
            substitute_atomic_fact(a, subst, next_fact_id)?,
        )),
        AndChainAtomicFact::AndFact(a) => {
            let mut facts = Vec::with_capacity(a.facts.len());
            for f in &a.facts {
                facts.push(substitute_atomic_fact(f, subst, next_fact_id)?);
            }
            Some(AndChainAtomicFact::AndFact(AndFact {
                fact_id: next_fact_id(),
                facts,
                line_file: a.line_file.clone(),
            }))
        }
        AndChainAtomicFact::ChainFact(c) => Some(AndChainAtomicFact::ChainFact(
            substitute_chain_fact(c, subst, next_fact_id)?,
        )),
    }
}

fn substitute_atomic_fact(
    atomic: &AtomicFact,
    subst: &HashMap<String, Obj>,
    next_fact_id: &mut dyn FnMut() -> FactId,
) -> Option<AtomicFact> {
    let fact_id = next_fact_id();
    match atomic {
        AtomicFact::NormalAtomicFact(f) => {
            let mut body = Vec::with_capacity(f.body.len());
            for o in &f.body {
                body.push(substitute_obj(o, subst)?);
            }
            Some(AtomicFact::NormalAtomicFact(NormalAtomicFact {
                fact_id,
                predicate: f.predicate.clone(),
                body,
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::NotNormalAtomicFact(f) => {
            let mut body = Vec::with_capacity(f.body.len());
            for o in &f.body {
                body.push(substitute_obj(o, subst)?);
            }
            Some(AtomicFact::NotNormalAtomicFact(NotNormalAtomicFact {
                fact_id,
                predicate: f.predicate.clone(),
                body,
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::EqualFact(f) => Some(AtomicFact::EqualFact(EqualFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotEqualFact(f) => Some(AtomicFact::NotEqualFact(NotEqualFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::LessFact(f) => Some(AtomicFact::LessFact(LessFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotLessFact(f) => Some(AtomicFact::NotLessFact(NotLessFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::GreaterFact(f) => Some(AtomicFact::GreaterFact(GreaterFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotGreaterFact(f) => Some(AtomicFact::NotGreaterFact(NotGreaterFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::LessEqualFact(f) => Some(AtomicFact::LessEqualFact(LessEqualFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotLessEqualFact(f) => Some(AtomicFact::NotLessEqualFact(NotLessEqualFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::GreaterEqualFact(f) => Some(AtomicFact::GreaterEqualFact(GreaterEqualFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotGreaterEqualFact(f) => {
            Some(AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact {
                fact_id,
                left: substitute_obj(&f.left, subst)?,
                right: substitute_obj(&f.right, subst)?,
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::IsSetFact(f) => Some(AtomicFact::IsSetFact(IsSetFact {
            fact_id,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsSetFact(f) => Some(AtomicFact::NotIsSetFact(NotIsSetFact {
            fact_id,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::IsNonemptySetFact(f) => Some(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
            fact_id,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsNonemptySetFact(f) => {
            Some(AtomicFact::NotIsNonemptySetFact(NotIsNonemptySetFact {
                fact_id,
                set: substitute_obj(&f.set, subst)?,
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::IsFiniteSetFact(f) => Some(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsFiniteSetFact(f) => {
            Some(AtomicFact::NotIsFiniteSetFact(NotIsFiniteSetFact {
                fact_id,
                set: substitute_obj(&f.set, subst)?,
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::InFact(f) => Some(AtomicFact::InFact(InFact {
            fact_id,
            element: substitute_obj(&f.element, subst)?,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotInFact(f) => Some(AtomicFact::NotInFact(NotInFact {
            fact_id,
            element: substitute_obj(&f.element, subst)?,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::IsCartFact(f) => Some(AtomicFact::IsCartFact(IsCartFact {
            fact_id,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsCartFact(f) => Some(AtomicFact::NotIsCartFact(NotIsCartFact {
            fact_id,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::IsTupleFact(f) => Some(AtomicFact::IsTupleFact(IsTupleFact {
            fact_id,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotIsTupleFact(f) => Some(AtomicFact::NotIsTupleFact(NotIsTupleFact {
            fact_id,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::SubsetFact(f) => Some(AtomicFact::SubsetFact(SubsetFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotSubsetFact(f) => Some(AtomicFact::NotSubsetFact(NotSubsetFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::SupersetFact(f) => Some(AtomicFact::SupersetFact(SupersetFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::NotSupersetFact(f) => Some(AtomicFact::NotSupersetFact(NotSupersetFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::FnEqualInFact(f) => Some(AtomicFact::FnEqualInFact(FnEqualInFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            set: substitute_obj(&f.set, subst)?,
            line_file: f.line_file.clone(),
        })),
        AtomicFact::FnEqualFact(f) => Some(AtomicFact::FnEqualFact(FnEqualFact {
            fact_id,
            left: substitute_obj(&f.left, subst)?,
            right: substitute_obj(&f.right, subst)?,
            line_file: f.line_file.clone(),
        })),
    }
}

// Structural replace of plain free names. Binder-carrying objs → None for now.
pub fn substitute_obj(obj: &Obj, subst: &HashMap<String, Obj>) -> Option<Obj> {
    match obj {
        Obj::Identifier(id) => {
            if let AtomicName::Plain { name } = &id.name {
                if let Some(replacement) = subst.get(name) {
                    return Some(replacement.clone());
                }
            }
            Some(obj.clone())
        }
        Obj::Number(_)
        | Obj::ImaginaryUnit(_)
        | Obj::EulerNumber(_)
        | Obj::Pi(_)
        | Obj::StandardSet(_) => Some(obj.clone()),
        Obj::Add(Add { left, right }) => Some(Obj::Add(Add {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Sub(Sub { left, right }) => Some(Obj::Sub(Sub {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Mul(Mul { left, right }) => Some(Obj::Mul(Mul {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Div(Div { left, right }) => Some(Obj::Div(Div {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Mod(Mod { left, right }) => Some(Obj::Mod(Mod {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Quot(Quot { left, right }) => Some(Obj::Quot(Quot {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Gcd(Gcd { left, right }) => Some(Obj::Gcd(Gcd {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Lcm(Lcm { left, right }) => Some(Obj::Lcm(Lcm {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Min(Min { left, right }) => Some(Obj::Min(Min {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Max(Max { left, right }) => Some(Obj::Max(Max {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Pow(Pow { base, exponent }) => Some(Obj::Pow(Pow {
            base: Box::new(substitute_obj(base, subst)?),
            exponent: Box::new(substitute_obj(exponent, subst)?),
        })),
        Obj::Log(Log { base, arg }) => Some(Obj::Log(Log {
            base: Box::new(substitute_obj(base, subst)?),
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Floor(Floor { arg }) => Some(Obj::Floor(Floor {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Ceil(Ceil { arg }) => Some(Obj::Ceil(Ceil {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Exp(Exp { arg }) => Some(Obj::Exp(Exp {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Ln(Ln { arg }) => Some(Obj::Ln(Ln {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Sign(Sign { arg }) => Some(Obj::Sign(Sign {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Factorial(Factorial { arg }) => Some(Obj::Factorial(Factorial {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Abs(Abs { arg }) => Some(Obj::Abs(Abs {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Sin(Sin { arg }) => Some(Obj::Sin(Sin {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Arcsin(Arcsin { arg }) => Some(Obj::Arcsin(Arcsin {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Cos(Cos { arg }) => Some(Obj::Cos(Cos {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Tan(Tan { arg }) => Some(Obj::Tan(Tan {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Cot(Cot { arg }) => Some(Obj::Cot(Cot {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::RealPart(RealPart { arg }) => Some(Obj::RealPart(RealPart {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::ImaginaryPart(ImaginaryPart { arg }) => Some(Obj::ImaginaryPart(ImaginaryPart {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::ComplexAbs(ComplexAbs { arg }) => Some(Obj::ComplexAbs(ComplexAbs {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Sqrt(Sqrt { arg }) => Some(Obj::Sqrt(Sqrt {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::Union(Union { left, right }) => Some(Obj::Union(Union {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::Intersect(Intersect { left, right }) => Some(Obj::Intersect(Intersect {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::SetMinus(SetMinus { left, right }) => Some(Obj::SetMinus(SetMinus {
            left: Box::new(substitute_obj(left, subst)?),
            right: Box::new(substitute_obj(right, subst)?),
        })),
        Obj::BigUnion(BigUnion { left }) => Some(Obj::BigUnion(BigUnion {
            left: Box::new(substitute_obj(left, subst)?),
        })),
        Obj::BigIntersect(BigIntersect { left }) => Some(Obj::BigIntersect(BigIntersect {
            left: Box::new(substitute_obj(left, subst)?),
        })),
        Obj::PowerSet(PowerSet { set }) => Some(Obj::PowerSet(PowerSet {
            set: Box::new(substitute_obj(set, subst)?),
        })),
        Obj::ListSet(ListSet { list }) => {
            let mut new_list = Vec::with_capacity(list.len());
            for o in list {
                new_list.push(Box::new(substitute_obj(o, subst)?));
            }
            Some(Obj::ListSet(ListSet { list: new_list }))
        }
        Obj::Cart(Cart { args }) => {
            let mut new_args = Vec::with_capacity(args.len());
            for o in args {
                new_args.push(Box::new(substitute_obj(o, subst)?));
            }
            Some(Obj::Cart(Cart { args: new_args }))
        }
        Obj::Tuple(Tuple { args }) => {
            let mut new_args = Vec::with_capacity(args.len());
            for o in args {
                new_args.push(Box::new(substitute_obj(o, subst)?));
            }
            Some(Obj::Tuple(Tuple { args: new_args }))
        }
        Obj::CartDim(CartDim { set }) => Some(Obj::CartDim(CartDim {
            set: Box::new(substitute_obj(set, subst)?),
        })),
        Obj::Proj(Proj { set, dim }) => Some(Obj::Proj(Proj {
            set: Box::new(substitute_obj(set, subst)?),
            dim: Box::new(substitute_obj(dim, subst)?),
        })),
        Obj::TupleDim(TupleDim { arg }) => Some(Obj::TupleDim(TupleDim {
            arg: Box::new(substitute_obj(arg, subst)?),
        })),
        Obj::FiniteSetSize(FiniteSetSize { set }) => Some(Obj::FiniteSetSize(FiniteSetSize {
            set: Box::new(substitute_obj(set, subst)?),
        })),
        Obj::FiniteSetMax(FiniteSetMax { set }) => Some(Obj::FiniteSetMax(FiniteSetMax {
            set: Box::new(substitute_obj(set, subst)?),
        })),
        Obj::FiniteSetMin(FiniteSetMin { set }) => Some(Obj::FiniteSetMin(FiniteSetMin {
            set: Box::new(substitute_obj(set, subst)?),
        })),
        Obj::FnRange(FnRange { function }) => Some(Obj::FnRange(FnRange {
            function: Box::new(substitute_obj(function, subst)?),
        })),
        // Binder / complex heads: not substituted in this tranche.
        Obj::FnObj(_)
        | Obj::SetBuilder(_)
        | Obj::FnSet(_)
        | Obj::AnonymousFn(_)
        | Obj::IndexUnion(_)
        | Obj::IndexIntersect(_)
        | Obj::GeneralCart(_)
        | Obj::Replacement(_)
        | Obj::Sum(_)
        | Obj::SumOfFiniteSet(_)
        | Obj::Product(_)
        | Obj::ProductOfFiniteSet(_)
        | Obj::Reduce(_)
        | Obj::FiniteSetReduce(_)
        | Obj::Range(_)
        | Obj::ClosedRange(_)
        | Obj::FiniteSeqSet(_)
        | Obj::SeqSet(_)
        | Obj::FiniteSeqListObj(_)
        | Obj::ObjAtIndex(_)
        | Obj::StructObj(_)
        | Obj::ObjAsStructInstanceWithFieldAccess(_)
        | Obj::InstantiatedTemplateObj(_)
        | Obj::OneSideInfinityIntervalObj(_)
        | Obj::IntervalObj(_) => None,
    }
}
