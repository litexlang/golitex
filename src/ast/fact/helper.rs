use super::super::obj::{IdentifierObj, Obj};
use super::super::param::ParamType;
use super::{
    AndChainAtomicFact, AtomicFact, BijectiveFact, CoprimeFact, DvdFact, EqualFact,
    ExistShapedFact, Fact, GreaterEqualFact, GreaterFact, InFact, InjectiveFact,
    IsChoiceFunctionForFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact, LessEqualFact,
    LessFact, NormalAtomicFact, NotBijectiveFact, NotCoprimeFact, NotDvdFact, NotEqualFact,
    NotGreaterEqualFact, NotGreaterFact, NotInFact, NotInjectiveFact, NotIsChoiceFunctionForFact,
    NotIsFiniteSetFact, NotIsNonemptySetFact, NotIsSetFact, NotLessEqualFact, NotLessFact,
    NotNormalAtomicFact, NotPrimeFact, NotProperSubsetFact, NotProperSupersetFact, NotSubsetFact,
    NotSupersetFact, NotSurjectiveFact, OrFact, PlainExistFact, PrimeFact, ProperSubsetFact,
    ProperSupersetFact, QuantifierFreeFact, SubsetFact, SupersetFact, SurjectiveFact,
};
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::FactId;
use std::collections::HashSet;

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
            | AtomicFact::NotSubsetFact(_)
            | AtomicFact::NotSupersetFact(_)
            | AtomicFact::NotProperSubsetFact(_)
            | AtomicFact::NotProperSupersetFact(_)
            | AtomicFact::NotPrimeFact(_)
            | AtomicFact::NotCoprimeFact(_)
            | AtomicFact::NotDvdFact(_)
            | AtomicFact::NotInjectiveFact(_)
            | AtomicFact::NotSurjectiveFact(_)
            | AtomicFact::NotBijectiveFact(_)
            | AtomicFact::NotIsChoiceFunctionForFact(_)
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
        AtomicFact::SubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::SupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::ProperSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotProperSubsetFact(f) => vec![&f.left, &f.right],
        AtomicFact::ProperSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotProperSupersetFact(f) => vec![&f.left, &f.right],
        AtomicFact::PrimeFact(f) => vec![&f.value],
        AtomicFact::NotPrimeFact(f) => vec![&f.value],
        AtomicFact::CoprimeFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotCoprimeFact(f) => vec![&f.left, &f.right],
        AtomicFact::DvdFact(f) => vec![&f.left, &f.right],
        AtomicFact::NotDvdFact(f) => vec![&f.left, &f.right],
        AtomicFact::InjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::NotInjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::SurjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::NotSurjectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::BijectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::NotBijectiveFact(f) => vec![&f.domain, &f.codomain, &f.function],
        AtomicFact::IsChoiceFunctionForFact(f) => {
            vec![&f.index, &f.set, &f.family, &f.choice]
        }
        AtomicFact::NotIsChoiceFunctionForFact(f) => {
            vec![&f.index, &f.set, &f.family, &f.choice]
        }
    }
}

pub fn or_fact_args_ref(or_fact: &OrFact) -> Vec<&Obj> {
    let mut out = Vec::new();
    for branch in &or_fact.facts {
        match branch {
            AndChainAtomicFact::AtomicFact(a) => out.extend(atomic_fact_args_ref(a)),
            AndChainAtomicFact::AndFact(a) => {
                for atomic in &a.facts {
                    out.extend(atomic_fact_args_ref(atomic));
                }
            }
            AndChainAtomicFact::ChainFact(c) => {
                for obj in &c.objs {
                    out.push(obj);
                }
            }
        }
    }
    out
}

pub fn quantifier_free_fact_args_ref(fact: &QuantifierFreeFact) -> Vec<&Obj> {
    match fact {
        QuantifierFreeFact::AtomicFact(a) => atomic_fact_args_ref(a),
        QuantifierFreeFact::AndFact(a) => {
            let mut out = Vec::new();
            for atomic in &a.facts {
                out.extend(atomic_fact_args_ref(atomic));
            }
            out
        }
        QuantifierFreeFact::ChainFact(c) => c.objs.iter().collect(),
        QuantifierFreeFact::OrFact(o) => or_fact_args_ref(o),
    }
}

// Free objs in an exist fact: param-type carriers plus body args that are not binders.
// Example: `exist x N st {x = a}` → free args `[N, a]` (binder `x` skipped).
pub fn plain_exist_fact_free_args_ref(plain: &PlainExistFact) -> Vec<&Obj> {
    let mut binder_ids = HashSet::new();
    for group in &plain.typed_parameters.groups {
        for param in &group.params {
            binder_ids.insert(param.id);
        }
    }
    let mut out = Vec::new();
    for group in &plain.typed_parameters.groups {
        if let ParamType::Obj(obj) = &group.param_type {
            out.push(obj);
        }
    }
    for fact in &plain.facts {
        for obj in quantifier_free_fact_args_ref(fact) {
            if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = obj {
                if binder_ids.contains(id) {
                    continue;
                }
            }
            out.push(obj);
        }
    }
    out
}

pub fn exist_shaped_fact_free_args_ref(exist: &ExistShapedFact) -> Vec<&Obj> {
    plain_exist_fact_free_args_ref(exist.plain())
}

pub fn plain_exist_fact_id(plain: &PlainExistFact) -> FactId {
    plain.fact_id
}

pub fn exist_shaped_fact_id(exist: &ExistShapedFact) -> FactId {
    plain_exist_fact_id(exist.plain())
}

pub fn plain_exist_binder_ids(plain: &PlainExistFact) -> HashSet<IdentifierId> {
    let mut ids = HashSet::new();
    for group in &plain.typed_parameters.groups {
        for param in &group.params {
            ids.insert(param.id);
        }
    }
    ids
}

pub fn exist_shaped_fact_binder_ids(exist: &ExistShapedFact) -> HashSet<IdentifierId> {
    plain_exist_binder_ids(exist.plain())
}

pub fn exist_shaped_fact_to_fact(exist: &ExistShapedFact) -> Fact {
    match exist {
        ExistShapedFact::Exist(p) => Fact::ExistFact(p.clone()),
        ExistShapedFact::ExistUnique(p) => Fact::ExistUniqueFact(p.clone()),
        ExistShapedFact::NotExist(p) => Fact::NotExistFact(p.clone()),
    }
}

pub fn exist_shaped_fact_from_fact(fact: &Fact) -> Option<ExistShapedFact> {
    match fact {
        Fact::ExistFact(p) => Some(ExistShapedFact::Exist(p.clone())),
        Fact::ExistUniqueFact(p) => Some(ExistShapedFact::ExistUnique(p.clone())),
        Fact::NotExistFact(p) => Some(ExistShapedFact::NotExist(p.clone())),
        _ => None,
    }
}

pub fn and_chain_as_fact(branch: &AndChainAtomicFact) -> Fact {
    match branch {
        AndChainAtomicFact::AtomicFact(a) => Fact::AtomicFact(a.clone()),
        AndChainAtomicFact::AndFact(a) => Fact::AndFact(a.clone()),
        AndChainAtomicFact::ChainFact(c) => Fact::ChainFact(c.clone()),
    }
}

// Flip atomic polarity with a fresh FactId.
pub fn negate_atomic_fact(fact: &AtomicFact, new_fact_id: FactId) -> Option<AtomicFact> {
    Some(match fact {
        AtomicFact::NormalAtomicFact(f) => NotNormalAtomicFact {
            fact_id: new_fact_id,
            predicate: f.predicate.clone(),
            body: f.body.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotNormalAtomicFact(f) => NormalAtomicFact {
            fact_id: new_fact_id,
            predicate: f.predicate.clone(),
            body: f.body.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::EqualFact(f) => NotEqualFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotEqualFact(f) => EqualFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::LessFact(f) => NotLessFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotLessFact(f) => LessFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::GreaterFact(f) => NotGreaterFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotGreaterFact(f) => GreaterFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::LessEqualFact(f) => NotLessEqualFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotLessEqualFact(f) => LessEqualFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::GreaterEqualFact(f) => NotGreaterEqualFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotGreaterEqualFact(f) => GreaterEqualFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::IsSetFact(f) => NotIsSetFact {
            fact_id: new_fact_id,
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotIsSetFact(f) => IsSetFact {
            fact_id: new_fact_id,
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::IsNonemptySetFact(f) => NotIsNonemptySetFact {
            fact_id: new_fact_id,
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotIsNonemptySetFact(f) => IsNonemptySetFact {
            fact_id: new_fact_id,
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::IsFiniteSetFact(f) => NotIsFiniteSetFact {
            fact_id: new_fact_id,
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotIsFiniteSetFact(f) => IsFiniteSetFact {
            fact_id: new_fact_id,
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::InFact(f) => NotInFact {
            fact_id: new_fact_id,
            element: f.element.clone(),
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotInFact(f) => InFact {
            fact_id: new_fact_id,
            element: f.element.clone(),
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::SubsetFact(f) => NotSubsetFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotSubsetFact(f) => SubsetFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::SupersetFact(f) => NotSupersetFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotSupersetFact(f) => SupersetFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::ProperSubsetFact(f) => NotProperSubsetFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotProperSubsetFact(f) => ProperSubsetFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::ProperSupersetFact(f) => NotProperSupersetFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotProperSupersetFact(f) => ProperSupersetFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::PrimeFact(f) => NotPrimeFact {
            fact_id: new_fact_id,
            value: f.value.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotPrimeFact(f) => PrimeFact {
            fact_id: new_fact_id,
            value: f.value.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::CoprimeFact(f) => NotCoprimeFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotCoprimeFact(f) => CoprimeFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::DvdFact(f) => NotDvdFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotDvdFact(f) => DvdFact {
            fact_id: new_fact_id,
            left: f.left.clone(),
            right: f.right.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::InjectiveFact(f) => NotInjectiveFact {
            fact_id: new_fact_id,
            domain: f.domain.clone(),
            codomain: f.codomain.clone(),
            function: f.function.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotInjectiveFact(f) => InjectiveFact {
            fact_id: new_fact_id,
            domain: f.domain.clone(),
            codomain: f.codomain.clone(),
            function: f.function.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::SurjectiveFact(f) => NotSurjectiveFact {
            fact_id: new_fact_id,
            domain: f.domain.clone(),
            codomain: f.codomain.clone(),
            function: f.function.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotSurjectiveFact(f) => SurjectiveFact {
            fact_id: new_fact_id,
            domain: f.domain.clone(),
            codomain: f.codomain.clone(),
            function: f.function.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::BijectiveFact(f) => NotBijectiveFact {
            fact_id: new_fact_id,
            domain: f.domain.clone(),
            codomain: f.codomain.clone(),
            function: f.function.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotBijectiveFact(f) => BijectiveFact {
            fact_id: new_fact_id,
            domain: f.domain.clone(),
            codomain: f.codomain.clone(),
            function: f.function.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::IsChoiceFunctionForFact(f) => NotIsChoiceFunctionForFact {
            fact_id: new_fact_id,
            index: f.index.clone(),
            set: f.set.clone(),
            family: f.family.clone(),
            choice: f.choice.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotIsChoiceFunctionForFact(f) => IsChoiceFunctionForFact {
            fact_id: new_fact_id,
            index: f.index.clone(),
            set: f.set.clone(),
            family: f.family.clone(),
            choice: f.choice.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
    })
}
