use super::{
    AndChainAtomicFact, AtomicFact, EqualFact, Fact, GreaterEqualFact, GreaterFact, InFact,
    IsCartFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact, IsTupleFact, LessEqualFact,
    LessFact, NormalAtomicFact, NotEqualFact, NotGreaterEqualFact, NotGreaterFact, NotInFact,
    NotIsCartFact, NotIsFiniteSetFact, NotIsNonemptySetFact, NotIsSetFact, NotIsTupleFact,
    NotLessEqualFact, NotLessFact, NotNormalAtomicFact, NotSubsetFact, NotSupersetFact, OrFact,
    SubsetFact, SupersetFact,
};
use super::super::obj::Obj;
use crate::new_pipeline::runtime::FactId;

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

pub fn and_chain_as_fact(branch: &AndChainAtomicFact) -> Fact {
    match branch {
        AndChainAtomicFact::AtomicFact(a) => Fact::AtomicFact(a.clone()),
        AndChainAtomicFact::AndFact(a) => Fact::AndFact(a.clone()),
        AndChainAtomicFact::ChainFact(c) => Fact::ChainFact(c.clone()),
    }
}

// Flip atomic polarity with a fresh FactId. FnEqual* has no not-form → None.
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
        AtomicFact::IsCartFact(f) => NotIsCartFact {
            fact_id: new_fact_id,
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotIsCartFact(f) => IsCartFact {
            fact_id: new_fact_id,
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::IsTupleFact(f) => NotIsTupleFact {
            fact_id: new_fact_id,
            set: f.set.clone(),
            line_file: f.line_file.clone(),
        }
        .into(),
        AtomicFact::NotIsTupleFact(f) => IsTupleFact {
            fact_id: new_fact_id,
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
        AtomicFact::FnEqualFact(_) | AtomicFact::FnEqualInFact(_) => return None,
    })
}
