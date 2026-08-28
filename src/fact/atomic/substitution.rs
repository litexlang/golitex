//! Capture-aware atomic fact substitution.

use crate::prelude::*;
impl AtomicFact {
    pub fn replace_bound_identifier(self, from: &str, to: &str) -> Self {
        if from == to {
            return self;
        }
        fn r(o: Obj, from: &str, to: &str) -> Obj {
            Obj::replace_bound_identifier(o, from, to)
        }
        match self {
            AtomicFact::NormalAtomicFact(x) => NormalAtomicFact::new(
                x.predicate,
                x.body.into_iter().map(|o| r(o, from, to)).collect(),
                x.line_file,
            )
            .into(),
            AtomicFact::EqualFact(x) => {
                EqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::LessFact(x) => {
                LessFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::GreaterFact(x) => {
                GreaterFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::LessEqualFact(x) => {
                LessEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::GreaterEqualFact(x) => {
                GreaterEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::IsSetFact(x) => IsSetFact::new(r(x.set, from, to), x.line_file).into(),
            AtomicFact::IsNonemptySetFact(x) => {
                IsNonemptySetFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::IsFiniteSetFact(x) => {
                IsFiniteSetFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::InFact(x) => {
                InFact::new(r(x.element, from, to), r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::IsCartFact(x) => IsCartFact::new(r(x.set, from, to), x.line_file).into(),
            AtomicFact::IsTupleFact(x) => IsTupleFact::new(r(x.set, from, to), x.line_file).into(),
            AtomicFact::SubsetFact(x) => {
                SubsetFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::SupersetFact(x) => {
                SupersetFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotNormalAtomicFact(x) => NotNormalAtomicFact::new(
                x.predicate,
                x.body.into_iter().map(|o| r(o, from, to)).collect(),
                x.line_file,
            )
            .into(),
            AtomicFact::NotEqualFact(x) => {
                NotEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotLessFact(x) => {
                NotLessFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotGreaterFact(x) => {
                NotGreaterFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotLessEqualFact(x) => {
                NotLessEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotGreaterEqualFact(x) => {
                NotGreaterEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file)
                    .into()
            }
            AtomicFact::NotIsSetFact(x) => {
                NotIsSetFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotIsNonemptySetFact(x) => {
                NotIsNonemptySetFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotIsFiniteSetFact(x) => {
                NotIsFiniteSetFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotInFact(x) => {
                NotInFact::new(r(x.element, from, to), r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotIsCartFact(x) => {
                NotIsCartFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotIsTupleFact(x) => {
                NotIsTupleFact::new(r(x.set, from, to), x.line_file).into()
            }
            AtomicFact::NotSubsetFact(x) => {
                NotSubsetFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::NotSupersetFact(x) => {
                NotSupersetFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
            AtomicFact::FnEqualInFact(x) => FnEqualInFact::new(
                r(x.left, from, to),
                r(x.right, from, to),
                r(x.set, from, to),
                x.line_file,
            )
            .into(),
            AtomicFact::FnEqualFact(x) => {
                FnEqualFact::new(r(x.left, from, to), r(x.right, from, to), x.line_file).into()
            }
        }
    }
}
