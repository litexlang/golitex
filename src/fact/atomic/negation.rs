//! Atomic fact logical negation.

use crate::prelude::*;
impl AtomicFact {
    /// Return the logical negation of an atomic fact.
    ///
    /// Function equality has no negated atomic form in Litex. Swapping its two
    /// sides is symmetry, not negation, so callers must handle that case.
    pub fn logical_negation(&self) -> Result<AtomicFact, RuntimeError> {
        if matches!(
            self,
            AtomicFact::FnEqualInFact(_) | AtomicFact::FnEqualFact(_)
        ) {
            return Err(RuntimeError::from(NewFactRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!("logical negation is not supported for `{}`", self),
                    self.line_file(),
                ),
            )));
        }

        Ok(match self {
            AtomicFact::NormalAtomicFact(a) => AtomicFact::NotNormalAtomicFact(
                NotNormalAtomicFact::new(a.predicate.clone(), a.body.clone(), a.line_file.clone()),
            ),
            AtomicFact::NotNormalAtomicFact(a) => AtomicFact::NormalAtomicFact(
                NormalAtomicFact::new(a.predicate.clone(), a.body.clone(), a.line_file.clone()),
            ),
            AtomicFact::EqualFact(a) => {
                NotEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::LessFact(a) => {
                NotLessFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::GreaterFact(a) => {
                NotGreaterFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::LessEqualFact(a) => {
                NotLessEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::GreaterEqualFact(a) => AtomicFact::NotGreaterEqualFact(
                NotGreaterEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()),
            ),
            AtomicFact::IsSetFact(a) => {
                NotIsSetFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::IsNonemptySetFact(a) => AtomicFact::NotIsNonemptySetFact(
                NotIsNonemptySetFact::new(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::IsFiniteSetFact(a) => AtomicFact::NotIsFiniteSetFact(
                NotIsFiniteSetFact::new(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::InFact(a) => {
                NotInFact::new(a.element.clone(), a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::IsCartFact(a) => {
                NotIsCartFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::IsTupleFact(a) => {
                NotIsTupleFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::SubsetFact(a) => {
                NotSubsetFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::SupersetFact(a) => {
                NotSupersetFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotEqualFact(a) => {
                EqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotLessFact(a) => {
                LessFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotGreaterFact(a) => {
                GreaterFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotLessEqualFact(a) => {
                LessEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotGreaterEqualFact(a) => AtomicFact::GreaterEqualFact(
                GreaterEqualFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()),
            ),
            AtomicFact::NotIsSetFact(a) => {
                IsSetFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotIsNonemptySetFact(a) => AtomicFact::IsNonemptySetFact(
                IsNonemptySetFact::new(a.set.clone(), a.line_file.clone()),
            ),
            AtomicFact::NotIsFiniteSetFact(a) => {
                IsFiniteSetFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotInFact(a) => {
                InFact::new(a.element.clone(), a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotIsCartFact(a) => {
                IsCartFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotIsTupleFact(a) => {
                IsTupleFact::new(a.set.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotSubsetFact(a) => {
                SubsetFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::NotSupersetFact(a) => {
                SupersetFact::new(a.left.clone(), a.right.clone(), a.line_file.clone()).into()
            }
            AtomicFact::FnEqualInFact(_) | AtomicFact::FnEqualFact(_) => {
                unreachable!("function equality is handled before logical negation")
            }
        })
    }
}
