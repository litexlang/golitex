use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferAtomicExceptEqualityResult, InferFnEqualInFactResult, InferGreaterEqualFactResult,
    InferGreaterFactResult, InferIsFiniteSetFactResult, InferIsNonemptySetFactResult,
    InferIsSetFactResult, InferIsTupleFactResult, InferLessEqualFactResult, InferLessFactResult,
    InferNotEqualFactResult, InferNotFnEqualInFactResult, InferNotGreaterEqualFactResult,
    InferNotGreaterFactResult, InferNotInFactResult, InferNotIsCartFactResult,
    InferNotIsFiniteSetFactResult, InferNotIsNonemptySetFactResult, InferNotIsSetFactResult,
    InferNotIsTupleFactResult, InferNotLessEqualFactResult, InferNotLessFactResult,
    InferNotNormalAtomicFactResult, InferNotSubsetFactResult, InferNotSupersetFactResult,
    InferSubsetFactResult, InferSupersetFactResult,
};

impl Runtime {
    // Dispatch non-equal atomic infer by fact shape (mirrors AtomicFact except EqualFact).
    pub(crate) fn infer_atomic_except_equality(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> RuntimeResult<InferAtomicExceptEqualityResult> {
        match atomic_fact {
            AtomicFact::EqualFact(_) => unreachable!(
                "equality facts use infer_equal_fact, not infer_atomic_except_equality"
            ),
            AtomicFact::NormalAtomicFact(normal) => Ok(
                InferAtomicExceptEqualityResult::NormalAtomicFact(
                    self.infer_normal_atomic_fact(normal)?,
                ),
            ),
            AtomicFact::LessFact(_) => {
                Ok(InferAtomicExceptEqualityResult::LessFact(InferLessFactResult {}))
            }
            AtomicFact::GreaterFact(_) => Ok(InferAtomicExceptEqualityResult::GreaterFact(
                InferGreaterFactResult {},
            )),
            AtomicFact::LessEqualFact(_) => Ok(InferAtomicExceptEqualityResult::LessEqualFact(
                InferLessEqualFactResult {},
            )),
            AtomicFact::GreaterEqualFact(_) => Ok(InferAtomicExceptEqualityResult::GreaterEqualFact(
                InferGreaterEqualFactResult {},
            )),
            AtomicFact::IsSetFact(_) => {
                Ok(InferAtomicExceptEqualityResult::IsSetFact(InferIsSetFactResult {}))
            }
            AtomicFact::IsNonemptySetFact(_) => Ok(
                InferAtomicExceptEqualityResult::IsNonemptySetFact(InferIsNonemptySetFactResult {}),
            ),
            AtomicFact::IsFiniteSetFact(_) => Ok(InferAtomicExceptEqualityResult::IsFiniteSetFact(
                InferIsFiniteSetFactResult {},
            )),
            AtomicFact::InFact(in_fact) => {
                Ok(InferAtomicExceptEqualityResult::InFact(self.infer_in_fact(in_fact)?))
            }
            AtomicFact::IsCartFact(is_cart) => Ok(InferAtomicExceptEqualityResult::IsCartFact(
                self.infer_is_cart_fact(is_cart)?,
            )),
            AtomicFact::IsTupleFact(_) => {
                Ok(InferAtomicExceptEqualityResult::IsTupleFact(InferIsTupleFactResult {}))
            }
            AtomicFact::SubsetFact(_) => {
                Ok(InferAtomicExceptEqualityResult::SubsetFact(InferSubsetFactResult {}))
            }
            AtomicFact::SupersetFact(_) => Ok(InferAtomicExceptEqualityResult::SupersetFact(
                InferSupersetFactResult {},
            )),
            AtomicFact::NotNormalAtomicFact(_) => Ok(
                InferAtomicExceptEqualityResult::NotNormalAtomicFact(
                    InferNotNormalAtomicFactResult {},
                ),
            ),
            AtomicFact::NotEqualFact(_) => Ok(InferAtomicExceptEqualityResult::NotEqualFact(
                InferNotEqualFactResult {},
            )),
            AtomicFact::NotLessFact(_) => {
                Ok(InferAtomicExceptEqualityResult::NotLessFact(InferNotLessFactResult {}))
            }
            AtomicFact::NotGreaterFact(_) => Ok(InferAtomicExceptEqualityResult::NotGreaterFact(
                InferNotGreaterFactResult {},
            )),
            AtomicFact::NotLessEqualFact(_) => Ok(InferAtomicExceptEqualityResult::NotLessEqualFact(
                InferNotLessEqualFactResult {},
            )),
            AtomicFact::NotGreaterEqualFact(_) => Ok(
                InferAtomicExceptEqualityResult::NotGreaterEqualFact(
                    InferNotGreaterEqualFactResult {},
                ),
            ),
            AtomicFact::NotIsSetFact(_) => Ok(InferAtomicExceptEqualityResult::NotIsSetFact(
                InferNotIsSetFactResult {},
            )),
            AtomicFact::NotIsNonemptySetFact(_) => Ok(
                InferAtomicExceptEqualityResult::NotIsNonemptySetFact(
                    InferNotIsNonemptySetFactResult {},
                ),
            ),
            AtomicFact::NotIsFiniteSetFact(_) => Ok(
                InferAtomicExceptEqualityResult::NotIsFiniteSetFact(
                    InferNotIsFiniteSetFactResult {},
                ),
            ),
            AtomicFact::NotInFact(_) => {
                Ok(InferAtomicExceptEqualityResult::NotInFact(InferNotInFactResult {}))
            }
            AtomicFact::NotIsCartFact(_) => Ok(InferAtomicExceptEqualityResult::NotIsCartFact(
                InferNotIsCartFactResult {},
            )),
            AtomicFact::NotIsTupleFact(_) => Ok(InferAtomicExceptEqualityResult::NotIsTupleFact(
                InferNotIsTupleFactResult {},
            )),
            AtomicFact::NotSubsetFact(_) => Ok(InferAtomicExceptEqualityResult::NotSubsetFact(
                InferNotSubsetFactResult {},
            )),
            AtomicFact::NotSupersetFact(_) => Ok(InferAtomicExceptEqualityResult::NotSupersetFact(
                InferNotSupersetFactResult {},
            )),
            AtomicFact::FnEqualInFact(_) => Ok(InferAtomicExceptEqualityResult::FnEqualInFact(
                InferFnEqualInFactResult {},
            )),
            AtomicFact::NotFnEqualInFact(_) => Ok(
                InferAtomicExceptEqualityResult::NotFnEqualInFact(InferNotFnEqualInFactResult {}),
            ),
        }
    }
}
