//! Fixed scalar sign properties; all calls keep the inherited premise state.
use super::{
    less::LessFactSearchProofByBuiltinRule as L,
    less_equal::LessEqualFactSearchProofByBuiltinRule as W,
};
use crate::ast::fact::{LessEqualFact, LessFact};
use crate::ast::obj::{ArithmeticOperator as A, ExpLogOperator as E, Obj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::exact_rational::EvalRational;
use crate::runtime::{Runtime, RuntimeResult};
pub struct ProductPositiveNegativeStrictProof {
    pub positive_factor: VerifyFactResult,
    pub negative_factor: VerifyFactResult,
}
pub struct ProductNonnegativeNegativeWeakProof {
    pub nonnegative_factor: VerifyFactResult,
    pub negative_factor: VerifyFactResult,
}
pub struct LnPositiveAboveOneProof {
    pub above_one: AtomicExceptEqualityFactKnownProof,
}
pub struct LnNegativeBelowOneProof {
    pub below_one: AtomicExceptEqualityFactKnownProof,
}
impl Runtime {
    pub(super) fn scalar_extra_less(
        &mut self,
        f: &LessFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<L>> {
        if zero(&f.right) {
            if let Obj::ArithmeticOperator(A::Mul(m)) = &f.left {
                for (a, b) in [(&*m.left, &*m.right), (&*m.right, &*m.left)] {
                    let positive_factor = self.verify_order_positive(a, state)?;
                    if positive_factor.is_failed() {
                        continue;
                    }
                    let negative_factor = self.verify_order_negative(b, state)?;
                    if !negative_factor.is_failed() {
                        return Ok(Some(L::ProductPositiveNegativeStrict(
                            ProductPositiveNegativeStrictProof::new(
                                positive_factor,
                                negative_factor,
                            ),
                        )));
                    }
                }
            }
            if let Obj::ExpLogOperator(E::Ln(l)) = &f.left {
                let one = crate::ast::obj::Obj::Literal(crate::ast::obj::Literal::Number(
                    crate::ast::obj::Number::new("1".into()),
                ));
                if let Some(below_one) = self.known_integer_interval_order(&l.arg, &one, true) {
                    return Ok(Some(L::LnNegativeBelowOne(LnNegativeBelowOneProof::new(
                        below_one,
                    ))));
                }
            }
        }
        if zero(&f.left) {
            if let Obj::ExpLogOperator(E::Ln(l)) = &f.right {
                let one = crate::ast::obj::Obj::Literal(crate::ast::obj::Literal::Number(
                    crate::ast::obj::Number::new("1".into()),
                ));
                if let Some(above_one) = self.known_integer_interval_order(&one, &l.arg, true) {
                    return Ok(Some(L::LnPositiveAboveOne(LnPositiveAboveOneProof::new(
                        above_one,
                    ))));
                }
            }
        }
        Ok(None)
    }
    pub(super) fn scalar_extra_weak(
        &mut self,
        f: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<W>> {
        if zero(&f.right) {
            if let Obj::ArithmeticOperator(A::Mul(m)) = &f.left {
                for (a, b) in [(&*m.left, &*m.right), (&*m.right, &*m.left)] {
                    let nonnegative_factor = self.verify_order_nonnegative(a, state)?;
                    if nonnegative_factor.is_failed() {
                        continue;
                    }
                    let negative_factor = self.verify_order_negative(b, state)?;
                    if !negative_factor.is_failed() {
                        return Ok(Some(W::ProductNonnegativeNegativeWeak(
                            ProductNonnegativeNegativeWeakProof::new(
                                nonnegative_factor,
                                negative_factor,
                            ),
                        )));
                    }
                }
            }
        }
        Ok(None)
    }
}
fn zero(o: &Obj) -> bool {
    EvalRational::from_obj(o).is_some_and(|n| n.is_zero())
}

impl ProductPositiveNegativeStrictProof {
    pub fn new(positive_factor: VerifyFactResult, negative_factor: VerifyFactResult) -> Self {
        Self {
            positive_factor,
            negative_factor,
        }
    }
}

impl ProductNonnegativeNegativeWeakProof {
    pub fn new(nonnegative_factor: VerifyFactResult, negative_factor: VerifyFactResult) -> Self {
        Self {
            nonnegative_factor,
            negative_factor,
        }
    }
}

impl LnPositiveAboveOneProof {
    pub fn new(above_one: AtomicExceptEqualityFactKnownProof) -> Self {
        Self { above_one }
    }
}

impl LnNegativeBelowOneProof {
    pub fn new(below_one: AtomicExceptEqualityFactKnownProof) -> Self {
        Self { below_one }
    }
}
