//! exp on R and ln on R+ preserve and reflect strict and weak order.
use super::less::LessFactSearchProofByBuiltinRule;
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::ast::fact::{LessEqualFact, LessFact};
use crate::ast::obj::{Exp, ExpLogOperator, Ln, Obj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct ExpStrictMonotoneProof {
    pub argument_order: VerifyFactResult,
}
impl ExpStrictMonotoneProof {
    pub fn new(argument_order: VerifyFactResult) -> Self {
        Self { argument_order }
    }
}

pub struct LnStrictMonotoneProof {
    pub argument_order: VerifyFactResult,
}
impl LnStrictMonotoneProof {
    pub fn new(argument_order: VerifyFactResult) -> Self {
        Self { argument_order }
    }
}

pub struct ExpStrictOrderReflectionProof {
    pub image_order: VerifyFactResult,
}
impl ExpStrictOrderReflectionProof {
    pub fn new(image_order: VerifyFactResult) -> Self {
        Self { image_order }
    }
}

pub struct LnStrictOrderReflectionProof {
    pub image_order: VerifyFactResult,
}
impl LnStrictOrderReflectionProof {
    pub fn new(image_order: VerifyFactResult) -> Self {
        Self { image_order }
    }
}

pub struct ExpWeakMonotoneProof {
    pub argument_order: VerifyFactResult,
}
impl ExpWeakMonotoneProof {
    pub fn new(argument_order: VerifyFactResult) -> Self {
        Self { argument_order }
    }
}

pub struct LnWeakMonotoneProof {
    pub argument_order: VerifyFactResult,
}
impl LnWeakMonotoneProof {
    pub fn new(argument_order: VerifyFactResult) -> Self {
        Self { argument_order }
    }
}

pub struct ExpWeakOrderReflectionProof {
    pub image_order: VerifyFactResult,
}
impl ExpWeakOrderReflectionProof {
    pub fn new(image_order: VerifyFactResult) -> Self {
        Self { image_order }
    }
}

pub struct LnWeakOrderReflectionProof {
    pub image_order: VerifyFactResult,
}
impl LnWeakOrderReflectionProof {
    pub fn new(image_order: VerifyFactResult) -> Self {
        Self { image_order }
    }
}

impl Runtime {
    pub(super) fn search_exp_ln_strict_order(
        &mut self,
        fact: &LessFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        // Increasing functions preserve strict order; examples: a < b => exp(a) < exp(b).
        // Parent WD owns the forward exp R / ln R+ argument domains.
        if let (
            Obj::ExpLogOperator(ExpLogOperator::Exp(a)),
            Obj::ExpLogOperator(ExpLogOperator::Exp(b)),
        ) = (&fact.left, &fact.right)
        {
            if let Some(argument_order) =
                self.exp_ln_strict_source_order(&a.arg, &b.arg, fact, state)?
            {
                return Ok(Some(LessFactSearchProofByBuiltinRule::ExpStrictMonotone(
                    ExpStrictMonotoneProof::new(argument_order),
                )));
            }
        }
        if let (
            Obj::ExpLogOperator(ExpLogOperator::Ln(a)),
            Obj::ExpLogOperator(ExpLogOperator::Ln(b)),
        ) = (&fact.left, &fact.right)
        {
            if let Some(argument_order) =
                self.exp_ln_strict_source_order(&a.arg, &b.arg, fact, state)?
            {
                return Ok(Some(LessFactSearchProofByBuiltinRule::LnStrictMonotone(
                    LnStrictMonotoneProof::new(argument_order),
                )));
            }
        }
        // Order reflection consumes checked image-order evidence, including its WD.
        // The inherited premise ceiling cannot enter another builtin, so forward
        // and reflection cannot recursively call each other.
        let exp_left = Obj::ExpLogOperator(ExpLogOperator::Exp(Exp {
            arg: Box::new(fact.left.clone()),
        }));
        let exp_right = Obj::ExpLogOperator(ExpLogOperator::Exp(Exp {
            arg: Box::new(fact.right.clone()),
        }));
        if let Some(image_order) =
            self.exp_ln_strict_source_order(&exp_left, &exp_right, fact, state)?
        {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::ExpStrictOrderReflection(
                    ExpStrictOrderReflectionProof::new(image_order),
                ),
            ));
        }
        let ln_left = Obj::ExpLogOperator(ExpLogOperator::Ln(Ln {
            arg: Box::new(fact.left.clone()),
        }));
        let ln_right = Obj::ExpLogOperator(ExpLogOperator::Ln(Ln {
            arg: Box::new(fact.right.clone()),
        }));
        if let Some(image_order) =
            self.exp_ln_strict_source_order(&ln_left, &ln_right, fact, state)?
        {
            return Ok(Some(
                LessFactSearchProofByBuiltinRule::LnStrictOrderReflection(
                    LnStrictOrderReflectionProof::new(image_order),
                ),
            ));
        }
        Ok(None)
    }

    pub(super) fn search_exp_ln_weak_order(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        // Increasing functions preserve weak order; examples: a <= b => exp(a) <= exp(b).
        // Parent WD owns the forward exp R / ln R+ argument domains.
        if let (
            Obj::ExpLogOperator(ExpLogOperator::Exp(a)),
            Obj::ExpLogOperator(ExpLogOperator::Exp(b)),
        ) = (&fact.left, &fact.right)
        {
            if let Some(argument_order) =
                self.exp_ln_weak_source_order(&a.arg, &b.arg, fact, state)?
            {
                return Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::ExpWeakMonotone(
                        ExpWeakMonotoneProof::new(argument_order),
                    ),
                ));
            }
        }
        if let (
            Obj::ExpLogOperator(ExpLogOperator::Ln(a)),
            Obj::ExpLogOperator(ExpLogOperator::Ln(b)),
        ) = (&fact.left, &fact.right)
        {
            if let Some(argument_order) =
                self.exp_ln_weak_source_order(&a.arg, &b.arg, fact, state)?
            {
                return Ok(Some(LessEqualFactSearchProofByBuiltinRule::LnWeakMonotone(
                    LnWeakMonotoneProof::new(argument_order),
                )));
            }
        }
        // Order reflection consumes checked image-order evidence, including its WD.
        // The inherited premise ceiling cannot enter another builtin, so forward
        // and reflection cannot recursively call each other.
        let exp_left = Obj::ExpLogOperator(ExpLogOperator::Exp(Exp {
            arg: Box::new(fact.left.clone()),
        }));
        let exp_right = Obj::ExpLogOperator(ExpLogOperator::Exp(Exp {
            arg: Box::new(fact.right.clone()),
        }));
        if let Some(image_order) =
            self.exp_ln_weak_source_order(&exp_left, &exp_right, fact, state)?
        {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::ExpWeakOrderReflection(
                    ExpWeakOrderReflectionProof::new(image_order),
                ),
            ));
        }
        let ln_left = Obj::ExpLogOperator(ExpLogOperator::Ln(Ln {
            arg: Box::new(fact.left.clone()),
        }));
        let ln_right = Obj::ExpLogOperator(ExpLogOperator::Ln(Ln {
            arg: Box::new(fact.right.clone()),
        }));
        if let Some(image_order) =
            self.exp_ln_weak_source_order(&ln_left, &ln_right, fact, state)?
        {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::LnWeakOrderReflection(
                    LnWeakOrderReflectionProof::new(image_order),
                ),
            ));
        }
        Ok(None)
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/exp_ln_order/tests.rs"]
mod exp_ln_order_tests;
