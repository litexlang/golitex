//! Real sign and binary extrema preserve weak order.
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::ast::fact::{Fact, GreaterEqualFact, LessEqualFact};
use crate::ast::obj::{ArithmeticOperator, Obj};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::rational_expression::exact_rational::EvalRational;
use crate::runtime::{Runtime, RuntimeResult};

pub struct SignLowerBoundProof;
pub struct SignUpperBoundProof;
pub struct MinLowerBoundProof;
pub struct MaxUpperBoundProof;

pub enum WeakOrderArgumentProof {
    SameArgument(Obj),
    ByOrder(Box<VerifyFactResult>),
}

pub struct SignWeakMonotoneProof {
    pub argument_order: WeakOrderArgumentProof,
}
impl SignWeakMonotoneProof {
    pub fn new(argument_order: WeakOrderArgumentProof) -> Self {
        Self { argument_order }
    }
}
pub struct MinWeakMonotoneProof {
    pub left_order: WeakOrderArgumentProof,
    pub right_order: WeakOrderArgumentProof,
}
impl MinWeakMonotoneProof {
    pub fn new(left_order: WeakOrderArgumentProof, right_order: WeakOrderArgumentProof) -> Self {
        Self {
            left_order,
            right_order,
        }
    }
}
pub struct MaxWeakMonotoneProof {
    pub left_order: WeakOrderArgumentProof,
    pub right_order: WeakOrderArgumentProof,
}
impl MaxWeakMonotoneProof {
    pub fn new(left_order: WeakOrderArgumentProof, right_order: WeakOrderArgumentProof) -> Self {
        Self {
            left_order,
            right_order,
        }
    }
}

impl Runtime {
    pub(super) fn search_sign_extremum_weak_order(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        use ArithmeticOperator as A;
        use LessEqualFactSearchProofByBuiltinRule as P;
        // -1<=sign(x)<=1 for real x. The parent fact WD checks x in R.
        // Example: forall x R: -1<=sign(x).
        if matches!(&fact.right, Obj::ArithmeticOperator(A::Sign(_)))
            && EvalRational::from_obj(&fact.left) == EvalRational::new(-1, 1)
        {
            return Ok(Some(P::SignLowerBound(SignLowerBoundProof)));
        }
        if matches!(&fact.left, Obj::ArithmeticOperator(A::Sign(_)))
            && EvalRational::from_obj(&fact.right) == EvalRational::new(1, 1)
        {
            return Ok(Some(P::SignUpperBound(SignUpperBoundProof)));
        }
        // Binary min lies below each operand; max lies above each operand.
        // Example: min(a,b)<=a and b<=max(a,b), for real a,b.
        if let Obj::ArithmeticOperator(A::Min(m)) = &fact.left {
            if fact.right.ir() == m.left.ir() || fact.right.ir() == m.right.ir() {
                return Ok(Some(P::MinLowerBound(MinLowerBoundProof)));
            }
        }
        if let Obj::ArithmeticOperator(A::Max(m)) = &fact.right {
            if fact.left.ir() == m.left.ir() || fact.left.ir() == m.right.ir() {
                return Ok(Some(P::MaxUpperBound(MaxUpperBoundProof)));
            }
        }
        // Weak order is preserved, never reflected: sign(a)<=sign(b) does
        // not imply a<=b. All generated orders use the inherited ceiling.
        if let (Obj::ArithmeticOperator(A::Sign(a)), Obj::ArithmeticOperator(A::Sign(b))) =
            (&fact.left, &fact.right)
        {
            if let Some(argument_order) = self.sign_extremum_order_premise(&a.arg, &b.arg, state)? {
                return Ok(Some(P::SignWeakMonotone(SignWeakMonotoneProof::new(
                    argument_order,
                ))));
            }
        }
        // a<=c, b<=d => min(a,b)<=min(c,d), and likewise max.
        // Parent WD owns all four real domains; retain both actual premises.
        match (&fact.left, &fact.right) {
            (Obj::ArithmeticOperator(A::Min(a)), Obj::ArithmeticOperator(A::Min(b))) => {
                let Some(left_order) = self.sign_extremum_order_premise(&a.left, &b.left, state)?
                else {
                    return Ok(None);
                };
                let Some(right_order) =
                    self.sign_extremum_order_premise(&a.right, &b.right, state)?
                else {
                    return Ok(None);
                };
                return Ok(Some(P::MinWeakMonotone(MinWeakMonotoneProof::new(
                    left_order,
                    right_order,
                ))));
            }
            (Obj::ArithmeticOperator(A::Max(a)), Obj::ArithmeticOperator(A::Max(b))) => {
                let Some(left_order) = self.sign_extremum_order_premise(&a.left, &b.left, state)?
                else {
                    return Ok(None);
                };
                let Some(right_order) =
                    self.sign_extremum_order_premise(&a.right, &b.right, state)?
                else {
                    return Ok(None);
                };
                return Ok(Some(P::MaxWeakMonotone(MaxWeakMonotoneProof::new(
                    left_order,
                    right_order,
                ))));
            }
            _ => {}
        }
        Ok(None)
    }

    fn sign_extremum_order_premise(
        &mut self,
        left: &Obj,
        right: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<WeakOrderArgumentProof>> {
        // A fixed argument needs identity evidence, not another search stage.
        // Example: a<=b => min(a,c)<=min(b,c). Parent WD owns c in R.
        if left.ir() == right.ir() {
            return Ok(Some(WeakOrderArgumentProof::SameArgument(left.clone())));
        }
        let premise: Fact = LessEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&premise, state)?;
        if !proof.is_failed() {
            return Ok(Some(WeakOrderArgumentProof::ByOrder(Box::new(proof))));
        }
        let reverse: Fact = GreaterEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: right.clone(),
            right: left.clone(),
            line_file: None,
        }
        .into();
        let proof = self.verify_builtin_rule_premise(&reverse, state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(WeakOrderArgumentProof::ByOrder(Box::new(proof))))
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/legacy_six_simple_bt/tests.rs"]
mod legacy_six_simple_bt_tests;
