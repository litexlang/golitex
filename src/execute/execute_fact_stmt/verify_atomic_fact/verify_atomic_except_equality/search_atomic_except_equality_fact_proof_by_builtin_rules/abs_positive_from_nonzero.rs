//! A nonzero real argument has strictly positive absolute value.
use crate::prelude::*;

pub struct AbsPositiveFromNonzeroProof {
    pub argument_nonzero: VerifyFactResult,
}

impl AbsPositiveFromNonzeroProof {
    pub fn new(argument_nonzero: VerifyFactResult) -> Self {
        Self { argument_nonzero }
    }
}

impl From<AbsPositiveFromNonzeroProof> for LessFactSearchProofByBuiltinRule {
    fn from(proof: AbsPositiveFromNonzeroProof) -> Self {
        Self::AbsPositiveFromNonzero(proof)
    }
}

impl Runtime {
    pub(super) fn search_abs_positive_from_nonzero(
        &mut self,
        fact: &LessFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        // x != 0 => 0 < abs(x). Parent WD establishes that x is real.
        // Only the argument's nonzero premise is checked, at the inherited
        // builtin premise ceiling; no sign cases or intermediate proofs search.
        if !EvalRational::from_obj(&fact.left).is_some_and(|value| value.is_zero()) {
            return Ok(None);
        }
        let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = &fact.right else {
            return Ok(None);
        };
        let argument_nonzero = self.verify_order_nonzero(&abs.arg, state)?;
        if argument_nonzero.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            AbsPositiveFromNonzeroProof::new(argument_nonzero).into(),
        ))
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/abs_positive_square_reflection/tests.rs"]
mod abs_positive_square_reflection_tests;
