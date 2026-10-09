//! Squaring reflects weak order between two nonnegative real operands.
use crate::prelude::*;

pub struct NonnegativeSquareOrderReflectionProof {
    pub left_nonnegative: VerifyFactResult,
    pub right_nonnegative: VerifyFactResult,
    pub squared_order: VerifyFactResult,
}

impl NonnegativeSquareOrderReflectionProof {
    pub fn new(
        left_nonnegative: VerifyFactResult,
        right_nonnegative: VerifyFactResult,
        squared_order: VerifyFactResult,
    ) -> Self {
        Self {
            left_nonnegative,
            right_nonnegative,
            squared_order,
        }
    }
}

impl From<NonnegativeSquareOrderReflectionProof> for LessEqualFactSearchProofByBuiltinRule {
    fn from(proof: NonnegativeSquareOrderReflectionProof) -> Self {
        Self::NonnegativeSquareOrderReflection(proof)
    }
}

impl Runtime {
    pub(super) fn search_nonnegative_square_order_reflection(
        &mut self,
        fact: &LessEqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        // 0 <= x, 0 <= y, x^2 <= y^2 => x <= y.
        // Parent comparison WD owns real domains. All three guards retain
        // their actual source direction and the inherited premise ceiling.
        let exponent = Obj::Literal(Literal::Number(Number::new("2".into())));
        let left_square = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: Box::new(fact.left.clone()),
            exponent: Box::new(exponent.clone()),
        }));
        let right_square = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: Box::new(fact.right.clone()),
            exponent: Box::new(exponent),
        }));
        let Some(squared_order) =
            self.weak_order_premise(&left_square, &right_square, fact.line_file.clone(), state)?
        else {
            return Ok(None);
        };
        let left_nonnegative = self.verify_order_nonnegative(&fact.left, state)?;
        if left_nonnegative.is_failed() {
            return Ok(None);
        }
        let right_nonnegative = self.verify_order_nonnegative(&fact.right, state)?;
        if right_nonnegative.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NonnegativeSquareOrderReflectionProof::new(
                left_nonnegative,
                right_nonnegative,
                squared_order,
            )
            .into(),
        ))
    }
}
