//! One-layer positive-real and nonzero-rational product/quotient closure.
use super::InFactSearchProofByBuiltinRule;
use crate::ast::fact::{Fact, InFact};
use crate::ast::obj::{ArithmeticOperator, Obj, StandardSet};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

pub struct PositiveRealProductProof {
    pub left_positive: VerifyFactResult,
    pub right_positive: VerifyFactResult,
}
impl PositiveRealProductProof {
    pub fn new(left_positive: VerifyFactResult, right_positive: VerifyFactResult) -> Self { Self { left_positive, right_positive } }
}
pub struct PositiveRealQuotientProof {
    pub numerator_positive: VerifyFactResult,
    pub denominator_positive: VerifyFactResult,
}
impl PositiveRealQuotientProof {
    pub fn new(numerator_positive: VerifyFactResult, denominator_positive: VerifyFactResult) -> Self { Self { numerator_positive, denominator_positive } }
}
pub struct NonzeroRationalProductProof {
    pub left_nonzero_rational: VerifyFactResult,
    pub right_nonzero_rational: VerifyFactResult,
}
impl NonzeroRationalProductProof {
    pub fn new(left_nonzero_rational: VerifyFactResult, right_nonzero_rational: VerifyFactResult) -> Self { Self { left_nonzero_rational, right_nonzero_rational } }
}
pub struct NonzeroRationalQuotientProof {
    pub numerator_nonzero_rational: VerifyFactResult,
    pub denominator_nonzero_rational: VerifyFactResult,
}
impl NonzeroRationalQuotientProof {
    pub fn new(numerator_nonzero_rational: VerifyFactResult, denominator_nonzero_rational: VerifyFactResult) -> Self { Self { numerator_nonzero_rational, denominator_nonzero_rational } }
}
impl Runtime {
    pub(super) fn scalar_refined_product(
        &mut self, fact: &InFact, state: VerifyState,
    ) -> RuntimeResult<Option<InFactSearchProofByBuiltinRule>> {
        use InFactSearchProofByBuiltinRule as P;
        let (left, right, quotient) = match &fact.element {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) => (&*product.left, &*product.right, false),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) => (&*div.left, &*div.right, true),
            _ => return Ok(None),
        };
        let set = match &fact.set {
            Obj::StandardSet(StandardSet::RPos) => StandardSet::RPos,
            Obj::StandardSet(StandardSet::QStar) => StandardSet::QStar,
            _ => return Ok(None),
        };
        // Both operands must have the exact refinement. The same inherited
        // ceiling is used for each; this is not recursive refined typing.
        // Example: a,b R+ => a/b in R+; a,b Q* => a*b in Q*.
        let requirement: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(), element: left.clone(),
            set: Obj::StandardSet(set.clone()), line_file: fact.line_file.clone(),
        }.into();
        let left_proof = self.verify_builtin_rule_premise(&requirement, state)?;
        if left_proof.is_failed() { return Ok(None); }
        let requirement: Fact = InFact {
            fact_id: self.global_ids.allocate_fact_id(), element: right.clone(),
            set: Obj::StandardSet(set.clone()), line_file: fact.line_file.clone(),
        }.into();
        let right_proof = self.verify_builtin_rule_premise(&requirement, state)?;
        if right_proof.is_failed() { return Ok(None); }
        Ok(Some(match (set, quotient) {
            (StandardSet::RPos, false) => P::PositiveRealProduct(PositiveRealProductProof::new(left_proof, right_proof)),
            (StandardSet::RPos, true) => P::PositiveRealQuotient(PositiveRealQuotientProof::new(left_proof, right_proof)),
            (StandardSet::QStar, false) => P::NonzeroRationalProduct(NonzeroRationalProductProof::new(left_proof, right_proof)),
            (StandardSet::QStar, true) => P::NonzeroRationalQuotient(NonzeroRationalQuotientProof::new(left_proof, right_proof)),
            _ => unreachable!("validated refined carrier"),
        }))
    }
}
