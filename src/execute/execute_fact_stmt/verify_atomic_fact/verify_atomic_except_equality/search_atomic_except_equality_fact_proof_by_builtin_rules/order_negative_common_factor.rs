//! Negative factors reverse strict real order; nonpositive factors reverse weak order.
//! All four product placements are fixed surface rules, each with its own evidence.
use crate::ast::fact::{Fact, LessFact, GreaterFact, LessEqualFact, GreaterEqualFact};
use crate::ast::obj::{Obj, ArithmeticOperator};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_inverse_trig::zero_obj;
use crate::runtime::{Runtime, RuntimeResult};
use super::less::LessFactSearchProofByBuiltinRule;
use super::greater::GreaterFactSearchProofByBuiltinRule;
use super::less_equal::LessEqualFactSearchProofByBuiltinRule;
use super::greater_equal::GreaterEqualFactSearchProofByBuiltinRule;

// Real multiplication: c<0, b<a => c*a<c*b.
pub struct MulLeftNegativeReversesStrictLessProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<0, b<a => a*c<b*c.
pub struct MulRightNegativeReversesStrictLessProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<0, b<a => c*a<b*c.
pub struct MulLeftRightNegativeReversesStrictLessProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<0, b<a => a*c<c*b.
pub struct MulRightLeftNegativeReversesStrictLessProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<0, a<b => c*a>c*b.
pub struct MulLeftNegativeReversesStrictGreaterProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<0, a<b => a*c>b*c.
pub struct MulRightNegativeReversesStrictGreaterProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<0, a<b => c*a>b*c.
pub struct MulLeftRightNegativeReversesStrictGreaterProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<0, a<b => a*c>c*b.
pub struct MulRightLeftNegativeReversesStrictGreaterProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<=0, b<=a => c*a<=c*b.
pub struct MulLeftNonpositiveReversesWeakLessEqualProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<=0, b<=a => a*c<=b*c.
pub struct MulRightNonpositiveReversesWeakLessEqualProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<=0, b<=a => c*a<=b*c.
pub struct MulLeftRightNonpositiveReversesWeakLessEqualProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<=0, b<=a => a*c<=c*b.
pub struct MulRightLeftNonpositiveReversesWeakLessEqualProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<=0, a<=b => c*a>=c*b.
pub struct MulLeftNonpositiveReversesWeakGreaterEqualProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<=0, a<=b => a*c>=b*c.
pub struct MulRightNonpositiveReversesWeakGreaterEqualProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<=0, a<=b => c*a>=b*c.
pub struct MulLeftRightNonpositiveReversesWeakGreaterEqualProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

// Real multiplication: c<=0, a<=b => a*c>=c*b.
pub struct MulRightLeftNonpositiveReversesWeakGreaterEqualProof {
    pub factor_sign_proof: VerifyFactResult,
    pub reversed_order_proof: VerifyFactResult,
}

impl Runtime {
    pub(super) fn search_negative_common_factor_less(&mut self, fact: &LessFact, state: VerifyState)
        -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let (Obj::ArithmeticOperator(ArithmeticOperator::Mul(left)), Obj::ArithmeticOperator(ArithmeticOperator::Mul(right))) = (&fact.left, &fact.right) else { return Ok(None); };
        if left.left.ir() == right.left.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.left.as_ref(), right.right.as_ref(), left.right.as_ref(), false, state)? {
                return Ok(Some(LessFactSearchProofByBuiltinRule::MulLeftNegativeReversesStrictLess(MulLeftNegativeReversesStrictLessProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.right.ir() == right.right.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.right.as_ref(), right.left.as_ref(), left.left.as_ref(), false, state)? {
                return Ok(Some(LessFactSearchProofByBuiltinRule::MulRightNegativeReversesStrictLess(MulRightNegativeReversesStrictLessProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.left.ir() == right.right.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.left.as_ref(), right.left.as_ref(), left.right.as_ref(), false, state)? {
                return Ok(Some(LessFactSearchProofByBuiltinRule::MulLeftRightNegativeReversesStrictLess(MulLeftRightNegativeReversesStrictLessProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.right.ir() == right.left.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.right.as_ref(), right.right.as_ref(), left.left.as_ref(), false, state)? {
                return Ok(Some(LessFactSearchProofByBuiltinRule::MulRightLeftNegativeReversesStrictLess(MulRightLeftNegativeReversesStrictLessProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        Ok(None)
    }

    pub(super) fn search_negative_common_factor_greater(&mut self, fact: &GreaterFact, state: VerifyState)
        -> RuntimeResult<Option<GreaterFactSearchProofByBuiltinRule>> {
        let (Obj::ArithmeticOperator(ArithmeticOperator::Mul(left)), Obj::ArithmeticOperator(ArithmeticOperator::Mul(right))) = (&fact.left, &fact.right) else { return Ok(None); };
        if left.left.ir() == right.left.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.left.as_ref(), left.right.as_ref(), right.right.as_ref(), false, state)? {
                return Ok(Some(GreaterFactSearchProofByBuiltinRule::MulLeftNegativeReversesStrictGreater(MulLeftNegativeReversesStrictGreaterProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.right.ir() == right.right.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.right.as_ref(), left.left.as_ref(), right.left.as_ref(), false, state)? {
                return Ok(Some(GreaterFactSearchProofByBuiltinRule::MulRightNegativeReversesStrictGreater(MulRightNegativeReversesStrictGreaterProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.left.ir() == right.right.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.left.as_ref(), left.right.as_ref(), right.left.as_ref(), false, state)? {
                return Ok(Some(GreaterFactSearchProofByBuiltinRule::MulLeftRightNegativeReversesStrictGreater(MulLeftRightNegativeReversesStrictGreaterProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.right.ir() == right.left.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.right.as_ref(), left.left.as_ref(), right.right.as_ref(), false, state)? {
                return Ok(Some(GreaterFactSearchProofByBuiltinRule::MulRightLeftNegativeReversesStrictGreater(MulRightLeftNegativeReversesStrictGreaterProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        Ok(None)
    }

    pub(super) fn search_negative_common_factor_less_equal(&mut self, fact: &LessEqualFact, state: VerifyState)
        -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let (Obj::ArithmeticOperator(ArithmeticOperator::Mul(left)), Obj::ArithmeticOperator(ArithmeticOperator::Mul(right))) = (&fact.left, &fact.right) else { return Ok(None); };
        if left.left.ir() == right.left.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.left.as_ref(), right.right.as_ref(), left.right.as_ref(), true, state)? {
                return Ok(Some(LessEqualFactSearchProofByBuiltinRule::MulLeftNonpositiveReversesWeakLessEqual(MulLeftNonpositiveReversesWeakLessEqualProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.right.ir() == right.right.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.right.as_ref(), right.left.as_ref(), left.left.as_ref(), true, state)? {
                return Ok(Some(LessEqualFactSearchProofByBuiltinRule::MulRightNonpositiveReversesWeakLessEqual(MulRightNonpositiveReversesWeakLessEqualProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.left.ir() == right.right.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.left.as_ref(), right.left.as_ref(), left.right.as_ref(), true, state)? {
                return Ok(Some(LessEqualFactSearchProofByBuiltinRule::MulLeftRightNonpositiveReversesWeakLessEqual(MulLeftRightNonpositiveReversesWeakLessEqualProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.right.ir() == right.left.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.right.as_ref(), right.right.as_ref(), left.left.as_ref(), true, state)? {
                return Ok(Some(LessEqualFactSearchProofByBuiltinRule::MulRightLeftNonpositiveReversesWeakLessEqual(MulRightLeftNonpositiveReversesWeakLessEqualProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        Ok(None)
    }

    pub(super) fn search_negative_common_factor_greater_equal(&mut self, fact: &GreaterEqualFact, state: VerifyState)
        -> RuntimeResult<Option<GreaterEqualFactSearchProofByBuiltinRule>> {
        let (Obj::ArithmeticOperator(ArithmeticOperator::Mul(left)), Obj::ArithmeticOperator(ArithmeticOperator::Mul(right))) = (&fact.left, &fact.right) else { return Ok(None); };
        if left.left.ir() == right.left.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.left.as_ref(), left.right.as_ref(), right.right.as_ref(), true, state)? {
                return Ok(Some(GreaterEqualFactSearchProofByBuiltinRule::MulLeftNonpositiveReversesWeakGreaterEqual(MulLeftNonpositiveReversesWeakGreaterEqualProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.right.ir() == right.right.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.right.as_ref(), left.left.as_ref(), right.left.as_ref(), true, state)? {
                return Ok(Some(GreaterEqualFactSearchProofByBuiltinRule::MulRightNonpositiveReversesWeakGreaterEqual(MulRightNonpositiveReversesWeakGreaterEqualProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.left.ir() == right.right.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.left.as_ref(), left.right.as_ref(), right.left.as_ref(), true, state)? {
                return Ok(Some(GreaterEqualFactSearchProofByBuiltinRule::MulLeftRightNonpositiveReversesWeakGreaterEqual(MulLeftRightNonpositiveReversesWeakGreaterEqualProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        if left.right.ir() == right.left.ir() {
            if let Some((factor_sign_proof, reversed_order_proof)) = self.verify_negative_common_factor_requirements(left.right.as_ref(), left.left.as_ref(), right.right.as_ref(), true, state)? {
                return Ok(Some(GreaterEqualFactSearchProofByBuiltinRule::MulRightLeftNonpositiveReversesWeakGreaterEqual(MulRightLeftNonpositiveReversesWeakGreaterEqualProof { factor_sign_proof, reversed_order_proof })));
            }
        }
        Ok(None)
    }

    // Mandatory stage order: sign first, reversed argument comparison second.
    // The inherited premise state is forwarded unchanged to each fixed alternative.
    fn verify_negative_common_factor_requirements(&mut self, factor: &Obj, smaller: &Obj, larger: &Obj, weak: bool, state: VerifyState)
        -> RuntimeResult<Option<(VerifyFactResult, VerifyFactResult)>> {
        let Some(factor_sign_proof) = self.verify_fixed_order_requirement(factor, &zero_obj(), weak, state)? else { return Ok(None); };
        let Some(reversed_order_proof) = self.verify_fixed_order_requirement(smaller, larger, weak, state)? else { return Ok(None); };
        Ok(Some((factor_sign_proof, reversed_order_proof)))
    }

    // <= may use an actual strict premise as stronger evidence. Strict goals never
    // accept weak premises. Return the verified chosen fact, not a fabricated normal.
    fn verify_fixed_order_requirement(&mut self, left: &Obj, right: &Obj, weak: bool, state: VerifyState)
        -> RuntimeResult<Option<VerifyFactResult>> {
        let mut candidates: Vec<Fact> = Vec::new();
        if weak {
            candidates.push(LessEqualFact { fact_id: self.global_ids.allocate_fact_id(), left: left.clone(), right: right.clone(), line_file: None }.into());
            candidates.push(GreaterEqualFact { fact_id: self.global_ids.allocate_fact_id(), left: right.clone(), right: left.clone(), line_file: None }.into());
        }
        candidates.push(LessFact { fact_id: self.global_ids.allocate_fact_id(), left: left.clone(), right: right.clone(), line_file: None }.into());
        candidates.push(GreaterFact { fact_id: self.global_ids.allocate_fact_id(), left: right.clone(), right: left.clone(), line_file: None }.into());
        for candidate in candidates {
            let proof = self.verify_builtin_rule_premise(&candidate, state)?;
            if !proof.is_failed() { return Ok(Some(proof)); }
        }
        Ok(None)
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/negative_common_factor_order/tests.rs"]
mod negative_common_factor_order_tests;
