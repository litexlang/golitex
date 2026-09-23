//! Order / absolute-value algebra builtins for `<=`.
//!
//! Each matcher is a dedicated LessEqual builtin rule (one rule ↔ one proof struct).
//! Subgoals are proved via `verify_fact` (known facts, closed numeric, earlier rules).

use crate::new_pipeline::ast::fact::{AtomicFact, Fact, LessEqualFact};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{
    Abs, Add, ArithmeticOperator, Mul, Obj, Sub,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{
    is_zero_obj, zero_obj, AbsLeFromSymmetricBoundsBuiltinRuleProof,
    AbsLeImpliesNegUpperBuiltinRuleProof, AbsLeImpliesUpperBuiltinRuleProof,
    AbsSelfLowerBuiltinRuleProof, AbsSelfUpperBuiltinRuleProof,
    AbsTriangleInequalityBuiltinRuleProof, AddLeftCongruenceBuiltinRuleProof,
    AddLeftNonnegativeBuiltinRuleProof, AddRightCongruenceBuiltinRuleProof,
    LessEqualFactSearchProofByBuiltinRule, MulLeftNonnegativeMonotoneBuiltinRuleProof,
    MulRightNonnegativeMonotoneBuiltinRuleProof, SubNonnegativeBuiltinRuleProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::parse::keywords::LESS_EQUAL;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

impl Runtime {
    // Try order / abs algebra routes after the dedicated add-right nonnegative rule.
    pub(super) fn search_order_abs_algebra_less_equal_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.add_left_nonnegative_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.add_right_congruence_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.add_left_congruence_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.sub_nonnegative_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.mul_left_nonnegative_monotone_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.mul_right_nonnegative_monotone_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        // Zero-premise abs shapes first (no recursive verify_fact).
        if abs_triangle_inequality_matches(fact) {
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::AbsTriangleInequality(
                    AbsTriangleInequalityBuiltinRuleProof {},
                ),
            ));
        }
        if abs_self_upper_matches(fact) {
            return Ok(Some(LessEqualFactSearchProofByBuiltinRule::AbsSelfUpper(
                AbsSelfUpperBuiltinRuleProof {},
            )));
        }
        if abs_self_lower_matches(fact) {
            return Ok(Some(LessEqualFactSearchProofByBuiltinRule::AbsSelfLower(
                AbsSelfLowerBuiltinRuleProof {},
            )));
        }
        if let Some(proof) = self.abs_le_from_symmetric_bounds_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.abs_le_implies_upper_proof(fact) {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.abs_le_implies_neg_upper_proof(fact) {
            return Ok(Some(proof));
        }
        Ok(None)
    }

    // `a <= b + a` from `0 <= b`.
    fn add_left_nonnegative_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) = &fact.right
        else {
            return Ok(None);
        };
        if right.as_ref().ir() != fact.left.ir() {
            return Ok(None);
        }
        let proof = self.verify_nonnegative(left.as_ref(), verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::AddLeftNonnegative(
                AddLeftNonnegativeBuiltinRuleProof {
                    nonnegative_addend_proof: proof,
                },
            ),
        ))
    }

    // `a + c <= b + c` from `a <= b`.
    fn add_right_congruence_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: left_l,
                right: left_r,
            })),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: right_l,
                right: right_r,
            })),
        ) = (&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if left_r.as_ref().ir() != right_r.as_ref().ir() {
            return Ok(None);
        }
        let premise = less_equal_fact(left_l.as_ref(), right_l.as_ref(), self);
        let premise_proof = self.verify_fact(&premise, verify_state)?;
        if premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::AddRightCongruence(
                AddRightCongruenceBuiltinRuleProof { premise_proof },
            ),
        ))
    }

    // `c + a <= c + b` from `a <= b`.
    fn add_left_congruence_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: left_l,
                right: left_r,
            })),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                left: right_l,
                right: right_r,
            })),
        ) = (&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if left_l.as_ref().ir() != right_l.as_ref().ir() {
            return Ok(None);
        }
        let premise = less_equal_fact(left_r.as_ref(), right_r.as_ref(), self);
        let premise_proof = self.verify_fact(&premise, verify_state)?;
        if premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::AddLeftCongruence(
                AddLeftCongruenceBuiltinRuleProof { premise_proof },
            ),
        ))
    }

    // `a - b <= a` from `0 <= b`.
    fn sub_nonnegative_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) = &fact.left
        else {
            return Ok(None);
        };
        if left.as_ref().ir() != fact.right.ir() {
            return Ok(None);
        }
        let proof = self.verify_nonnegative(right.as_ref(), verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(LessEqualFactSearchProofByBuiltinRule::SubNonnegative(
            SubNonnegativeBuiltinRuleProof {
                nonnegative_subtrahend_proof: proof,
            },
        )))
    }

    // `0 <= k` and `a <= b` ⇒ `k * a <= k * b`.
    fn mul_left_nonnegative_monotone_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                left: left_k,
                right: left_a,
            })),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                left: right_k,
                right: right_b,
            })),
        ) = (&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if left_k.as_ref().ir() != right_k.as_ref().ir() {
            return Ok(None);
        }
        let nonnegative_factor_proof =
            self.verify_nonnegative(left_k.as_ref(), verify_state.clone())?;
        if nonnegative_factor_proof.is_failed() {
            return Ok(None);
        }
        let order_premise = less_equal_fact(left_a.as_ref(), right_b.as_ref(), self);
        let order_premise_proof = self.verify_fact(&order_premise, verify_state)?;
        if order_premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::MulLeftNonnegativeMonotone(
                MulLeftNonnegativeMonotoneBuiltinRuleProof {
                    nonnegative_factor_proof,
                    order_premise_proof,
                },
            ),
        ))
    }

    // `0 <= k` and `a <= b` ⇒ `a * k <= b * k`.
    fn mul_right_nonnegative_monotone_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                left: left_a,
                right: left_k,
            })),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                left: right_b,
                right: right_k,
            })),
        ) = (&fact.left, &fact.right)
        else {
            return Ok(None);
        };
        if left_k.as_ref().ir() != right_k.as_ref().ir() {
            return Ok(None);
        }
        let nonnegative_factor_proof =
            self.verify_nonnegative(left_k.as_ref(), verify_state.clone())?;
        if nonnegative_factor_proof.is_failed() {
            return Ok(None);
        }
        let order_premise = less_equal_fact(left_a.as_ref(), right_b.as_ref(), self);
        let order_premise_proof = self.verify_fact(&order_premise, verify_state)?;
        if order_premise_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::MulRightNonnegativeMonotone(
                MulRightNonnegativeMonotoneBuiltinRuleProof {
                    nonnegative_factor_proof,
                    order_premise_proof,
                },
            ),
        ))
    }

    // `x <= a` and `-x <= a` ⇒ `abs(x) <= a`.
    fn abs_le_from_symmetric_bounds_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) = &fact.left else {
            return Ok(None);
        };
        let bound = &fact.right;
        let upper = less_equal_fact(arg.as_ref(), bound, self);
        let upper_proof = self.verify_fact(&upper, verify_state.clone())?;
        if upper_proof.is_failed() {
            return Ok(None);
        }
        let neg_x = negate_obj(arg.as_ref());
        let neg_upper = less_equal_fact(&neg_x, bound, self);
        let neg_upper_proof = self.verify_fact(&neg_upper, verify_state)?;
        if neg_upper_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::AbsLeFromSymmetricBounds(
                AbsLeFromSymmetricBoundsBuiltinRuleProof {
                    upper_proof,
                    neg_upper_proof,
                },
            ),
        ))
    }

    // Known `abs(x) <= a` ⇒ goal `x <= a`.
    fn abs_le_implies_upper_proof(
        &self,
        fact: &LessEqualFact,
    ) -> Option<LessEqualFactSearchProofByBuiltinRule> {
        let abs_x = abs_obj(&fact.left);
        let cite_fact_id = self.known_less_equal_fact_id(&abs_x, &fact.right)?;
        Some(LessEqualFactSearchProofByBuiltinRule::AbsLeImpliesUpper(
            AbsLeImpliesUpperBuiltinRuleProof { cite_fact_id },
        ))
    }

    // Known `abs(x) <= a` ⇒ goal `-x <= a`.
    fn abs_le_implies_neg_upper_proof(
        &self,
        fact: &LessEqualFact,
    ) -> Option<LessEqualFactSearchProofByBuiltinRule> {
        let x = match_negation(&fact.left)?;
        let abs_x = abs_obj(x);
        let cite_fact_id = self.known_less_equal_fact_id(&abs_x, &fact.right)?;
        Some(LessEqualFactSearchProofByBuiltinRule::AbsLeImpliesNegUpper(
            AbsLeImpliesNegUpperBuiltinRuleProof { cite_fact_id },
        ))
    }

    fn verify_nonnegative(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult>
    {
        let goal = less_equal_fact(&zero_obj(), obj, self);
        self.verify_fact(&goal, verify_state)
    }

    pub(crate) fn known_less_equal_fact_id(&self, left: &Obj, right: &Obj) -> Option<FactId> {
        let key = (AtomicName::Plain {
            name: LESS_EQUAL.into(),
        }, true);
        let left_ir = left.ir();
        let right_ir = right.ir();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&key)
            else {
                continue;
            };
            for known in knowns {
                if let AtomicFact::LessEqualFact(f) = known {
                    if f.left.ir() == left_ir && f.right.ir() == right_ir {
                        return Some(f.fact_id);
                    }
                }
            }
        }
        None
    }
}

fn less_equal_fact(left: &Obj, right: &Obj, runtime: &mut Runtime) -> Fact {
    Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: left.clone(),
        right: right.clone(),
        line_file: None,
    }))
}

fn negate_obj(obj: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
        left: Box::new(zero_obj()),
        right: Box::new(obj.clone()),
    }))
}

fn abs_obj(obj: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
        arg: Box::new(obj.clone()),
    }))
}

fn match_negation(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right }))
            if is_zero_obj(left.as_ref()) =>
        {
            Some(right.as_ref())
        }
        _ => None,
    }
}

fn abs_self_upper_matches(fact: &LessEqualFact) -> bool {
    matches!(
        &fact.right,
        Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg }))
            if arg.as_ref().ir() == fact.left.ir()
    )
}

fn abs_self_lower_matches(fact: &LessEqualFact) -> bool {
    let Some(abs_x) = (match &fact.left {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right }))
            if is_zero_obj(left.as_ref()) =>
        {
            match right.as_ref() {
                Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg })) => Some(arg.as_ref()),
                _ => None,
            }
        }
        _ => None,
    }) else {
        return false;
    };
    abs_x.ir() == fact.right.ir()
}

fn abs_triangle_inequality_matches(fact: &LessEqualFact) -> bool {
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: sum })) = &fact.left else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left: x, right: y })) = sum.as_ref()
    else {
        return false;
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: abs_x,
        right: abs_y,
    })) = &fact.right
    else {
        return false;
    };
    matches!(
        (abs_x.as_ref(), abs_y.as_ref()),
        (
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: ax })),
            Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: ay })),
        ) if ax.as_ref().ir() == x.as_ref().ir() && ay.as_ref().ir() == y.as_ref().ir()
    )
}
