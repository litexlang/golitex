//! Division / mod / subtraction-bridge / transitivity / finite-set-size order builtins.
//!
//! One matcher ↔ one dedicated proof struct (see less_equal.rs / less.rs / greater_equal.rs).

use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, InFact, IsFiniteSetFact, IsNonemptySetFact, LessEqualFact, LessFact,
    SubsetFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{
    ArithmeticOperator, Div, FiniteSetSize, FiniteSetStat, IntegerOperator, Literal, Mod, Number,
    Obj, StandardSet, Sub,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::{
    FiniteSetSizeAtLeastOneBuiltinRuleProof, FiniteSetSizeNonnegativeBuiltinRuleProof,
    GreaterEqualFactSearchProofByBuiltinRule,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::{
    DivByGtOneLessSelfBuiltinRuleProof, DivMonotoneStrictSamePosDivisorBuiltinRuleProof,
    LessFactSearchProofByBuiltinRule, LessFromPosDifferenceBuiltinRuleProof,
    LessTransitivityBuiltinRuleProof, ModRemainderStrictUpperBoundBuiltinRuleProof,
    PosDifferenceFromLessBuiltinRuleProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{
    is_zero_obj, zero_obj, DivMonotoneWeakSamePosDivisorBuiltinRuleProof,
    FiniteSetSizeAtLeastOneLeBuiltinRuleProof, FiniteSetSizeNonnegativeLeBuiltinRuleProof,
    FiniteSetSizeSubsetLeBuiltinRuleProof, LessEqualFactSearchProofByBuiltinRule,
    LessEqualFromNonnegDifferenceBuiltinRuleProof, LessEqualTransitivityBuiltinRuleProof,
    ModRemainderNonnegativeBuiltinRuleProof, NonnegDifferenceFromLessEqualBuiltinRuleProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::parse::keywords::{LESS, LESS_EQUAL};
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};

impl Runtime {
    // Shape / premise search for mod, div, sub-bridge, transitivity, cardinality (`<=`).
    // Example goals: `0 <= a % b`, `0 <= b - a`, `a <= c`, `a / c <= b / c`,
    // `0 <= finite_set_size(S)`.
    pub(super) fn search_order_div_mod_bridge_trans_less_equal_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.less_equal_transitivity_proof(fact)? {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.less_equal_from_nonneg_difference_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.nonneg_difference_from_less_equal_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.mod_remainder_nonnegative_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.div_monotone_weak_same_pos_divisor_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.finite_set_size_nonnegative_le_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.finite_set_size_at_least_one_le_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        self.finite_set_size_subset_le_proof(fact, verify_state)
    }

    // Shape / premise search for mod, div, sub-bridge, transitivity (`<`).
    // Example goals: `a % b < b`, `0 < b - a`, `a < c`, `a / c < b / c`, `a / b < a`.
    pub(super) fn search_order_div_mod_bridge_trans_less_proof(
        &mut self,
        fact: &LessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        if let Some(proof) = self.less_transitivity_proof(fact)? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.less_from_pos_difference_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.pos_difference_from_less_proof(fact, verify_state.clone())? {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.mod_remainder_strict_upper_bound_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.div_monotone_strict_same_pos_divisor_proof(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        self.div_by_gt_one_less_self_proof(fact, verify_state)
    }

    // Weak cardinality bounds on `>=`.
    // Example goals: `finite_set_size(S) >= 0`, `finite_set_size(S) >= 1`.
    pub(super) fn search_order_finite_set_size_greater_equal_proof(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterEqualFactSearchProofByBuiltinRule>> {
        if is_zero_obj(right) {
            if let Some(proof) =
                self.finite_set_size_nonnegative_ge_proof(left, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
        }
        if is_one_literal(right) {
            if let Some(proof) = self.finite_set_size_at_least_one_ge_proof(left, verify_state)? {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    // `a <= b` / `a < b` chained through a shared middle term prove `a <= c`.
    // Example: known `x <= y` and `y <= z` prove `x <= z`.
    fn less_equal_transitivity_proof(
        &self,
        fact: &LessEqualFact,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let left_ir = fact.left.ir();
        let right_ir = fact.right.ir();
        let edges = self.known_order_edges();
        for (left_cite, left_left, mid, _) in edges.iter() {
            if left_left.ir() != left_ir {
                continue;
            }
            let mid_ir = mid.ir();
            for (right_cite, mid2, right_right, _) in edges.iter() {
                if mid2.ir() == mid_ir && right_right.ir() == right_ir {
                    return Ok(Some(
                        LessEqualFactSearchProofByBuiltinRule::LessEqualTransitivity(
                            LessEqualTransitivityBuiltinRuleProof {
                                left_to_mid_cite_fact_id: *left_cite,
                                mid_to_right_cite_fact_id: *right_cite,
                            },
                        ),
                    ));
                }
            }
        }
        Ok(None)
    }

    // Chained order through a middle term with at least one strict premise proves `a < c`.
    // Example: known `x <= y` and `y < z` prove `x < z`.
    fn less_transitivity_proof(
        &self,
        fact: &LessFact,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let left_ir = fact.left.ir();
        let right_ir = fact.right.ir();
        let edges = self.known_order_edges();
        for (left_cite, left_left, mid, left_strict) in edges.iter() {
            if left_left.ir() != left_ir {
                continue;
            }
            let mid_ir = mid.ir();
            for (right_cite, mid2, right_right, right_strict) in edges.iter() {
                if mid2.ir() == mid_ir
                    && right_right.ir() == right_ir
                    && (*left_strict || *right_strict)
                {
                    return Ok(Some(LessFactSearchProofByBuiltinRule::LessTransitivity(
                        LessTransitivityBuiltinRuleProof {
                            left_to_mid_cite_fact_id: *left_cite,
                            mid_to_right_cite_fact_id: *right_cite,
                            left_to_mid_strict: *left_strict,
                            mid_to_right_strict: *right_strict,
                        },
                    )));
                }
            }
        }
        Ok(None)
    }

    // `0 <= b - a` implies `a <= b` (premise must already be known).
    // Example: known `0 <= y - x` proves `x <= y`.
    fn less_equal_from_nonneg_difference_proof(
        &mut self,
        fact: &LessEqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let difference = sub_obj(&fact.right, &fact.left);
        let Some(cite_fact_id) = self.known_less_equal_fact_id(&zero_obj(), &difference) else {
            return Ok(None);
        };
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::LessEqualFromNonnegDifference(
                LessEqualFromNonnegDifferenceBuiltinRuleProof { cite_fact_id },
            ),
        ))
    }

    // `a <= b` implies `0 <= b - a` (order premise must already be known).
    // Example: known `x <= y` proves `0 <= y - x`.
    fn nonneg_difference_from_less_equal_proof(
        &mut self,
        fact: &LessEqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if !is_zero_obj(&fact.left) {
            return Ok(None);
        }
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) = &fact.right
        else {
            return Ok(None);
        };
        let Some(cite_fact_id) = self.known_less_equal_fact_id(right.as_ref(), left.as_ref()) else {
            return Ok(None);
        };
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::NonnegDifferenceFromLessEqual(
                NonnegDifferenceFromLessEqualBuiltinRuleProof { cite_fact_id },
            ),
        ))
    }

    // `0 < b - a` implies `a < b` (premise must already be known).
    // Example: known `0 < y - x` proves `x < y`.
    fn less_from_pos_difference_proof(
        &mut self,
        fact: &LessFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let difference = sub_obj(&fact.right, &fact.left);
        let Some(cite_fact_id) = self.known_less_fact_id(&zero_obj(), &difference) else {
            return Ok(None);
        };
        Ok(Some(LessFactSearchProofByBuiltinRule::LessFromPosDifference(
            LessFromPosDifferenceBuiltinRuleProof { cite_fact_id },
        )))
    }

    // `a < b` implies `0 < b - a` (order premise must already be known).
    // Example: known `x < y` proves `0 < y - x`.
    fn pos_difference_from_less_proof(
        &mut self,
        fact: &LessFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        if !is_zero_obj(&fact.left) {
            return Ok(None);
        }
        let Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) = &fact.right
        else {
            return Ok(None);
        };
        let Some(cite_fact_id) = self.known_less_fact_id(right.as_ref(), left.as_ref()) else {
            return Ok(None);
        };
        Ok(Some(LessFactSearchProofByBuiltinRule::PosDifferenceFromLess(
            PosDifferenceFromLessBuiltinRuleProof { cite_fact_id },
        )))
    }

    // Euclidean remainder is nonnegative: `a $in Z`, `b $in N+` ⇒ `0 <= a % b`.
    // Example: after `have a Z` and `have b N+`, prove `0 <= a % b`.
    fn mod_remainder_nonnegative_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if !is_zero_obj(&fact.left) {
            return Ok(None);
        }
        let Some((dividend, modulus)) = match_mod_obj(&fact.right) else {
            return Ok(None);
        };
        let dividend_in_z_proof = self.verify_in_integer(dividend, verify_state.clone())?;
        if dividend_in_z_proof.is_failed() {
            return Ok(None);
        }
        let modulus_in_n_pos_proof = self.verify_in_positive_natural(modulus, verify_state)?;
        if modulus_in_n_pos_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::ModRemainderNonnegative(
                ModRemainderNonnegativeBuiltinRuleProof {
                    dividend_in_z_proof,
                    modulus_in_n_pos_proof,
                },
            ),
        ))
    }

    // Euclidean remainder is strictly below the modulus.
    // Example: after `have a Z` and `have b N+`, prove `a % b < b`.
    fn mod_remainder_strict_upper_bound_proof(
        &mut self,
        fact: &LessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let Some((dividend, modulus)) = match_mod_obj(&fact.left) else {
            return Ok(None);
        };
        if modulus.ir() != fact.right.ir() {
            return Ok(None);
        }
        let dividend_in_z_proof = self.verify_in_integer(dividend, verify_state.clone())?;
        if dividend_in_z_proof.is_failed() {
            return Ok(None);
        }
        let modulus_in_n_pos_proof = self.verify_in_positive_natural(modulus, verify_state)?;
        if modulus_in_n_pos_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::ModRemainderStrictUpperBound(
                ModRemainderStrictUpperBoundBuiltinRuleProof {
                    dividend_in_z_proof,
                    modulus_in_n_pos_proof,
                },
            ),
        ))
    }

    // Positive common divisor preserves weak order.
    // Example: known `0 < c` and `a <= b` prove `a / c <= b / c`.
    fn div_monotone_weak_same_pos_divisor_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some((left_num, left_den)) = match_div_obj(&fact.left) else {
            return Ok(None);
        };
        let Some((right_num, right_den)) = match_div_obj(&fact.right) else {
            return Ok(None);
        };
        if left_den.ir() != right_den.ir() {
            return Ok(None);
        }
        let divisor_pos_proof = self.verify_order_positive(left_den, verify_state.clone())?;
        if divisor_pos_proof.is_failed() {
            return Ok(None);
        }
        let numerators_order = make_less_equal_fact(left_num, right_num, self);
        let numerators_order_proof = self.verify_fact(&numerators_order, verify_state)?;
        if numerators_order_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::DivMonotoneWeakSamePosDivisor(
                DivMonotoneWeakSamePosDivisorBuiltinRuleProof {
                    divisor_pos_proof,
                    numerators_order_proof,
                },
            ),
        ))
    }

    // Positive common divisor preserves strict order.
    // Example: known `0 < c` and `a < b` prove `a / c < b / c`.
    fn div_monotone_strict_same_pos_divisor_proof(
        &mut self,
        fact: &LessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let Some((left_num, left_den)) = match_div_obj(&fact.left) else {
            return Ok(None);
        };
        let Some((right_num, right_den)) = match_div_obj(&fact.right) else {
            return Ok(None);
        };
        if left_den.ir() != right_den.ir() {
            return Ok(None);
        }
        let divisor_pos_proof = self.verify_order_positive(left_den, verify_state.clone())?;
        if divisor_pos_proof.is_failed() {
            return Ok(None);
        }
        let numerators_order = make_less_fact(left_num, right_num, self);
        let numerators_order_proof = self.verify_fact(&numerators_order, verify_state)?;
        if numerators_order_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::DivMonotoneStrictSamePosDivisor(
                DivMonotoneStrictSamePosDivisorBuiltinRuleProof {
                    divisor_pos_proof,
                    numerators_order_proof,
                },
            ),
        ))
    }

    // Dividing a positive quantity by a factor > 1 shrinks it.
    // Example: known `0 < a` and `1 < b` prove `a / b < a`.
    fn div_by_gt_one_less_self_proof(
        &mut self,
        fact: &LessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let Some((numerator, denominator)) = match_div_obj(&fact.left) else {
            return Ok(None);
        };
        if numerator.ir() != fact.right.ir() {
            return Ok(None);
        }
        let numerator_pos_proof = self.verify_order_positive(numerator, verify_state.clone())?;
        if numerator_pos_proof.is_failed() {
            return Ok(None);
        }
        let denominator_gt_one_proof = self.verify_order_gt_one(denominator, verify_state)?;
        if denominator_gt_one_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(LessFactSearchProofByBuiltinRule::DivByGtOneLessSelf(
            DivByGtOneLessSelfBuiltinRuleProof {
                numerator_pos_proof,
                denominator_gt_one_proof,
            },
        )))
    }

    // Cardinality of a finite set is nonnegative.
    // Example: `$is_finite_set(S)` proves `0 <= finite_set_size(S)`.
    fn finite_set_size_nonnegative_le_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if !is_zero_obj(&fact.left) {
            return Ok(None);
        }
        let Some(set) = match_finite_set_size(&fact.right) else {
            return Ok(None);
        };
        let finite_proof = self.verify_is_finite_set(set, verify_state)?;
        if finite_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeNonnegativeLe(
                FiniteSetSizeNonnegativeLeBuiltinRuleProof { finite_proof },
            ),
        ))
    }

    fn finite_set_size_nonnegative_ge_proof(
        &mut self,
        left: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterEqualFactSearchProofByBuiltinRule>> {
        let Some(set) = match_finite_set_size(left) else {
            return Ok(None);
        };
        let finite_proof = self.verify_is_finite_set(set, verify_state)?;
        if finite_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            GreaterEqualFactSearchProofByBuiltinRule::FiniteSetSizeNonnegative(
                FiniteSetSizeNonnegativeBuiltinRuleProof { finite_proof },
            ),
        ))
    }

    // Nonempty finite set has cardinality at least one.
    // Example: `$is_finite_set(S)` and `$is_nonempty_set(S)` prove `1 <= finite_set_size(S)`.
    fn finite_set_size_at_least_one_le_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if !is_one_literal(&fact.left) {
            return Ok(None);
        }
        let Some(set) = match_finite_set_size(&fact.right) else {
            return Ok(None);
        };
        let finite_proof = self.verify_is_finite_set(set, verify_state.clone())?;
        if finite_proof.is_failed() {
            return Ok(None);
        }
        let nonempty_proof = self.verify_is_nonempty_set(set, verify_state)?;
        if nonempty_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeAtLeastOneLe(
                FiniteSetSizeAtLeastOneLeBuiltinRuleProof {
                    finite_proof,
                    nonempty_proof,
                },
            ),
        ))
    }

    fn finite_set_size_at_least_one_ge_proof(
        &mut self,
        left: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<GreaterEqualFactSearchProofByBuiltinRule>> {
        let Some(set) = match_finite_set_size(left) else {
            return Ok(None);
        };
        let finite_proof = self.verify_is_finite_set(set, verify_state.clone())?;
        if finite_proof.is_failed() {
            return Ok(None);
        }
        let nonempty_proof = self.verify_is_nonempty_set(set, verify_state)?;
        if nonempty_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            GreaterEqualFactSearchProofByBuiltinRule::FiniteSetSizeAtLeastOne(
                FiniteSetSizeAtLeastOneBuiltinRuleProof {
                    finite_proof,
                    nonempty_proof,
                },
            ),
        ))
    }

    // Subset of finite sets cannot raise cardinality.
    // Example: `A $subset B` with both finite proves
    // `finite_set_size(A) <= finite_set_size(B)`.
    fn finite_set_size_subset_le_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(left_set) = match_finite_set_size(&fact.left) else {
            return Ok(None);
        };
        let Some(right_set) = match_finite_set_size(&fact.right) else {
            return Ok(None);
        };
        let left_finite_proof = self.verify_is_finite_set(left_set, verify_state.clone())?;
        if left_finite_proof.is_failed() {
            return Ok(None);
        }
        let right_finite_proof = self.verify_is_finite_set(right_set, verify_state.clone())?;
        if right_finite_proof.is_failed() {
            return Ok(None);
        }
        let subset_proof = self.verify_subset(left_set, right_set, verify_state)?;
        if subset_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeSubsetLe(
                FiniteSetSizeSubsetLeBuiltinRuleProof {
                    left_finite_proof,
                    right_finite_proof,
                    subset_proof,
                },
            ),
        ))
    }

    pub(crate) fn verify_in_integer(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: obj.clone(),
            set: Obj::StandardSet(StandardSet::Z),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }

    pub(crate) fn verify_in_natural(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: obj.clone(),
            set: Obj::StandardSet(StandardSet::N),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }

    pub(super) fn verify_is_finite_set(
        &mut self,
        set: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: set.clone(),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }

    pub(super) fn verify_is_nonempty_set(
        &mut self,
        set: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: set.clone(),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }

    pub(super) fn verify_subset(
        &mut self,
        left: &Obj,
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::SubsetFact(SubsetFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }

    pub(super) fn known_order_edges(&self) -> Vec<(FactId, Obj, Obj, bool)> {
        let mut edges = Vec::new();
        let less_key = (AtomicName::Plain { name: LESS.into() }, true);
        let less_equal_key = (AtomicName::Plain { name: LESS_EQUAL.into() }, true);
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&less_key)
            {
                for known in knowns {
                    if let AtomicFact::LessFact(f) = known {
                        edges.push((f.fact_id, f.left.clone(), f.right.clone(), true));
                    }
                }
            }
            if let Some(knowns) = env
                .facts
                .known_atomic_except_equality_facts
                .by_prop
                .get(&less_equal_key)
            {
                for known in knowns {
                    if let AtomicFact::LessEqualFact(f) = known {
                        edges.push((f.fact_id, f.left.clone(), f.right.clone(), false));
                    }
                }
            }
        }
        edges
    }
}

pub(super) fn match_mod_obj(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::IntegerOperator(IntegerOperator::Mod(Mod { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

pub(super) fn match_div_obj(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Div(Div { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

pub(super) fn match_finite_set_size(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize { set })) => {
            Some(set.as_ref())
        }
        _ => None,
    }
}

pub(super) fn sub_obj(left: &Obj, right: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }))
}

pub(super) fn make_less_equal_fact(left: &Obj, right: &Obj, runtime: &mut Runtime) -> Fact {
    Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: left.clone(),
        right: right.clone(),
        line_file: None,
    }))
}

pub(super) fn make_less_fact(left: &Obj, right: &Obj, runtime: &mut Runtime) -> Fact {
    Fact::AtomicFact(AtomicFact::LessFact(LessFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: left.clone(),
        right: right.clone(),
        line_file: None,
    }))
}

pub(super) fn one_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "1".to_string(),
    }))
}

pub(super) fn is_one_literal(obj: &Obj) -> bool {
    matches!(
        obj,
        Obj::Literal(Literal::Number(Number {
            normalized_value,
        })) if normalized_value == "1"
    )
}
