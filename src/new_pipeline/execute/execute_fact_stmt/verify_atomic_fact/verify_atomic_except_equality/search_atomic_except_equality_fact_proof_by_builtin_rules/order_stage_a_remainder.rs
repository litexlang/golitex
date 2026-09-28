//! Stage A remainder order builtins: negative-divisor flip, div↔product bridges,
//! numeric bound chase, integer successor/predecessor, positive even > 1,
//! finite-set max/min membership, union cardinality, surjection cardinality.
//!
//! One matcher ↔ one dedicated proof struct (see less_equal.rs / less.rs).

use crate::new_pipeline::ast::fact::{
    AtomicFact, EqualFact, Fact, InFact, LessEqualFact, LessFact, NormalAtomicFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{
    Add, ArithmeticOperator, Div, FiniteSetMax, FiniteSetMin, FiniteSetSize, FiniteSetStat,
    IntegerOperator, Literal, Mod, Mul, Number, Obj, SetOperator, Sub, Union,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less::{
    DivMonotoneStrictSameNegDivisorBuiltinRuleProof, LessFactSearchProofByBuiltinRule,
    NumericLowerBoundWeakenLtBuiltinRuleProof, NumericUpperBoundWeakenLtBuiltinRuleProof,
    PositiveEvenGtOneBuiltinRuleProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::{
    zero_obj, DivMonotoneWeakSameNegDivisorBuiltinRuleProof,
    FiniteSetMaxMemberLeBuiltinRuleProof, FiniteSetMinMemberLeBuiltinRuleProof,
    FiniteSetSizeSurjectionCodomainLeDomainBuiltinRuleProof,
    FiniteSetSizeUnionLeSumBuiltinRuleProof, IntegerAdjacencyLeBuiltinRuleProof,
    IntegerDiffAtLeastOneLeBuiltinRuleProof, IntegerPredecessorLeBuiltinRuleProof,
    IntegerSuccessorLeBuiltinRuleProof, LessEqualFactSearchProofByBuiltinRule,
    LessEqualFromPosDenomQuotientBoundBuiltinRuleProof,
    LessEqualFromPosDivProductBoundBuiltinRuleProof,
    NumericLowerBoundFromStrictPredecessorLeBuiltinRuleProof,
    NumericLowerBoundWeakenLeBuiltinRuleProof, NumericUpperBoundWeakenLeBuiltinRuleProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::order_div_mod_bridge_trans::{
    is_one_literal, make_less_equal_fact, make_less_fact, match_div_obj, match_finite_set_size,
    one_obj,
};
use crate::syntax::keywords::SURJECTIVE;

impl Runtime {
    // Stage A remainder search for `<=`.
    pub(super) fn search_order_stage_a_remainder_less_equal_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if let Some(p) = self.div_monotone_weak_same_neg_divisor_proof(fact, verify_state.clone())? {
            return Ok(Some(p));
        }
        if let Some(p) =
            self.less_equal_from_pos_div_product_bound_proof(fact, verify_state.clone())?
        {
            return Ok(Some(p));
        }
        if let Some(p) =
            self.less_equal_from_pos_denom_quotient_bound_proof(fact, verify_state.clone())?
        {
            return Ok(Some(p));
        }
        if let Some(p) = self.numeric_lower_bound_weaken_le_proof(fact)? {
            return Ok(Some(p));
        }
        if let Some(p) = self
            .numeric_lower_bound_from_strict_predecessor_le_proof(fact, verify_state.clone())?
        {
            return Ok(Some(p));
        }
        if let Some(p) = self.numeric_upper_bound_weaken_le_proof(fact)? {
            return Ok(Some(p));
        }
        if let Some(p) = self.integer_successor_le_proof(fact, verify_state.clone())? {
            return Ok(Some(p));
        }
        if let Some(p) = self.integer_adjacency_le_proof(fact, verify_state.clone())? {
            return Ok(Some(p));
        }
        if let Some(p) = self.integer_predecessor_le_proof(fact, verify_state.clone())? {
            return Ok(Some(p));
        }
        if let Some(p) = self.integer_diff_at_least_one_le_proof(fact, verify_state.clone())? {
            return Ok(Some(p));
        }
        if let Some(p) = self.finite_set_max_member_le_proof(fact, verify_state.clone())? {
            return Ok(Some(p));
        }
        if let Some(p) = self.finite_set_min_member_le_proof(fact, verify_state.clone())? {
            return Ok(Some(p));
        }
        if let Some(p) = self.finite_set_size_union_le_sum_proof(fact, verify_state.clone())? {
            return Ok(Some(p));
        }
        self.finite_set_size_surjection_codomain_le_domain_proof(fact, verify_state)
    }

    // Stage A remainder search for `<`.
    pub(super) fn search_order_stage_a_remainder_less_proof(
        &mut self,
        fact: &LessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        if let Some(p) =
            self.div_monotone_strict_same_neg_divisor_proof(fact, verify_state.clone())?
        {
            return Ok(Some(p));
        }
        if let Some(p) = self.numeric_lower_bound_weaken_lt_proof(fact)? {
            return Ok(Some(p));
        }
        if let Some(p) = self.numeric_upper_bound_weaken_lt_proof(fact)? {
            return Ok(Some(p));
        }
        self.positive_even_gt_one_proof(fact, verify_state)
    }

    // Negative common divisor reverses weak order.
    // Example: known `c < 0` and `b <= a` prove `a / c <= b / c`.
    fn div_monotone_weak_same_neg_divisor_proof(
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
        let divisor_neg_proof = self.verify_order_negative(left_den, verify_state.clone())?;
        if divisor_neg_proof.is_failed() {
            return Ok(None);
        }
        let numerators_order = make_less_equal_fact(right_num, left_num, self);
        let numerators_order_proof = self.verify_fact(&numerators_order, verify_state)?;
        if numerators_order_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::DivMonotoneWeakSameNegDivisor(
                DivMonotoneWeakSameNegDivisorBuiltinRuleProof {
                    divisor_neg_proof,
                    numerators_order_proof,
                },
            ),
        ))
    }

    // Negative common divisor reverses strict order.
    // Example: known `c < 0` and `b < a` prove `a / c < b / c`.
    fn div_monotone_strict_same_neg_divisor_proof(
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
        let divisor_neg_proof = self.verify_order_negative(left_den, verify_state.clone())?;
        if divisor_neg_proof.is_failed() {
            return Ok(None);
        }
        let numerators_order = make_less_fact(right_num, left_num, self);
        let numerators_order_proof = self.verify_fact(&numerators_order, verify_state)?;
        if numerators_order_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::DivMonotoneStrictSameNegDivisor(
                DivMonotoneStrictSameNegDivisorBuiltinRuleProof {
                    divisor_neg_proof,
                    numerators_order_proof,
                },
            ),
        ))
    }

    // Move a positive factor into a quotient on the right.
    // Example: known `0 < c` and `c * a <= b` (or `a * c <= b`) prove `a <= b / c`.
    fn less_equal_from_pos_div_product_bound_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some((numerator, denominator)) = match_div_obj(&fact.right) else {
            return Ok(None);
        };
        let divisor_pos_proof = self.verify_order_positive(denominator, verify_state.clone())?;
        if divisor_pos_proof.is_failed() {
            return Ok(None);
        }
        for product in [
            mul_obj(denominator, &fact.left),
            mul_obj(&fact.left, denominator),
        ] {
            let bound = make_less_equal_fact(&product, numerator, self);
            let product_bound_proof = self.verify_fact(&bound, verify_state.clone())?;
            if product_bound_proof.is_failed() {
                continue;
            }
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::LessEqualFromPosDivProductBound(
                    LessEqualFromPosDivProductBoundBuiltinRuleProof {
                        divisor_pos_proof,
                        product_bound_proof,
                    },
                ),
            ));
        }
        Ok(None)
    }

    // Move a positive denominator out of a left quotient.
    // Example: known `0 < c` and `a / c <= b` prove `a <= b * c`.
    fn less_equal_from_pos_denom_quotient_bound_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some((left_factor, right_factor)) = match_mul_obj(&fact.right) else {
            return Ok(None);
        };
        for (denominator, other) in [(left_factor, right_factor), (right_factor, left_factor)] {
            let divisor_pos_proof = self.verify_order_positive(denominator, verify_state.clone())?;
            if divisor_pos_proof.is_failed() {
                continue;
            }
            let quotient = div_obj(&fact.left, denominator);
            let bound = make_less_equal_fact(&quotient, other, self);
            let quotient_bound_proof = self.verify_fact(&bound, verify_state.clone())?;
            if quotient_bound_proof.is_failed() {
                continue;
            }
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::LessEqualFromPosDenomQuotientBound(
                    LessEqualFromPosDenomQuotientBoundBuiltinRuleProof {
                        divisor_pos_proof,
                        quotient_bound_proof,
                    },
                ),
            ));
        }
        Ok(None)
    }

    // Weaken a known numeric lower bound to a smaller literal weak goal.
    // Example: known `4 < x` or `4 <= x` proves `2 <= x`.
    fn numeric_lower_bound_weaken_le_proof(
        &self,
        fact: &LessEqualFact,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(target) = literal_integer_value(&fact.left) else {
            return Ok(None);
        };
        for (cite_fact_id, bound, right, _) in self.known_order_edges() {
            if right.ir() != fact.right.ir() {
                continue;
            }
            let Some(known) = literal_integer_value(&bound) else {
                continue;
            };
            if target <= known {
                return Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::NumericLowerBoundWeakenLe(
                        NumericLowerBoundWeakenLeBuiltinRuleProof { cite_fact_id },
                    ),
                ));
            }
        }
        Ok(None)
    }

    // Integer discreteness lifts a strict predecessor lower bound.
    // Example: known `4 < x` and `x $in Z` prove `5 <= x`.
    fn numeric_lower_bound_from_strict_predecessor_le_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(target) = literal_integer_value(&fact.left) else {
            return Ok(None);
        };
        for (cite_fact_id, bound, right, strict) in self.known_order_edges() {
            if !strict || right.ir() != fact.right.ir() {
                continue;
            }
            let Some(known) = literal_integer_value(&bound) else {
                continue;
            };
            if known.checked_add(1) != Some(target) {
                continue;
            }
            let in_z_proof = self.verify_in_integer(&fact.right, verify_state.clone())?;
            if in_z_proof.is_failed() {
                continue;
            }
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::NumericLowerBoundFromStrictPredecessorLe(
                    NumericLowerBoundFromStrictPredecessorLeBuiltinRuleProof {
                        cite_fact_id,
                        in_z_proof,
                    },
                ),
            ));
        }
        Ok(None)
    }

    // Weaken a known numeric upper bound to a larger literal weak goal.
    // Example: known `x < 4` or `x <= 4` proves `x <= 6`.
    fn numeric_upper_bound_weaken_le_proof(
        &self,
        fact: &LessEqualFact,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(target) = literal_integer_value(&fact.right) else {
            return Ok(None);
        };
        for (cite_fact_id, left, bound, _) in self.known_order_edges() {
            if left.ir() != fact.left.ir() {
                continue;
            }
            let Some(known) = literal_integer_value(&bound) else {
                continue;
            };
            if known <= target {
                return Ok(Some(
                    LessEqualFactSearchProofByBuiltinRule::NumericUpperBoundWeakenLe(
                        NumericUpperBoundWeakenLeBuiltinRuleProof { cite_fact_id },
                    ),
                ));
            }
        }
        Ok(None)
    }

    // Weaken a known numeric lower bound to a smaller literal strict goal.
    // Example: known `4 < x` proves `2 < x`; known `5 <= x` proves `2 < x`.
    fn numeric_lower_bound_weaken_lt_proof(
        &self,
        fact: &LessFact,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let Some(target) = literal_integer_value(&fact.left) else {
            return Ok(None);
        };
        for (cite_fact_id, bound, right, strict) in self.known_order_edges() {
            if right.ir() != fact.right.ir() {
                continue;
            }
            let Some(known) = literal_integer_value(&bound) else {
                continue;
            };
            let ok = if strict { target <= known } else { target < known };
            if ok {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::NumericLowerBoundWeakenLt(
                        NumericLowerBoundWeakenLtBuiltinRuleProof { cite_fact_id },
                    ),
                ));
            }
        }
        Ok(None)
    }

    // Weaken a known numeric upper bound to a larger literal strict goal.
    // Example: known `x < 4` proves `x < 6`; known `x <= 4` proves `x < 6`.
    fn numeric_upper_bound_weaken_lt_proof(
        &self,
        fact: &LessFact,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        let Some(target) = literal_integer_value(&fact.right) else {
            return Ok(None);
        };
        for (cite_fact_id, left, bound, strict) in self.known_order_edges() {
            if left.ir() != fact.left.ir() {
                continue;
            }
            let Some(known) = literal_integer_value(&bound) else {
                continue;
            };
            let ok = if strict { known <= target } else { known < target };
            if ok {
                return Ok(Some(
                    LessFactSearchProofByBuiltinRule::NumericUpperBoundWeakenLt(
                        NumericUpperBoundWeakenLtBuiltinRuleProof { cite_fact_id },
                    ),
                ));
            }
        }
        Ok(None)
    }

    // Integer successor: `a < b` ⇒ `a + 1 <= b`.
    // Example: known `m < n` for integers proves `m + 1 <= n`.
    fn integer_successor_le_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(base) = match_plus_one(&fact.left) else {
            return Ok(None);
        };
        let left_in_z_proof = self.verify_in_integer(base, verify_state.clone())?;
        if left_in_z_proof.is_failed() {
            return Ok(None);
        }
        let right_in_z_proof = self.verify_in_integer(&fact.right, verify_state.clone())?;
        if right_in_z_proof.is_failed() {
            return Ok(None);
        }
        let strict = make_less_fact(base, &fact.right, self);
        let strict_proof = self.verify_fact(&strict, verify_state)?;
        if strict_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::IntegerSuccessorLe(
                IntegerSuccessorLeBuiltinRuleProof {
                    left_in_z_proof,
                    right_in_z_proof,
                    strict_proof,
                },
            ),
        ))
    }

    // Integer adjacency: `a < b + 1` ⇒ `a <= b`.
    // Example: known `m < n + 1` for integers proves `m <= n`.
    fn integer_adjacency_le_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let left_in_z_proof = self.verify_in_integer(&fact.left, verify_state.clone())?;
        if left_in_z_proof.is_failed() {
            return Ok(None);
        }
        let right_in_z_proof = self.verify_in_integer(&fact.right, verify_state.clone())?;
        if right_in_z_proof.is_failed() {
            return Ok(None);
        }
        let successor = add_obj(&fact.right, &one_obj());
        let strict = make_less_fact(&fact.left, &successor, self);
        let strict_proof = self.verify_fact(&strict, verify_state)?;
        if strict_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::IntegerAdjacencyLe(
                IntegerAdjacencyLeBuiltinRuleProof {
                    left_in_z_proof,
                    right_in_z_proof,
                    strict_proof,
                },
            ),
        ))
    }

    // Integer predecessor: `a < b` ⇒ `a <= b - 1`.
    // Example: known `m < n` for integers proves `m <= n - 1`.
    fn integer_predecessor_le_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(base) = match_minus_one(&fact.right) else {
            return Ok(None);
        };
        let left_in_z_proof = self.verify_in_integer(&fact.left, verify_state.clone())?;
        if left_in_z_proof.is_failed() {
            return Ok(None);
        }
        let right_in_z_proof = self.verify_in_integer(base, verify_state.clone())?;
        if right_in_z_proof.is_failed() {
            return Ok(None);
        }
        let strict = make_less_fact(&fact.left, base, self);
        let strict_proof = self.verify_fact(&strict, verify_state)?;
        if strict_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::IntegerPredecessorLe(
                IntegerPredecessorLeBuiltinRuleProof {
                    left_in_z_proof,
                    right_in_z_proof,
                    strict_proof,
                },
            ),
        ))
    }

    // Integer difference: `a < b` ⇒ `1 <= b - a`.
    // Example: known `m < n` for integers proves `1 <= n - m`.
    fn integer_diff_at_least_one_le_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        if !is_one_literal(&fact.left) {
            return Ok(None);
        }
        let Some((diff_left, diff_right)) = match_sub_obj(&fact.right) else {
            return Ok(None);
        };
        let left_in_z_proof = self.verify_in_integer(diff_right, verify_state.clone())?;
        if left_in_z_proof.is_failed() {
            return Ok(None);
        }
        let right_in_z_proof = self.verify_in_integer(diff_left, verify_state.clone())?;
        if right_in_z_proof.is_failed() {
            return Ok(None);
        }
        let strict = make_less_fact(diff_right, diff_left, self);
        let strict_proof = self.verify_fact(&strict, verify_state)?;
        if strict_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::IntegerDiffAtLeastOneLe(
                IntegerDiffAtLeastOneLeBuiltinRuleProof {
                    left_in_z_proof,
                    right_in_z_proof,
                    strict_proof,
                },
            ),
        ))
    }

    // Positive even integer exceeds one.
    // Example: known `i $in N+` and `i % 2 = 0` prove `1 < i`.
    fn positive_even_gt_one_proof(
        &mut self,
        fact: &LessFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessFactSearchProofByBuiltinRule>> {
        if !is_one_literal(&fact.left) {
            return Ok(None);
        }
        let integer = &fact.right;
        let in_n_pos_proof = self.verify_in_positive_natural(integer, verify_state.clone())?;
        if in_n_pos_proof.is_failed() {
            return Ok(None);
        }
        let even_goal = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: mod_obj(integer, &two_obj()),
            right: zero_obj(),
            line_file: None,
        }));
        let even_proof = self.verify_fact(&even_goal, verify_state)?;
        if even_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessFactSearchProofByBuiltinRule::PositiveEvenGtOne(
                PositiveEvenGtOneBuiltinRuleProof {
                    in_n_pos_proof,
                    even_proof,
                },
            ),
        ))
    }

    // Members sit below the finite-set maximum.
    // Example: known `x $in S` proves `x <= finite_set_max(S)`.
    fn finite_set_max_member_le_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(set) = match_finite_set_max(&fact.right) else {
            return Ok(None);
        };
        let member_proof = self.verify_membership(&fact.left, set, verify_state)?;
        if member_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::FiniteSetMaxMemberLe(
                FiniteSetMaxMemberLeBuiltinRuleProof { member_proof },
            ),
        ))
    }

    // The finite-set minimum sits below members.
    // Example: known `x $in S` proves `finite_set_min(S) <= x`.
    fn finite_set_min_member_le_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(set) = match_finite_set_min(&fact.left) else {
            return Ok(None);
        };
        let member_proof = self.verify_membership(&fact.right, set, verify_state)?;
        if member_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::FiniteSetMinMemberLe(
                FiniteSetMinMemberLeBuiltinRuleProof { member_proof },
            ),
        ))
    }

    // Union cardinality is at most the sum of the input cardinalities.
    // Example: `finite_set_size(union(A, B)) <= finite_set_size(A) + finite_set_size(B)`.
    fn finite_set_size_union_le_sum_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(union_set) = match_finite_set_size(&fact.left) else {
            return Ok(None);
        };
        let Some((u_left, u_right)) = match_union_obj(union_set) else {
            return Ok(None);
        };
        let Some((sum_left, sum_right)) = match_add_obj(&fact.right) else {
            return Ok(None);
        };
        let Some(left_set) = match_finite_set_size(sum_left) else {
            return Ok(None);
        };
        let Some(right_set) = match_finite_set_size(sum_right) else {
            return Ok(None);
        };
        if u_left.ir() != left_set.ir() || u_right.ir() != right_set.ir() {
            return Ok(None);
        }
        let left_finite_proof = self.verify_is_finite_set(left_set, verify_state.clone())?;
        if left_finite_proof.is_failed() {
            return Ok(None);
        }
        let right_finite_proof = self.verify_is_finite_set(right_set, verify_state)?;
        if right_finite_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeUnionLeSum(
                FiniteSetSizeUnionLeSumBuiltinRuleProof {
                    left_finite_proof,
                    right_finite_proof,
                },
            ),
        ))
    }

    // Surjection from a finite source bounds codomain size by source size.
    // Example: known `$surjective(A, B, f)` and finite `A` prove
    // `finite_set_size(B) <= finite_set_size(A)`.
    fn finite_set_size_surjection_codomain_le_domain_proof(
        &mut self,
        fact: &LessEqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<LessEqualFactSearchProofByBuiltinRule>> {
        let Some(codomain_set) = match_finite_set_size(&fact.left) else {
            return Ok(None);
        };
        let Some(domain_set) = match_finite_set_size(&fact.right) else {
            return Ok(None);
        };
        for (cite_fact_id, domain, codomain) in self.known_surjection_triples() {
            if domain.ir() != domain_set.ir() || codomain.ir() != codomain_set.ir() {
                continue;
            }
            let domain_finite_proof =
                self.verify_is_finite_set(domain_set, verify_state.clone())?;
            if domain_finite_proof.is_failed() {
                continue;
            }
            return Ok(Some(
                LessEqualFactSearchProofByBuiltinRule::FiniteSetSizeSurjectionCodomainLeDomain(
                    FiniteSetSizeSurjectionCodomainLeDomainBuiltinRuleProof {
                        cite_surjection_fact_id: cite_fact_id,
                        domain_finite_proof,
                    },
                ),
            ));
        }
        Ok(None)
    }

    fn verify_membership(
        &mut self,
        element: &Obj,
        set: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let goal = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: element.clone(),
            set: set.clone(),
            line_file: None,
        }));
        self.verify_fact(&goal, verify_state)
    }

    fn known_surjection_triples(&self) -> Vec<(FactId, Obj, Obj)> {
        let key = (AtomicName::plain(SURJECTIVE.to_string()), true);
        let mut out = Vec::new();
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
                if let AtomicFact::NormalAtomicFact(NormalAtomicFact {
                    fact_id,
                    body,
                    ..
                }) = known
                {
                    if body.len() == 3 {
                        out.push((*fact_id, body[0].clone(), body[1].clone()));
                    }
                }
            }
        }
        out
    }
}

fn match_mul_obj(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_add_obj(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_sub_obj(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_union_obj(obj: &Obj) -> Option<(&Obj, &Obj)> {
    match obj {
        Obj::SetOperator(SetOperator::Union(Union { left, right })) => {
            Some((left.as_ref(), right.as_ref()))
        }
        _ => None,
    }
}

fn match_finite_set_max(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMax(FiniteSetMax { set })) => Some(set.as_ref()),
        _ => None,
    }
}

fn match_finite_set_min(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::FiniteSetStat(FiniteSetStat::FiniteSetMin(FiniteSetMin { set })) => Some(set.as_ref()),
        _ => None,
    }
}

fn match_plus_one(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right }))
            if is_one_literal(right.as_ref()) =>
        {
            Some(left.as_ref())
        }
        Obj::ArithmeticOperator(ArithmeticOperator::Add(Add { left, right }))
            if is_one_literal(left.as_ref()) =>
        {
            Some(right.as_ref())
        }
        _ => None,
    }
}

fn match_minus_one(obj: &Obj) -> Option<&Obj> {
    match obj {
        Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub { left, right }))
            if is_one_literal(right.as_ref()) =>
        {
            Some(left.as_ref())
        }
        _ => None,
    }
}

fn mul_obj(left: &Obj, right: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }))
}

fn add_obj(left: &Obj, right: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }))
}

fn div_obj(left: &Obj, right: &Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }))
}

fn mod_obj(left: &Obj, right: &Obj) -> Obj {
    Obj::IntegerOperator(IntegerOperator::Mod(Mod {
        left: Box::new(left.clone()),
        right: Box::new(right.clone()),
    }))
}

fn two_obj() -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: "2".to_string(),
    }))
}

fn literal_integer_value(obj: &Obj) -> Option<i128> {
    match obj {
        Obj::Literal(Literal::Number(Number { normalized_value })) => {
            normalized_value.parse::<i128>().ok()
        }
        _ => None,
    }
}
