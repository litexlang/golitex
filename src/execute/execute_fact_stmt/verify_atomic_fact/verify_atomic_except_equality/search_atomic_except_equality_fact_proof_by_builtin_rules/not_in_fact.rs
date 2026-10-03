use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, InFact, LessEqualFact, LessFact, NotEqualFact, NotInFact,
};
use crate::ast::obj::{
    IntervalObj, Obj, OneSideInfinityIntervalObj, SetFormer, SetOperator, StandardSet,
};
use crate::rational_expression::closed_scalar_membership::normalized_decimal_inhabits_standard_set;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::rational_expression::evaluate_obj_to_normalized_decimal_number;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not x $in S` (zero-premise or subgoal routes).
pub enum NotInFactSearchProofByBuiltinRule {
    // Closed numeric non-membership by decimal evaluation.
    // Mathematical property: a closed expression that evaluates to a normalized
    // decimal outside the target standard set is not a member.
    // Examples: `not (-1) $in N`, `not 0 $in N+`, `not 1.5 $in Z`.
    ClosedNumericNonMembership(ClosedNumericNonMembershipBuiltinRuleProof),
    // Finite list-set non-membership by inequality to every listed element.
    // Mathematical property: if `x != a_i` for every `a_i` in `{a_1, …, a_n}`,
    // then `not x $in {a_1, …, a_n}`.
    // Example: `not 4 $in {1, 2, 3}`.
    ListSetExhaustiveDisequality(ListSetExhaustiveDisequalityBuiltinRuleProof),
    // Intersection non-membership from the left factor.
    // Mathematical property: `not x $in A` ⇒ `not x $in intersect(A, B)`.
    // Example: prove `not 1 $in intersect({2}, {1, 2})` from `not 1 $in {2}`.
    NonMembershipOfIntersectFromLeft(NonMembershipOfIntersectFromLeftBuiltinRuleProof),
    // Intersection non-membership from the right factor.
    // Mathematical property: `not x $in B` ⇒ `not x $in intersect(A, B)`.
    // Example: prove `not 1 $in intersect({1, 2}, {2})` from `not 1 $in {2}`.
    NonMembershipOfIntersectFromRight(NonMembershipOfIntersectFromRightBuiltinRuleProof),
    // Union non-membership from both sides.
    // Mathematical property: `not x $in A` and `not x $in B` ⇒
    // `not x $in union(A, B)`.
    // Example: `not 0 $in {1}` and `not 0 $in {2}` prove `not 0 $in union({1}, {2})`.
    NonMembershipOfUnion(NonMembershipOfUnionBuiltinRuleProof),
    // Set-minus non-membership from the subtracted set.
    // Mathematical property: `x $in B` ⇒ `not x $in set_minus(A, B)`.
    // Example: trust `x $in B` proves `not x $in set_minus(A, B)`.
    NonMembershipOfSetMinusFromRight(NonMembershipOfSetMinusFromRightBuiltinRuleProof),
    // Set-minus non-membership from the left set.
    // Mathematical property: `not x $in A` ⇒ `not x $in set_minus(A, B)`.
    // Example: trust `not x $in A` proves `not x $in set_minus(A, B)`.
    NonMembershipOfSetMinusFromLeft(NonMembershipOfSetMinusFromLeftBuiltinRuleProof),
    // Open endpoint of a bounded interval is not a member.
    // Mathematical property: if the left (resp. right) end is open and `x = a`
    // (resp. `x = b`), then `not x $in '(a,b)` / `'[a,b)` / etc.
    // Example: `not 0 $in '(0, 2)`.
    NonMembershipOfIntervalAtOpenEndpoint(NonMembershipOfIntervalAtOpenEndpointBuiltinRuleProof),
    // Outside a bounded interval.
    // Mathematical property: `x < a` or `b < x` (with closed ends using `<=` denial via strict).
    // Example: `not 2 $in '[0, 1]`.
    NonMembershipOfIntervalOutside(NonMembershipOfIntervalOutsideBuiltinRuleProof),
}

pub struct ClosedNumericNonMembershipBuiltinRuleProof {
    pub normal: String,
}

pub struct ListSetExhaustiveDisequalityBuiltinRuleProof {
    pub disequality_proofs: Vec<VerifyFactResult>,
}

pub struct NonMembershipOfIntersectFromLeftBuiltinRuleProof {
    pub left_non_membership_proof: VerifyFactResult,
}

pub struct NonMembershipOfIntersectFromRightBuiltinRuleProof {
    pub right_non_membership_proof: VerifyFactResult,
}

pub struct NonMembershipOfUnionBuiltinRuleProof {
    pub left_non_membership_proof: VerifyFactResult,
    pub right_non_membership_proof: VerifyFactResult,
}

pub struct NonMembershipOfSetMinusFromRightBuiltinRuleProof {
    pub right_membership_proof: VerifyFactResult,
}

pub struct NonMembershipOfSetMinusFromLeftBuiltinRuleProof {
    pub left_non_membership_proof: VerifyFactResult,
}

pub struct NonMembershipOfIntervalAtOpenEndpointBuiltinRuleProof {
    pub endpoint_equal_proof: VerifyFactResult,
}

pub struct NonMembershipOfIntervalOutsideBuiltinRuleProof {
    pub outside_order_proof: VerifyFactResult,
}

impl Runtime {
    // Builtin NotIn: closed numeric, list-set exhaustion, then intersect/union/set_minus algebra.
    pub fn search_not_in_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        match &fact.set {
            Obj::StandardSet(_) => Ok(closed_numeric_non_membership_proof(fact)),
            Obj::SetFormer(SetFormer::ListSet(_)) => {
                self.list_set_exhaustive_disequality_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::Intersect(_)) => {
                self.intersect_non_membership_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::Union(_)) => {
                self.union_non_membership_proof(fact, verify_state)
            }
            Obj::SetOperator(SetOperator::SetMinus(_)) => {
                self.set_minus_non_membership_proof(fact, verify_state)
            }
            Obj::SetFormer(SetFormer::IntervalObj(_)) => {
                self.interval_non_membership_proof(fact, verify_state)
            }
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(_)) => {
                self.one_side_interval_non_membership_proof(fact, verify_state)
            }
            _ => Ok(None),
        }
    }

    fn list_set_exhaustive_disequality_proof(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        let Obj::SetFormer(SetFormer::ListSet(list_set)) = &fact.set else {
            return Ok(None);
        };
        let mut disequality_proofs = Vec::with_capacity(list_set.list.len());
        for listed in &list_set.list {
            let disequality = Fact::AtomicFact(AtomicFact::NotEqualFact(NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.element.clone(),
                right: listed.as_ref().clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&disequality, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            disequality_proofs.push(proof);
        }
        Ok(Some(
            NotInFactSearchProofByBuiltinRule::ListSetExhaustiveDisequality(
                ListSetExhaustiveDisequalityBuiltinRuleProof {
                    disequality_proofs,
                },
            ),
        ))
    }

    fn intersect_non_membership_proof(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::Intersect(intersect)) = &fact.set else {
            return Ok(None);
        };
        let left_goal = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: intersect.left.as_ref().clone(),
            line_file: None,
        }));
        let left_proof = self.verify_builtin_rule_premise(&left_goal, verify_state.clone())?;
        if !left_proof.is_failed() {
            return Ok(Some(
                NotInFactSearchProofByBuiltinRule::NonMembershipOfIntersectFromLeft(
                    NonMembershipOfIntersectFromLeftBuiltinRuleProof {
                        left_non_membership_proof: left_proof,
                    },
                ),
            ));
        }
        let right_goal = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: intersect.right.as_ref().clone(),
            line_file: None,
        }));
        let right_proof = self.verify_builtin_rule_premise(&right_goal, verify_state)?;
        if right_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NotInFactSearchProofByBuiltinRule::NonMembershipOfIntersectFromRight(
                NonMembershipOfIntersectFromRightBuiltinRuleProof {
                    right_non_membership_proof: right_proof,
                },
            ),
        ))
    }

    fn union_non_membership_proof(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::Union(union)) = &fact.set else {
            return Ok(None);
        };
        let left_goal = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: union.left.as_ref().clone(),
            line_file: None,
        }));
        let left_proof = self.verify_builtin_rule_premise(&left_goal, verify_state.clone())?;
        if left_proof.is_failed() {
            return Ok(None);
        }
        let right_goal = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: union.right.as_ref().clone(),
            line_file: None,
        }));
        let right_proof = self.verify_builtin_rule_premise(&right_goal, verify_state)?;
        if right_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(NotInFactSearchProofByBuiltinRule::NonMembershipOfUnion(
            NonMembershipOfUnionBuiltinRuleProof {
                left_non_membership_proof: left_proof,
                right_non_membership_proof: right_proof,
            },
        )))
    }

    fn set_minus_non_membership_proof(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        let Obj::SetOperator(SetOperator::SetMinus(set_minus)) = &fact.set else {
            return Ok(None);
        };
        // x $in B ⇒ not x $in set_minus(A, B)
        let right_in = Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: set_minus.right.as_ref().clone(),
            line_file: None,
        }));
        let right_proof = self.verify_builtin_rule_premise(&right_in, verify_state.clone())?;
        if !right_proof.is_failed() {
            return Ok(Some(
                NotInFactSearchProofByBuiltinRule::NonMembershipOfSetMinusFromRight(
                    NonMembershipOfSetMinusFromRightBuiltinRuleProof {
                        right_membership_proof: right_proof,
                    },
                ),
            ));
        }
        // not x $in A ⇒ not x $in set_minus(A, B)
        let left_notin = Fact::AtomicFact(AtomicFact::NotInFact(NotInFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: fact.element.clone(),
            set: set_minus.left.as_ref().clone(),
            line_file: None,
        }));
        let left_proof = self.verify_builtin_rule_premise(&left_notin, verify_state)?;
        if left_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NotInFactSearchProofByBuiltinRule::NonMembershipOfSetMinusFromLeft(
                NonMembershipOfSetMinusFromLeftBuiltinRuleProof {
                    left_non_membership_proof: left_proof,
                },
            ),
        ))
    }

    fn interval_non_membership_proof(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        let Obj::SetFormer(SetFormer::IntervalObj(interval)) = &fact.set else {
            return Ok(None);
        };
        let (lower_closed, upper_closed, start, end) = match interval {
            IntervalObj::LeftOpenRightOpen(s) => (false, false, s.start.as_ref(), s.end.as_ref()),
            IntervalObj::LeftOpenRightClosed(s) => (false, true, s.start.as_ref(), s.end.as_ref()),
            IntervalObj::LeftClosedRightOpen(s) => (true, false, s.start.as_ref(), s.end.as_ref()),
            IntervalObj::LeftClosedRightClosed(s) => (true, true, s.start.as_ref(), s.end.as_ref()),
        };

        if !lower_closed {
            let eq = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.element.clone(),
                right: start.clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&eq, verify_state.clone())?;
            if !proof.is_failed() {
                return Ok(Some(
                    NotInFactSearchProofByBuiltinRule::NonMembershipOfIntervalAtOpenEndpoint(
                        NonMembershipOfIntervalAtOpenEndpointBuiltinRuleProof {
                            endpoint_equal_proof: proof,
                        },
                    ),
                ));
            }
        }
        if !upper_closed {
            let eq = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.element.clone(),
                right: end.clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&eq, verify_state.clone())?;
            if !proof.is_failed() {
                return Ok(Some(
                    NotInFactSearchProofByBuiltinRule::NonMembershipOfIntervalAtOpenEndpoint(
                        NonMembershipOfIntervalAtOpenEndpointBuiltinRuleProof {
                            endpoint_equal_proof: proof,
                        },
                    ),
                ));
            }
        }

        // x < start
        let left_out = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: fact.element.clone(),
            right: start.clone(),
            line_file: None,
        }));
        let left_proof = self.verify_builtin_rule_premise(&left_out, verify_state.clone())?;
        if !left_proof.is_failed() {
            return Ok(Some(
                NotInFactSearchProofByBuiltinRule::NonMembershipOfIntervalOutside(
                    NonMembershipOfIntervalOutsideBuiltinRuleProof {
                        outside_order_proof: left_proof,
                    },
                ),
            ));
        }
        // end < x
        let right_out = Fact::AtomicFact(AtomicFact::LessFact(LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: end.clone(),
            right: fact.element.clone(),
            line_file: None,
        }));
        let right_proof = self.verify_builtin_rule_premise(&right_out, verify_state)?;
        if right_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NotInFactSearchProofByBuiltinRule::NonMembershipOfIntervalOutside(
                NonMembershipOfIntervalOutsideBuiltinRuleProof {
                    outside_order_proof: right_proof,
                },
            ),
        ))
    }

    fn one_side_interval_non_membership_proof(
        &mut self,
        fact: &NotInFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInFactSearchProofByBuiltinRule>> {
        let Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(interval)) = &fact.set else {
            return Ok(None);
        };
        let (is_lower_bound, closed, endpoint) = match interval {
            OneSideInfinityIntervalObj::LowerOpen(s) => (true, false, s.start.as_ref()),
            OneSideInfinityIntervalObj::LowerClosed(s) => (true, true, s.start.as_ref()),
            OneSideInfinityIntervalObj::UpperOpen(s) => (false, false, s.start.as_ref()),
            OneSideInfinityIntervalObj::UpperClosed(s) => (false, true, s.start.as_ref()),
        };

        if !closed {
            let eq = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: fact.element.clone(),
                right: endpoint.clone(),
                line_file: None,
            }));
            let proof = self.verify_builtin_rule_premise(&eq, verify_state.clone())?;
            if !proof.is_failed() {
                return Ok(Some(
                    NotInFactSearchProofByBuiltinRule::NonMembershipOfIntervalAtOpenEndpoint(
                        NonMembershipOfIntervalAtOpenEndpointBuiltinRuleProof {
                            endpoint_equal_proof: proof,
                        },
                    ),
                ));
            }
        }

        let outside = if is_lower_bound {
            // x < endpoint (or x <= when closed — use strict less for outside of [a,))
            if closed {
                Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: fact.element.clone(),
                    right: endpoint.clone(),
                    line_file: None,
                }))
            } else {
                Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: fact.element.clone(),
                    right: endpoint.clone(),
                    line_file: None,
                }))
            }
        } else if closed {
            Fact::AtomicFact(AtomicFact::LessFact(LessFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: endpoint.clone(),
                right: fact.element.clone(),
                line_file: None,
            }))
        } else {
            Fact::AtomicFact(AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: endpoint.clone(),
                right: fact.element.clone(),
                line_file: None,
            }))
        };
        let proof = self.verify_builtin_rule_premise(&outside, verify_state)?;
        if proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            NotInFactSearchProofByBuiltinRule::NonMembershipOfIntervalOutside(
                NonMembershipOfIntervalOutsideBuiltinRuleProof {
                    outside_order_proof: proof,
                },
            ),
        ))
    }
}

fn closed_numeric_non_membership_proof(
    fact: &NotInFact,
) -> Option<NotInFactSearchProofByBuiltinRule> {
    let number = evaluate_obj_to_normalized_decimal_number(&fact.element)?;
    let Obj::StandardSet(set) = &fact.set else {
        return None;
    };
    // C / R / Q contain every real decimal; non-membership cannot fire there.
    if matches!(set, StandardSet::C | StandardSet::R | StandardSet::Q) {
        return None;
    }
    if normalized_decimal_inhabits_standard_set(&number.normalized_value, set) {
        return None;
    }
    Some(
        NotInFactSearchProofByBuiltinRule::ClosedNumericNonMembership(
            ClosedNumericNonMembershipBuiltinRuleProof {
                normal: number.normalized_value,
            },
        ),
    )
}
