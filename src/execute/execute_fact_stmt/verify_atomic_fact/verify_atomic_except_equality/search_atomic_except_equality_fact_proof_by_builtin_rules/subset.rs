use crate::ast::fact::{AtomicFact, EqualFact, Fact, InFact, SubsetFact};
use crate::ast::names::AtomicName;
use crate::ast::obj::{Cart, FunctionSpace, Obj, ProductShape, SetFormer, SetOperator, StandardSet, Union};
use crate::execute::execute_fact_stmt::function_preimage::FunctionPreimageConstructionProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::parse::keywords::SUBSET;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin proofs for `$subset`. One rule ↔ one dedicated proof struct.
pub enum SubsetFactSearchProofByBuiltinRule {
    // Fixed inclusion among standard number sets.
    // Example: prove `N $subset R`.
    StandardSetSubset(StandardSetSubsetBuiltinRuleProof),
    // `intersect(A, B) $subset A`.
    // Example: prove `intersect({1, 2}, {2}) $subset {1, 2}`.
    IntersectSubsetLeft(IntersectSubsetLeftBuiltinRuleProof),
    // `intersect(A, B) $subset B`.
    // Example: prove `intersect({1, 2}, {2}) $subset {2}`.
    IntersectSubsetRight(IntersectSubsetRightBuiltinRuleProof),
    // `A $subset union(A, B)`.
    // Example: prove `{1} $subset union({1}, {2})`.
    SubsetUnionLeft(SubsetUnionLeftBuiltinRuleProof),
    // `B $subset union(A, B)`.
    // Example: prove `{2} $subset union({1}, {2})`.
    SubsetUnionRight(SubsetUnionRightBuiltinRuleProof),
    // `set_minus(A, B) $subset A`.
    // Example: prove `set_minus({1, 2}, {1}) $subset {1, 2}`.
    SetMinusSubsetLeft(SetMinusSubsetLeftBuiltinRuleProof),
    // Real intervals inhabit R.
    // Example: prove `'[a, b] $subset R`.
    RealIntervalSubsetReal(RealIntervalSubsetRealBuiltinRuleProof),
    // `{x S: P…} $subset S`.
    // Example: prove `{x R: x > 0} $subset R`.
    SetBuilderSubsetOfParamSet(SetBuilderSubsetOfParamSetBuiltinRuleProof),
    // A certified point/set preimage is a subset of its complete input carrier.
    // Example: preimage_set(square, {4}) $subset R for square : R -> R.
    FunctionPreimageSubsetOfInputCarrier(FunctionPreimageSubsetOfInputCarrierBuiltinRuleProof),
    // Reflexivity: `A $subset A`.
    // Example: prove `{1, 2} $subset {1, 2}`.
    SubsetReflexivity(SubsetReflexivityBuiltinRuleProof),
    // `A $subset S` and `B $subset S` ⇒ `union(A, B) $subset S`.
    // Example: prove `union({1}, {2}) $subset N`.
    UnionSubsetFromBothOperands(UnionSubsetFromBothOperandsBuiltinRuleProof),
    // `A $subset S` ⇒ `intersect(A, B) $subset S`.
    // Example: prove `intersect({1, 2}, {2, 3}) $subset N`.
    IntersectSubsetFromLeftUpperBound(IntersectSubsetFromLeftUpperBoundBuiltinRuleProof),
    // `B $subset S` ⇒ `intersect(A, B) $subset S`.
    // Example: prove `intersect({0}, {1, 2}) $subset N` from `{1, 2} $subset N`.
    IntersectSubsetFromRightUpperBound(IntersectSubsetFromRightUpperBoundBuiltinRuleProof),
    // `{a1, …, an} $subset S` from each `ai $in S`.
    // Example: prove `{1, 2} $subset N`.
    ListSetSubsetFromMembers(ListSetSubsetFromMembersBuiltinRuleProof),
    // `union(A, B) $subset union(C, D)` from componentwise subsets
    // (same operand order or crossed).
    // Example: trust `A $subset C`; trust `B $subset D`;
    //          `union(A, B) $subset union(C, D)`.
    UnionSubsetFromComponentwise(UnionSubsetFromComponentwiseBuiltinRuleProof),
    // Integer `range` / `closed_range` sits in its numeric carrier.
    // For `N` / `N+`, the start must already inhabit that carrier.
    // Example: have `a N`; have `b Z`; `a...b $subset N`.
    IntegerRangeSubsetNumericCarrier(IntegerRangeSubsetNumericCarrierBuiltinRuleProof),
    // `A $subset B` ⇒ `power_set(A) $subset power_set(B)`.
    // Example: trust `A $subset B`; prove `power_set(A) $subset power_set(B)`.
    SubsetPowerSetMonotone(SubsetPowerSetMonotoneBuiltinRuleProof),
    // `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`.
    // Example: trust `A $subset B`; prove `set_minus(A, C) $subset set_minus(B, C)`.
    SubsetSetMinusCommonRightMonotone(SubsetSetMinusCommonRightMonotoneBuiltinRuleProof),
    // Componentwise: `A $subset C`, `B $subset D` ⇒ `cart(A, B) $subset cart(C, D)`.
    // Example: trust `A $subset C`; trust `B $subset D`;
    //          `cart(A, B) $subset cart(C, D)`.
    SubsetCartComponentwise(SubsetCartComponentwiseBuiltinRuleProof),
    // Transitivity through one known middle set: `A $subset B`, `B $subset C`
    // ⇒ `A $subset C`.
    // Example: trust `A $subset B`; trust `B $subset C`; prove `A $subset C`.
    SubsetTransitivity(SubsetTransitivityBuiltinRuleProof),
}

pub struct StandardSetSubsetBuiltinRuleProof {
    pub left: StandardSet,
    pub right: StandardSet,
}

pub struct IntersectSubsetLeftBuiltinRuleProof {}
pub struct IntersectSubsetRightBuiltinRuleProof {}
pub struct SubsetUnionLeftBuiltinRuleProof {}
pub struct SubsetUnionRightBuiltinRuleProof {}
pub struct SetMinusSubsetLeftBuiltinRuleProof {}
pub struct RealIntervalSubsetRealBuiltinRuleProof {}
pub struct SetBuilderSubsetOfParamSetBuiltinRuleProof {}
pub struct FunctionPreimageSubsetOfInputCarrierBuiltinRuleProof {
    pub construction: FunctionPreimageConstructionProof,
    pub carrier_match: EqualFactSearchedProof,
}

impl FunctionPreimageSubsetOfInputCarrierBuiltinRuleProof {
    pub fn new(
        construction: FunctionPreimageConstructionProof,
        carrier_match: EqualFactSearchedProof,
    ) -> Self {
        Self { construction, carrier_match }
    }
}
pub struct SubsetReflexivityBuiltinRuleProof {}

pub struct UnionSubsetFromBothOperandsBuiltinRuleProof {
    pub left_operand_subset_proof: VerifyFactResult,
    pub right_operand_subset_proof: VerifyFactResult,
}

pub struct IntersectSubsetFromLeftUpperBoundBuiltinRuleProof {
    pub left_operand_subset_proof: VerifyFactResult,
}

pub struct IntersectSubsetFromRightUpperBoundBuiltinRuleProof {
    pub right_operand_subset_proof: VerifyFactResult,
}

pub struct ListSetSubsetFromMembersBuiltinRuleProof {
    pub member_in_proofs: Vec<VerifyFactResult>,
}

pub struct UnionSubsetFromComponentwiseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct IntegerRangeSubsetNumericCarrierBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct SubsetPowerSetMonotoneBuiltinRuleProof {
    pub base_subset_proof: VerifyFactResult,
}

pub struct SubsetSetMinusCommonRightMonotoneBuiltinRuleProof {
    pub left_operand_subset_proof: VerifyFactResult,
}

pub struct SubsetCartComponentwiseBuiltinRuleProof {
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct SubsetTransitivityBuiltinRuleProof {
    pub left_to_middle_proof: VerifyFactResult,
    pub middle_to_right_proof: VerifyFactResult,
}

impl Runtime {
    // Builtin search for `$subset`.
    // B0: reflexivity. A: match Obj shapes of (left, right). No sequential rule list.
    // Example: prove `N $subset R`, `union({1}, {2}) $subset N`.
    pub fn search_subset_fact_proof_by_builtin_rule(
        &mut self,
        fact: &SubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        // B0 — non-shape
        if fact.left.ir() == fact.right.ir() {
            return Ok(Some(SubsetFactSearchProofByBuiltinRule::SubsetReflexivity(
                SubsetReflexivityBuiltinRuleProof {},
            )));
        }

        // A — shape dispatch
        let shape = match (&fact.left, &fact.right) {
            (Obj::StandardSet(left), Obj::StandardSet(right)) => {
                if standard_set_is_subset_eq(left, right) {
                    return Ok(Some(SubsetFactSearchProofByBuiltinRule::StandardSetSubset(
                        StandardSetSubsetBuiltinRuleProof {
                            left: left.clone(),
                            right: right.clone(),
                        },
                    )));
                }
                Ok(None)
            }

            (Obj::SetOperator(SetOperator::Intersect(intersect)), right) => {
                if intersect.left.as_ref() == right {
                    return Ok(Some(
                        SubsetFactSearchProofByBuiltinRule::IntersectSubsetLeft(
                            IntersectSubsetLeftBuiltinRuleProof {},
                        ),
                    ));
                }
                if intersect.right.as_ref() == right {
                    return Ok(Some(
                        SubsetFactSearchProofByBuiltinRule::IntersectSubsetRight(
                            IntersectSubsetRightBuiltinRuleProof {},
                        ),
                    ));
                }
                if let Some(proof) = self.intersect_subset_from_left_upper_bound_proof(
                    intersect.left.as_ref(),
                    right,
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
                self.intersect_subset_from_right_upper_bound_proof(
                    intersect.right.as_ref(),
                    right,
                    verify_state.clone(),
                )
            }

            (Obj::SetOperator(SetOperator::Union(left_union)), Obj::SetOperator(SetOperator::Union(right_union))) => {
                if let Some(proof) = self.union_subset_from_componentwise_proof(
                    left_union,
                    right_union,
                    verify_state.clone(),
                )? {
                    return Ok(Some(proof));
                }
                self.union_subset_from_both_operands_proof(
                    left_union.left.as_ref(),
                    left_union.right.as_ref(),
                    &fact.right,
                    verify_state.clone(),
                )
            }

            (left, Obj::SetOperator(SetOperator::Union(union))) => {
                if union.left.as_ref() == left {
                    return Ok(Some(SubsetFactSearchProofByBuiltinRule::SubsetUnionLeft(
                        SubsetUnionLeftBuiltinRuleProof {},
                    )));
                }
                if union.right.as_ref() == left {
                    return Ok(Some(SubsetFactSearchProofByBuiltinRule::SubsetUnionRight(
                        SubsetUnionRightBuiltinRuleProof {},
                    )));
                }
                Ok(None)
            }

            (Obj::SetOperator(SetOperator::Union(union)), right) => self
                .union_subset_from_both_operands_proof(
                    union.left.as_ref(),
                    union.right.as_ref(),
                    right,
                    verify_state.clone(),
                ),

            (
                Obj::SetOperator(SetOperator::SetMinus(left_minus)),
                Obj::SetOperator(SetOperator::SetMinus(right_minus)),
            ) => {
                if left_minus.right.as_ref().ir() == right_minus.right.as_ref().ir() {
                    if let Some(proof) = self.subset_set_minus_common_right_monotone_proof(
                        left_minus.left.as_ref(),
                        right_minus.left.as_ref(),
                        verify_state.clone(),
                    )? {
                        return Ok(Some(proof));
                    }
                }
                if left_minus.left.as_ref() == &fact.right {
                    return Ok(Some(
                        SubsetFactSearchProofByBuiltinRule::SetMinusSubsetLeft(
                            SetMinusSubsetLeftBuiltinRuleProof {},
                        ),
                    ));
                }
                Ok(None)
            }

            (Obj::SetOperator(SetOperator::SetMinus(set_minus)), right)
                if set_minus.left.as_ref() == right =>
            {
                Ok(Some(
                    SubsetFactSearchProofByBuiltinRule::SetMinusSubsetLeft(
                        SetMinusSubsetLeftBuiltinRuleProof {},
                    ),
                ))
            }

            (
                Obj::SetOperator(SetOperator::PowerSet(left_power)),
                Obj::SetOperator(SetOperator::PowerSet(right_power)),
            ) => self.subset_power_set_monotone_proof(
                left_power.set.as_ref(),
                right_power.set.as_ref(),
                verify_state.clone(),
            ),

            (
                Obj::ProductShape(ProductShape::Cart(left_cart)),
                Obj::ProductShape(ProductShape::Cart(right_cart)),
            ) => self.subset_cart_componentwise_proof(left_cart, right_cart, verify_state.clone()),

            (
                Obj::SetFormer(SetFormer::IntervalObj(_))
                | Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(_)),
                Obj::StandardSet(StandardSet::R),
            ) => Ok(Some(
                SubsetFactSearchProofByBuiltinRule::RealIntervalSubsetReal(
                    RealIntervalSubsetRealBuiltinRuleProof {},
                ),
            )),

            (Obj::SetFormer(SetFormer::SetBuilder(builder)), right)
                if builder.param_set.as_ref().ir() == right.ir() =>
            {
                Ok(Some(
                    SubsetFactSearchProofByBuiltinRule::SetBuilderSubsetOfParamSet(
                        SetBuilderSubsetOfParamSetBuiltinRuleProof {},
                    ),
                ))
            }

            (Obj::SetFormer(SetFormer::ListSet(list_set)), right) => {
                self.list_set_subset_from_members_proof(&list_set.list, right, verify_state.clone())
            }

            (
                Obj::SetFormer(SetFormer::Range(range)),
                Obj::StandardSet(target),
            ) => self.integer_range_subset_numeric_carrier_proof(
                range.start.as_ref(),
                target,
                verify_state.clone(),
            ),

            (
                Obj::SetFormer(SetFormer::ClosedRange(range)),
                Obj::StandardSet(target),
            ) => self.integer_range_subset_numeric_carrier_proof(
                range.start.as_ref(),
                target,
                verify_state.clone(),
            ),

            _ => Ok(None),
        }?;
        if shape.is_some() {
            return Ok(shape);
        }

        // Preserve ordinary union/intersection inclusion priority.
        if matches!(fact.left, Obj::FunctionSpace(FunctionSpace::Preimage(_) | FunctionSpace::PreimageSet(_))) {
            if let Some(proof) = self.function_preimage_subset_input_carrier_proof(fact, verify_state)? {
                return Ok(Some(proof));
            }
        }

        // Bounded leaf: one known middle set for transitivity.
        self.subset_transitivity_proof(fact, verify_state)
    }

    fn list_set_subset_from_members_proof(
        &mut self,
        members: &[Box<Obj>],
        right: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let mut member_in_proofs = Vec::with_capacity(members.len());
        for element in members {
            let premise = in_fact(element.as_ref(), right, self);
            let proof = self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            member_in_proofs.push(proof);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::ListSetSubsetFromMembers(
                ListSetSubsetFromMembersBuiltinRuleProof { member_in_proofs },
            ),
        ))
    }

    fn union_subset_from_both_operands_proof(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        ambient: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let left_premise = subset_fact(left_operand, ambient, self);
        let left_operand_subset_proof = self.verify_builtin_rule_premise(&left_premise, verify_state.clone())?;
        if left_operand_subset_proof.is_failed() {
            return Ok(None);
        }
        let right_premise = subset_fact(right_operand, ambient, self);
        let right_operand_subset_proof = self.verify_builtin_rule_premise(&right_premise, verify_state)?;
        if right_operand_subset_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::UnionSubsetFromBothOperands(
                UnionSubsetFromBothOperandsBuiltinRuleProof {
                    left_operand_subset_proof,
                    right_operand_subset_proof,
                },
            ),
        ))
    }

    fn intersect_subset_from_left_upper_bound_proof(
        &mut self,
        left_operand: &Obj,
        ambient: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let premise = subset_fact(left_operand, ambient, self);
        let left_operand_subset_proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if left_operand_subset_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::IntersectSubsetFromLeftUpperBound(
                IntersectSubsetFromLeftUpperBoundBuiltinRuleProof {
                    left_operand_subset_proof,
                },
            ),
        ))
    }

    fn intersect_subset_from_right_upper_bound_proof(
        &mut self,
        right_operand: &Obj,
        ambient: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let premise = subset_fact(right_operand, ambient, self);
        let right_operand_subset_proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if right_operand_subset_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::IntersectSubsetFromRightUpperBound(
                IntersectSubsetFromRightUpperBoundBuiltinRuleProof {
                    right_operand_subset_proof,
                },
            ),
        ))
    }

    fn union_subset_from_componentwise_proof(
        &mut self,
        left_union: &Union,
        right_union: &Union,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        for ((l1, r1), (l2, r2)) in [
            (
                (left_union.left.as_ref(), right_union.left.as_ref()),
                (left_union.right.as_ref(), right_union.right.as_ref()),
            ),
            (
                (left_union.left.as_ref(), right_union.right.as_ref()),
                (left_union.right.as_ref(), right_union.left.as_ref()),
            ),
        ] {
            let mut proofs = Vec::new();
            let mut ok = true;
            for (left, right) in [(l1, r1), (l2, r2)] {
                if left.ir() == right.ir() {
                    continue;
                }
                let premise = subset_fact(left, right, self);
                let proof = self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
                if proof.is_failed() {
                    ok = false;
                    break;
                }
                proofs.push(proof);
            }
            if ok {
                return Ok(Some(
                    SubsetFactSearchProofByBuiltinRule::UnionSubsetFromComponentwise(
                        UnionSubsetFromComponentwiseBuiltinRuleProof {
                            proof_of_requirement_facts: proofs,
                        },
                    ),
                ));
            }
        }
        Ok(None)
    }

    fn integer_range_subset_numeric_carrier_proof(
        &mut self,
        start: &Obj,
        target: &StandardSet,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let required_start = match target {
            StandardSet::N => Some(StandardSet::N),
            StandardSet::NPos => Some(StandardSet::NPos),
            other if standard_set_is_subset_eq(&StandardSet::Z, other) => None,
            _ => return Ok(None),
        };
        let mut proofs = Vec::new();
        if let Some(required_start) = required_start {
            let premise = in_fact(start, &Obj::StandardSet(required_start), self);
            let proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
            if proof.is_failed() {
                return Ok(None);
            }
            proofs.push(proof);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::IntegerRangeSubsetNumericCarrier(
                IntegerRangeSubsetNumericCarrierBuiltinRuleProof {
                    proof_of_requirement_facts: proofs,
                },
            ),
        ))
    }

    // `A $subset B` ⇒ `power_set(A) $subset power_set(B)`.
    fn subset_power_set_monotone_proof(
        &mut self,
        left_base: &Obj,
        right_base: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let premise = subset_fact(left_base, right_base, self);
        let base_subset_proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if base_subset_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::SubsetPowerSetMonotone(
                SubsetPowerSetMonotoneBuiltinRuleProof { base_subset_proof },
            ),
        ))
    }

    // `A $subset B` ⇒ `set_minus(A, C) $subset set_minus(B, C)`.
    fn subset_set_minus_common_right_monotone_proof(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let premise = subset_fact(left_operand, right_operand, self);
        let left_operand_subset_proof = self.verify_builtin_rule_premise(&premise, verify_state)?;
        if left_operand_subset_proof.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::SubsetSetMinusCommonRightMonotone(
                SubsetSetMinusCommonRightMonotoneBuiltinRuleProof {
                    left_operand_subset_proof,
                },
            ),
        ))
    }

    // Componentwise cart inclusion from factor subsets.
    fn subset_cart_componentwise_proof(
        &mut self,
        left_cart: &Cart,
        right_cart: &Cart,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        if left_cart.args.len() != right_cart.args.len() {
            return Ok(None);
        }
        let mut proofs = Vec::new();
        for (left_factor, right_factor) in left_cart.args.iter().zip(right_cart.args.iter()) {
            if left_factor.as_ref().ir() == right_factor.as_ref().ir() {
                continue;
            }
            let premise = subset_fact(left_factor.as_ref(), right_factor.as_ref(), self);
            let proof = self.verify_builtin_rule_premise(&premise, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proofs.push(proof);
        }
        Ok(Some(
            SubsetFactSearchProofByBuiltinRule::SubsetCartComponentwise(
                SubsetCartComponentwiseBuiltinRuleProof {
                    proof_of_requirement_facts: proofs,
                },
            ),
        ))
    }

    // `A $subset B`, `B $subset C` through one stored middle set.
    fn subset_transitivity_proof(
        &mut self,
        fact: &SubsetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let left_ir = fact.left.ir();
        let right_ir = fact.right.ir();
        let key = (
            AtomicName::Plain {
                name: SUBSET.into(),
            },
            true,
        );
        let mut known_subsets = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env.facts.known_atomic_except_equality_facts.by_prop.get(&key)
            else {
                continue;
            };
            for known in knowns {
                if let AtomicFact::SubsetFact(s) = known {
                    known_subsets.push((s.left.clone(), s.right.clone()));
                }
            }
        }
        for (first_left, first_right) in &known_subsets {
            if first_left.ir() != left_ir {
                continue;
            }
            let middle_ir = first_right.ir();
            for (second_left, second_right) in &known_subsets {
                if second_left.ir() != middle_ir || second_right.ir() != right_ir {
                    continue;
                }
                let left_premise = subset_fact(first_left, first_right, self);
                let left_to_middle_proof =
                    self.verify_builtin_rule_premise(&left_premise, verify_state.clone())?;
                if left_to_middle_proof.is_failed() {
                    continue;
                }
                let right_premise = subset_fact(second_left, second_right, self);
                let middle_to_right_proof = self.verify_builtin_rule_premise(&right_premise, verify_state.clone())?;
                if middle_to_right_proof.is_failed() {
                    continue;
                }
                return Ok(Some(SubsetFactSearchProofByBuiltinRule::SubsetTransitivity(
                    SubsetTransitivityBuiltinRuleProof {
                        left_to_middle_proof,
                        middle_to_right_proof,
                    },
                )));
            }
        }
        Ok(None)
    }
}

impl Runtime {
    // Consume the existing checked bounded builder; do not search for a wider
    // input domain or infer arbitrary subset relationships.
    fn function_preimage_subset_input_carrier_proof(
        &mut self,
        fact: &SubsetFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<SubsetFactSearchProofByBuiltinRule>> {
        let Ok(construction) = self.verify_function_preimage_construction(&fact.left, state)? else {
            return Ok(None);
        };
        let comparison = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: construction.builder.param_set.as_ref().clone(),
            right: fact.right.clone(),
            line_file: fact.line_file.clone(),
        };
        let Some(carrier_match) = search_equal_fact_proof_by_they_are_the_same(&comparison) else {
            return Ok(None);
        };
        Ok(Some(SubsetFactSearchProofByBuiltinRule::FunctionPreimageSubsetOfInputCarrier(
            FunctionPreimageSubsetOfInputCarrierBuiltinRuleProof::new(
                construction, carrier_match.into(),
            ),
        )))
    }
}

#[cfg(test)]
#[path = "../../../../../../tests/unit/execute/preimage_input_carrier/tests.rs"]
mod preimage_input_carrier_tests;

pub(crate) fn standard_set_is_subset_eq(left: &StandardSet, right: &StandardSet) -> bool {
    matches!(
        (left, right),
        (_, StandardSet::C)
            | (StandardSet::NPos, StandardSet::NPos)
            | (StandardSet::NPos, StandardSet::N)
            | (StandardSet::NPos, StandardSet::Z)
            | (StandardSet::NPos, StandardSet::Q)
            | (StandardSet::NPos, StandardSet::R)
            | (StandardSet::NPos, StandardSet::QPos)
            | (StandardSet::NPos, StandardSet::RPos)
            | (StandardSet::NPos, StandardSet::ZStar)
            | (StandardSet::NPos, StandardSet::QStar)
            | (StandardSet::NPos, StandardSet::RStar)
            | (StandardSet::N, StandardSet::N)
            | (StandardSet::N, StandardSet::Z)
            | (StandardSet::N, StandardSet::Q)
            | (StandardSet::N, StandardSet::R)
            | (StandardSet::ZNeg, StandardSet::ZNeg)
            | (StandardSet::ZNeg, StandardSet::Z)
            | (StandardSet::ZNeg, StandardSet::Q)
            | (StandardSet::ZNeg, StandardSet::R)
            | (StandardSet::ZNeg, StandardSet::QNeg)
            | (StandardSet::ZNeg, StandardSet::RNeg)
            | (StandardSet::ZNeg, StandardSet::ZStar)
            | (StandardSet::ZNeg, StandardSet::QStar)
            | (StandardSet::ZNeg, StandardSet::RStar)
            | (StandardSet::ZStar, StandardSet::ZStar)
            | (StandardSet::ZStar, StandardSet::Z)
            | (StandardSet::ZStar, StandardSet::Q)
            | (StandardSet::ZStar, StandardSet::R)
            | (StandardSet::ZStar, StandardSet::QStar)
            | (StandardSet::ZStar, StandardSet::RStar)
            | (StandardSet::Z, StandardSet::Z)
            | (StandardSet::Z, StandardSet::Q)
            | (StandardSet::Z, StandardSet::R)
            | (StandardSet::QPos, StandardSet::QPos)
            | (StandardSet::QPos, StandardSet::Q)
            | (StandardSet::QPos, StandardSet::R)
            | (StandardSet::QPos, StandardSet::RPos)
            | (StandardSet::QPos, StandardSet::QStar)
            | (StandardSet::QPos, StandardSet::RStar)
            | (StandardSet::QNeg, StandardSet::QNeg)
            | (StandardSet::QNeg, StandardSet::Q)
            | (StandardSet::QNeg, StandardSet::R)
            | (StandardSet::QNeg, StandardSet::RNeg)
            | (StandardSet::QNeg, StandardSet::QStar)
            | (StandardSet::QNeg, StandardSet::RStar)
            | (StandardSet::QStar, StandardSet::QStar)
            | (StandardSet::QStar, StandardSet::Q)
            | (StandardSet::QStar, StandardSet::R)
            | (StandardSet::QStar, StandardSet::RStar)
            | (StandardSet::Q, StandardSet::Q)
            | (StandardSet::Q, StandardSet::R)
            | (StandardSet::RPos, StandardSet::RPos)
            | (StandardSet::RPos, StandardSet::R)
            | (StandardSet::RPos, StandardSet::RStar)
            | (StandardSet::RNeg, StandardSet::RNeg)
            | (StandardSet::RNeg, StandardSet::R)
            | (StandardSet::RNeg, StandardSet::RStar)
            | (StandardSet::RStar, StandardSet::RStar)
            | (StandardSet::RStar, StandardSet::R)
            | (StandardSet::NPos, StandardSet::CStar)
            | (StandardSet::ZNeg, StandardSet::CStar)
            | (StandardSet::ZStar, StandardSet::CStar)
            | (StandardSet::QPos, StandardSet::CStar)
            | (StandardSet::QNeg, StandardSet::CStar)
            | (StandardSet::QStar, StandardSet::CStar)
            | (StandardSet::RPos, StandardSet::CStar)
            | (StandardSet::RNeg, StandardSet::CStar)
            | (StandardSet::RStar, StandardSet::CStar)
            | (StandardSet::CStar, StandardSet::CStar)
            | (StandardSet::R, StandardSet::R)
    )
}

fn subset_fact(left: &Obj, right: &Obj, runtime: &mut Runtime) -> Fact {
    Fact::AtomicFact(AtomicFact::SubsetFact(SubsetFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: left.clone(),
        right: right.clone(),
        line_file: None,
    }))
}

fn in_fact(element: &Obj, set: &Obj, runtime: &mut Runtime) -> Fact {
    Fact::AtomicFact(AtomicFact::InFact(InFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        element: element.clone(),
        set: set.clone(),
        line_file: None,
    }))
}
