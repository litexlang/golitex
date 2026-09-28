use crate::new_pipeline::ast::fact::{
    and_chain_as_fact, atomic_fact_has_positive_polarity, negate_atomic_fact, AndChainAtomicFact,
    AtomicFact, Fact, GreaterEqualFact, InFact, OrFact,
};
use crate::new_pipeline::ast::obj::{Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::helper::{
    complementary_atomic_pair, equal_matches_pair, is_number_obj, match_abs_sign_split_arg,
    match_complete_residues, match_component_nonzero_pair,
    match_equality_plus_strict_covers_weak, match_greater_or_less_equal_operands,
    match_integer_discrete_split, match_integer_successor_tail,
    match_less_or_greater_equal_operands, match_weak_order_le_or_ge_operands, objs_same,
    square_sum_nonzero_candidates, zero_factor_from_equal,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::result::{
    OrBuiltinAbsSignSplit, OrBuiltinClassicalImplication, OrBuiltinComplementaryAtomic,
    OrBuiltinCompleteResidues, OrBuiltinEqualityPlusStrictCoversWeak,
    OrBuiltinGreaterOrLessEqual, OrBuiltinIntegerDiscreteSplit, OrBuiltinIntegerSuccessorTail,
    OrBuiltinLessOrGreaterEqual, OrBuiltinNaturalZeroOrAtLeastOne,
    OrBuiltinRealLineTrichotomyEqLessGreater, OrBuiltinRealLineTrichotomyGreaterEqLess,
    OrBuiltinRealLineTrichotomyLessEqGreater, OrBuiltinSquareSumComponentNonzero,
    OrBuiltinWeakOrderLeOrGe, OrBuiltinZeroProductSplit, OrFactSearchProofByBuiltinRule,
    OrFactSearchedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyFactWellDefinedResult, VerifyState,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

impl Runtime {
    // Or builtin search: trichotomy, natural zero/at-least-one, complementary
    // atomics, abs sign, zero product, strict/weak complementary, weak comparability,
    // equality-plus-strict, complete residues, successor tail, square-sum nonzero,
    // classical implication packaging, integer discrete split.
    pub(crate) fn search_or_fact_proof_by_builtin_rule(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        if let Some(proof) = self.search_or_complete_residues(fact)? {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_or_integer_successor_tail(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if fact.facts.len() == 2 {
            if let Some(proof) =
                self.search_or_natural_zero_or_at_least_one(fact, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
            if let Some(proof) = self.search_or_complementary_atomic(fact)? {
                return Ok(Some(proof));
            }
            if let Some(proof) = self.search_or_abs_sign_split(fact)? {
                return Ok(Some(proof));
            }
            if let Some(proof) = self.search_or_zero_product_split(fact, verify_state.clone())? {
                return Ok(Some(proof));
            }
            if let Some(proof) =
                self.search_or_less_or_greater_equal(fact, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
            if let Some(proof) =
                self.search_or_greater_or_less_equal(fact, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
            if let Some(proof) =
                self.search_or_weak_order_le_or_ge(fact, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
            if let Some(proof) =
                self.search_or_equality_plus_strict_covers_weak(fact, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
            if let Some(proof) =
                self.search_or_square_sum_component_nonzero(fact, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
            if let Some(proof) =
                self.search_or_integer_discrete_split(fact, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
            if let Some(proof) =
                self.search_or_classical_implication(fact, verify_state)?
            {
                return Ok(Some(proof));
            }
            return Ok(None);
        }
        if fact.facts.len() != 3 {
            return Ok(None);
        }

        // Rule: exact `a = b or a < b or a > b`.
        if let (
            AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)),
            AndChainAtomicFact::AtomicFact(AtomicFact::LessFact(less)),
            AndChainAtomicFact::AtomicFact(AtomicFact::GreaterFact(greater)),
        ) = (&fact.facts[0], &fact.facts[1], &fact.facts[2])
        {
            if objs_same(&less.left, &greater.left)
                && objs_same(&less.right, &greater.right)
                && equal_matches_pair(eq, &less.left, &less.right)
            {
                let left = less.left.clone();
                let right = less.right.clone();
                if let Some((left_in_r, right_in_r)) =
                    self.prove_both_objs_in_r(&left, &right, verify_state.clone())?
                {
                    return Ok(Some(OrFactSearchedProof::ByBuiltinRule(
                        OrFactSearchProofByBuiltinRule::RealLineTrichotomyEqLessGreater(
                            OrBuiltinRealLineTrichotomyEqLessGreater {
                                left,
                                right,
                                left_in_r,
                                right_in_r,
                            },
                        ),
                    )));
                }
            }
        }

        // Rule: exact `a < b or a = b or a > b`.
        if let (
            AndChainAtomicFact::AtomicFact(AtomicFact::LessFact(less)),
            AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)),
            AndChainAtomicFact::AtomicFact(AtomicFact::GreaterFact(greater)),
        ) = (&fact.facts[0], &fact.facts[1], &fact.facts[2])
        {
            if objs_same(&less.left, &greater.left)
                && objs_same(&less.right, &greater.right)
                && equal_matches_pair(eq, &less.left, &less.right)
            {
                let left = less.left.clone();
                let right = less.right.clone();
                if let Some((left_in_r, right_in_r)) =
                    self.prove_both_objs_in_r(&left, &right, verify_state.clone())?
                {
                    return Ok(Some(OrFactSearchedProof::ByBuiltinRule(
                        OrFactSearchProofByBuiltinRule::RealLineTrichotomyLessEqGreater(
                            OrBuiltinRealLineTrichotomyLessEqGreater {
                                left,
                                right,
                                left_in_r,
                                right_in_r,
                            },
                        ),
                    )));
                }
            }
        }

        // Rule: exact `a > b or a = b or a < b`.
        if let (
            AndChainAtomicFact::AtomicFact(AtomicFact::GreaterFact(greater)),
            AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)),
            AndChainAtomicFact::AtomicFact(AtomicFact::LessFact(less)),
        ) = (&fact.facts[0], &fact.facts[1], &fact.facts[2])
        {
            if objs_same(&less.left, &greater.left)
                && objs_same(&less.right, &greater.right)
                && equal_matches_pair(eq, &less.left, &less.right)
            {
                let left = less.left.clone();
                let right = less.right.clone();
                if let Some((left_in_r, right_in_r)) =
                    self.prove_both_objs_in_r(&left, &right, verify_state)?
                {
                    return Ok(Some(OrFactSearchedProof::ByBuiltinRule(
                        OrFactSearchProofByBuiltinRule::RealLineTrichotomyGreaterEqLess(
                            OrBuiltinRealLineTrichotomyGreaterEqLess {
                                left,
                                right,
                                left_in_r,
                                right_in_r,
                            },
                        ),
                    )));
                }
            }
        }

        Ok(None)
    }

    // Exact `n = 0 or n >= 1` after `n $in N`.
    fn search_or_natural_zero_or_at_least_one(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)),
            AndChainAtomicFact::AtomicFact(AtomicFact::GreaterEqualFact(ge)),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        if !is_number_obj(&eq.right, "0") || !is_number_obj(&ge.right, "1") {
            return Ok(None);
        }
        if !objs_same(&eq.left, &ge.left) {
            return Ok(None);
        }
        let n = eq.left.clone();
        let in_n = crate::new_pipeline::ast::fact::Fact::AtomicFact(AtomicFact::InFact(InFact {
            fact_id: self.global_ids.allocate_fact_id(),
            element: n.clone(),
            set: Obj::StandardSet(StandardSet::N),
            line_file: fact.line_file.clone(),
        }));
        let n_in_n = self.verify_fact(&in_n, verify_state)?;
        if n_in_n.is_failed() {
            return Ok(None);
        }
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::NaturalZeroOrAtLeastOne(
                OrBuiltinNaturalZeroOrAtLeastOne { n, n_in_n },
            ),
        )))
    }

    // Either order: complementary atomics `P or not P`.
    // Example: `1 = 1 or 1 != 1`.
    fn search_or_complementary_atomic(
        &mut self,
        fact: &OrFact,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(left),
            AndChainAtomicFact::AtomicFact(right),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        if !complementary_atomic_pair(left, right) {
            return Ok(None);
        }
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::ComplementaryAtomic(OrBuiltinComplementaryAtomic {
                left: left.clone(),
                right: right.clone(),
            }),
        )))
    }

    // Either order: `abs(x) = x or abs(x) = (-x)`. Pure shape match.
    // Example: after `have x R`, prove `abs(x) = x or abs(x) = (-x)`.
    fn search_or_abs_sign_split(
        &mut self,
        fact: &OrFact,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(first)),
            AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(second)),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        let Some(arg) = match_abs_sign_split_arg(first, second) else {
            return Ok(None);
        };
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::AbsSignSplit(OrBuiltinAbsSignSplit { arg }),
        )))
    }

    // Either order: `a = 0 or b = 0` when `a * b = 0` known and both `$in R`.
    // Example: after `have a, b R` and `trust a * b = 0`, prove `a = 0 or b = 0`.
    fn search_or_zero_product_split(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(first)),
            AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(second)),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        let Some(left) = zero_factor_from_equal(first) else {
            return Ok(None);
        };
        let Some(right) = zero_factor_from_equal(second) else {
            return Ok(None);
        };
        let left = left.clone();
        let right = right.clone();
        let Some((left_in_r, right_in_r)) =
            self.prove_both_objs_in_r(&left, &right, verify_state.clone())?
        else {
            return Ok(None);
        };
        let Some(product_zero) = self.prove_product_is_zero(&left, &right, verify_state)? else {
            return Ok(None);
        };
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::ZeroProductSplit(OrBuiltinZeroProductSplit {
                left,
                right,
                left_in_r,
                right_in_r,
                product_zero,
            }),
        )))
    }

    // Either order: `a < b or a >= b` after both `$in R`.
    // Example: after `have a, b R`, prove `a < b or a >= b`.
    fn search_or_less_or_greater_equal(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(first),
            AndChainAtomicFact::AtomicFact(second),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        let Some((left, right)) = match_less_or_greater_equal_operands(first, second) else {
            return Ok(None);
        };
        let Some((left_in_r, right_in_r)) =
            self.prove_both_objs_in_r(&left, &right, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::LessOrGreaterEqual(OrBuiltinLessOrGreaterEqual {
                left,
                right,
                left_in_r,
                right_in_r,
            }),
        )))
    }

    // Either order: `a > b or a <= b` after both `$in R`.
    // Example: after `have a, b R`, prove `a > b or a <= b`.
    fn search_or_greater_or_less_equal(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(first),
            AndChainAtomicFact::AtomicFact(second),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        let Some((left, right)) = match_greater_or_less_equal_operands(first, second) else {
            return Ok(None);
        };
        let Some((left_in_r, right_in_r)) =
            self.prove_both_objs_in_r(&left, &right, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::GreaterOrLessEqual(OrBuiltinGreaterOrLessEqual {
                left,
                right,
                left_in_r,
                right_in_r,
            }),
        )))
    }

    // Either order: `a <= b or a >= b` after both `$in R`.
    // Example: after `have a, b R`, prove `a <= b or a >= b`.
    fn search_or_weak_order_le_or_ge(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(first),
            AndChainAtomicFact::AtomicFact(second),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        let Some((left, right)) = match_weak_order_le_or_ge_operands(first, second) else {
            return Ok(None);
        };
        let Some((left_in_r, right_in_r)) =
            self.prove_both_objs_in_r(&left, &right, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::WeakOrderLeOrGe(OrBuiltinWeakOrderLeOrGe {
                left,
                right,
                left_in_r,
                right_in_r,
            }),
        )))
    }

    // Either order: `a = b or a < b` when `a <= b` known (dual with > / >=).
    // Example: after `have a, b R` and `trust a <= b`, prove `a = b or a < b`.
    fn search_or_equality_plus_strict_covers_weak(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(first),
            AndChainAtomicFact::AtomicFact(second),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        let Some((left, right, mut weak_template)) =
            match_equality_plus_strict_covers_weak(first, second)
        else {
            return Ok(None);
        };
        // Fresh FactId for the weak-bound verification goal.
        match &mut weak_template {
            AtomicFact::LessEqualFact(f) => f.fact_id = self.global_ids.allocate_fact_id(),
            AtomicFact::GreaterEqualFact(f) => f.fact_id = self.global_ids.allocate_fact_id(),
            _ => {}
        }
        let weak_bound = self.verify_fact(&Fact::AtomicFact(weak_template), verify_state)?;
        if weak_bound.is_failed() {
            return Ok(None);
        }
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::EqualityPlusStrictCoversWeak(
                OrBuiltinEqualityPlusStrictCoversWeak {
                    left,
                    right,
                    weak_bound,
                },
            ),
        )))
    }

    // Pure shape: exhaustive residues mod positive literal m.
    // Example: after `have n Z`, prove `n % 2 = 0 or n % 2 = 1`.
    fn search_or_complete_residues(
        &mut self,
        fact: &OrFact,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let Some((subject, modulus)) = match_complete_residues(&fact.facts) else {
            return Ok(None);
        };
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::CompleteResidues(OrBuiltinCompleteResidues {
                subject,
                modulus,
            }),
        )))
    }

    // Finite successors plus strict tail from known `x, base $in Z` and `x >= base`.
    // Example: after `have x Z` and `trust x >= 1`, prove `x = 1 or x = 2 or x = 3 or x > 3`.
    fn search_or_integer_successor_tail(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let Some((subject, base)) = match_integer_successor_tail(&fact.facts) else {
            return Ok(None);
        };
        let Some((subject_in_z, base_in_z)) =
            self.prove_both_objs_in_z(&subject, &base, verify_state.clone())?
        else {
            return Ok(None);
        };
        let ge = Fact::AtomicFact(AtomicFact::GreaterEqualFact(GreaterEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: subject.clone(),
            right: base.clone(),
            line_file: fact.line_file.clone(),
        }));
        let subject_ge_base = self.verify_fact(&ge, verify_state)?;
        if subject_ge_base.is_failed() {
            return Ok(None);
        }
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::IntegerSuccessorTail(OrBuiltinIntegerSuccessorTail {
                subject,
                base,
                subject_in_z,
                base_in_z,
                subject_ge_base,
            }),
        )))
    }

    // Either order: `a != 0 or b != 0` from known square-sum nonzero.
    // Example: after `have a, b R` and `trust a^2 + b^2 != 0`, prove `a != 0 or b != 0`.
    fn search_or_square_sum_component_nonzero(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(first),
            AndChainAtomicFact::AtomicFact(second),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        let Some((left, right)) = match_component_nonzero_pair(first, second) else {
            return Ok(None);
        };
        for mut candidate in square_sum_nonzero_candidates(&left, &right) {
            if let AtomicFact::NotEqualFact(f) = &mut candidate {
                f.fact_id = self.global_ids.allocate_fact_id();
            }
            let square_sum_nonzero =
                self.verify_fact(&Fact::AtomicFact(candidate), verify_state.clone())?;
            if !square_sum_nonzero.is_failed() {
                return Ok(Some(OrFactSearchedProof::ByBuiltinRule(
                    OrFactSearchProofByBuiltinRule::SquareSumComponentNonzero(
                        OrBuiltinSquareSumComponentNonzero {
                            left,
                            right,
                            square_sum_nonzero,
                        },
                    ),
                )));
            }
        }
        Ok(None)
    }

    // Either order: `x <= n or x >= n + 1` (or predecessor dual) after both `$in Z`.
    // Example: after `have x, n Z`, prove `x <= n or x >= n + 1`.
    fn search_or_integer_discrete_split(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(first),
            AndChainAtomicFact::AtomicFact(second),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        let Some((subject, base)) = match_integer_discrete_split(first, second) else {
            return Ok(None);
        };
        let Some((subject_in_z, base_in_z)) =
            self.prove_both_objs_in_z(&subject, &base, verify_state)?
        else {
            return Ok(None);
        };
        Ok(Some(OrFactSearchedProof::ByBuiltinRule(
            OrFactSearchProofByBuiltinRule::IntegerDiscreteSplit(OrBuiltinIntegerDiscreteSplit {
                subject,
                base,
                subject_in_z,
                base_in_z,
            }),
        )))
    }

    // Packaging `not A or B` (exactly one negative-polarity branch): assume A, prove B.
    // Example: after a known forall implication, prove `not $p(a) or $q(a)`.
    fn search_or_classical_implication(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let (
            AndChainAtomicFact::AtomicFact(first),
            AndChainAtomicFact::AtomicFact(second),
        ) = (&fact.facts[0], &fact.facts[1])
        else {
            return Ok(None);
        };
        let first_neg = !atomic_fact_has_positive_polarity(first);
        let second_neg = !atomic_fact_has_positive_polarity(second);
        // Require the classical packaging surface `not A or B` (exactly one negative arm).
        if first_neg == second_neg {
            return Ok(None);
        }
        for (assumed_from_branch_index, conclusion_branch_index) in [(0usize, 1usize), (1, 0)] {
            let assumed_from = if assumed_from_branch_index == 0 {
                first
            } else {
                second
            };
            // Prefer assuming the negation of the negative arm (recover A from not A).
            if atomic_fact_has_positive_polarity(assumed_from) {
                continue;
            }
            let Some(assumed_atomic) =
                negate_atomic_fact(assumed_from, self.global_ids.allocate_fact_id())
            else {
                continue;
            };
            let (attempt, local_env) = self.run_in_local_env_and_take_env(|rt| {
                let well_defined =
                    match rt.wrap_atomic_fact_wd(&assumed_atomic, verify_state.clone())? {
                        VerifyFactWellDefinedResult::Success(proof) => proof,
                        VerifyFactWellDefinedResult::Failed(_) => return Ok(None),
                    };
                let assumed_premise = Fact::AtomicFact(assumed_atomic.clone());
                let assumed_store_and_infer: StoreFactAndInferResult =
                    rt.store_fact_and_infer(&assumed_premise)?;
                let conclusion_fact = and_chain_as_fact(&fact.facts[conclusion_branch_index]);
                let conclusion_proof = rt.verify_fact(&conclusion_fact, verify_state.clone())?;
                if conclusion_proof.is_failed() {
                    return Ok(None);
                }
                Ok(Some((
                    assumed_premise,
                    well_defined,
                    assumed_store_and_infer,
                    conclusion_proof,
                )))
            })?;
            if let Some((
                assumed_premise,
                assumed_well_defined,
                assumed_store_and_infer,
                conclusion_proof,
            )) = attempt
            {
                return Ok(Some(OrFactSearchedProof::ByBuiltinRule(
                    OrFactSearchProofByBuiltinRule::ClassicalImplication(
                        OrBuiltinClassicalImplication {
                            assumed_from_branch_index,
                            conclusion_branch_index,
                            assumed_premise,
                            assumed_well_defined,
                            assumed_store_and_infer,
                            conclusion_proof,
                            local_env,
                        },
                    ),
                )));
            }
        }
        Ok(None)
    }
}

