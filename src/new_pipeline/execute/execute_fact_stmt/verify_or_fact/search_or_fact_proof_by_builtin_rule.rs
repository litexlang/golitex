use crate::new_pipeline::ast::fact::{AndChainAtomicFact, AtomicFact, InFact, OrFact};
use crate::new_pipeline::ast::obj::{Number, Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::helper::{
    equal_matches_pair, objs_same,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::result::{
    OrBuiltinNaturalZeroOrAtLeastOne, OrBuiltinRealLineTrichotomyEqLessGreater,
    OrBuiltinRealLineTrichotomyGreaterEqLess, OrBuiltinRealLineTrichotomyLessEqGreater,
    OrFactSearchProofByBuiltinRule, OrFactSearchedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Or builtin search: three rigid real-line trichotomy branch orders,
    // plus natural `= 0 or >= 1`.
    pub(crate) fn search_or_fact_proof_by_builtin_rule(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        if fact.facts.len() == 2 {
            if let Some(proof) =
                self.search_or_natural_zero_or_at_least_one(fact, verify_state.clone())?
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
            fact_id: self.ids.allocate_fact_id(),
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
}

fn is_number_obj(obj: &Obj, value: &str) -> bool {
    matches!(
        obj,
        Obj::Number(Number {
            normalized_value,
        }) if normalized_value == value
    )
}
