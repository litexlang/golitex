use crate::new_pipeline::ast::fact::{AndChainAtomicFact, AtomicFact, OrFact};
use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::helper::{
    equal_matches_pair, objs_same,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::result::{
    OrBuiltinRealLineTrichotomyEqLessGreater, OrBuiltinRealLineTrichotomyGreaterEqLess,
    OrBuiltinRealLineTrichotomyLessEqGreater, OrFactSearchProofByBuiltinRule, OrFactSearchedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Or builtin search: three rigid real-line trichotomy branch orders.
    // Example: have a R, b R => a = b or a < b or a > b
    pub(crate) fn search_or_fact_proof_by_builtin_rule(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
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
}
