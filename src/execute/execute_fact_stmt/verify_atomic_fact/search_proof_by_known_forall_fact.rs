//! Apply a stored forall's atomic then (or and-component leaf) to a goal atomic.
//!
//! Shared by equality and non-equality atomics. Non-equality entry is
//! `search_atomic_except_equality_fact_proof_by_known_forall_fact`.
//!
//! Pipeline for one cite (soft miss → Ok(None)):
//! 1. Load the forall and the atomic conclusion at `cite.location`
//! 2. Require same prop name and polarity as the goal
//! 3. `match_forall_conclusion_args_to_subst` — bind bare params from conclusion
//! 3b. `complete_forall_subst_from_dom_facts` — bind params that appear only in dom
//! 4. `prove_forall_instantiation_requirements` — param-type facts, then dom
//!
//! Example (non-equality):
//!   known `forall a R: a > 0 => a + 1 > 1`
//!   goal  `3 + 1 > 1`
//!   → match binds/equals args, prove `3 $in R` and `3 > 0`, done.
//! Example (dom-only middle):
//!   known `forall x,y,z S: $leq(x,y), $leq(y,z) => $leq(x,z)`
//!   goal  `$leq(a,c)` with known `$leq(a,b)`, `$leq(b,c)`
//!   → conclusion binds `x,z`; dom completion binds `y`.

use super::match_forall_conclusion_args::ForallMatchEqualityContext;
use crate::ast::fact::{atomic_fact_args_ref, atomic_fact_has_positive_polarity};
use crate::ast::fact::{AtomicFact, Fact, ForallConclusionLocation};
use crate::exec_env::forall_equality_index::EqualityIndexQuery;
use crate::exec_env::known_forall_conclusion_memory::{
    atomic_at_forall_location, ForallConclusionCite,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{FactId, Runtime, RuntimeResult};

impl Runtime {
    // Search known-forall atomic conclusions that can prove `goal`.
    // Candidates come from by_equal or by_atomic_prop; first success wins.
    pub fn search_atomic_fact_proof_by_known_forall_fact(
        &mut self,
        goal: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        let candidates = self.visible_forall_atomic_conclusion_candidates(goal);
        let mut equality = ForallMatchEqualityContext::default();
        for cite in candidates {
            if let Some(proof) = self.try_apply_forall_conclusion_cite(
                goal,
                &cite,
                verify_state.clone(),
                &mut equality,
            )? {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    // Collect cites from the execution-environment stack (inner env first).
    // `=` goals query the constructor index; other atomics key by (prop, polarity).
    pub(crate) fn visible_forall_atomic_conclusion_candidates(
        &self,
        goal: &AtomicFact,
    ) -> Vec<ForallConclusionCite> {
        let mut out = Vec::new();
        let mut equality_query = None;
        for env in self.execution_environments_stack.iter().rev() {
            match goal {
                AtomicFact::EqualFact(equal) => {
                    let query = equality_query.get_or_insert_with(|| {
                        EqualityIndexQuery::new(
                            self.execution_environments_stack
                                .iter()
                                .rev()
                                .map(|env| &env.facts.known_equivalence_classes.generating_edges)
                                .collect(),
                        )
                    });
                    out.extend(
                        env.facts
                            .known_forall_conclusions
                            .by_equal
                            .candidates(equal, query),
                    );
                }
                _ => {
                    let key = (goal.prop_name(), atomic_fact_has_positive_polarity(goal));
                    if let Some(entries) =
                        env.facts.known_forall_conclusions.by_atomic_prop.get(&key)
                    {
                        out.extend(entries.iter().cloned());
                    }
                }
            }
        }
        out
    }

    // Try one ForallConclusionCite against `goal`. Stages 1–4 in the file header.
    fn try_apply_forall_conclusion_cite(
        &mut self,
        goal: &AtomicFact,
        cite: &ForallConclusionCite,
        verify_state: VerifyState,
        equality: &mut ForallMatchEqualityContext,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        // Stage 1: resolve forall + atomic conclusion at the cite location.
        let forall = match self.fact_by_id_in_stack(cite.fact_id) {
            Some(Fact::ForallFact(f)) => f.clone(),
            _ => return Ok(None),
        };
        let conclusion = match atomic_at_forall_location(&forall, &cite.location) {
            Some(conclusion) => conclusion,
            None => {
                let ForallConclusionLocation::ChainFactComponent(loc) = &cite.location else {
                    return Ok(None);
                };
                let Some(crate::ast::fact::ExistOrAndChainAtomicFact::ChainFact(chain)) =
                    forall.then_facts.get(loc.then_fact_index)
                else {
                    return Ok(None);
                };
                let (Some(left), Some(right), Some(prop)) = (
                    chain.objs.get(loc.component_index),
                    chain.objs.get(loc.component_index + 1),
                    chain.prop_names.get(loc.component_index),
                ) else {
                    return Ok(None);
                };
                self.atomic_from_prop(
                    prop.clone(),
                    vec![left.clone(), right.clone()],
                    true,
                    chain.line_file.clone().unwrap_or_else(|| {
                        crate::ast::line_file::SourceLine::new(0, crate::runtime::CodeSource::Eval)
                    }),
                )?
            }
        };

        // Stage 2: prop name and polarity must match before matching args.
        if conclusion.prop_name() != goal.prop_name()
            || atomic_fact_has_positive_polarity(&conclusion)
                != atomic_fact_has_positive_polarity(goal)
        {
            return Ok(None);
        }

        let param_ids = forall.typed_parameters.ordered_param_ids();
        let conclusion_args = atomic_fact_args_ref(&conclusion);
        let goal_args = atomic_fact_args_ref(goal);

        // Stage 3: match conclusion args (may leave dom-only params unbound).
        let Some((mut subst, arg_match_proofs)) = self.match_forall_conclusion_args_with_equality(
            &conclusion_args,
            &goal_args,
            &param_ids,
            equality,
        )?
        else {
            return Ok(None);
        };

        // Stage 3b: bind params that appear only in dom facts.
        if !self.complete_forall_subst_with_equality(&forall, &mut subst, &param_ids, equality)? {
            return Ok(None);
        }

        let forall_parameters_match_what_args: Vec<_> = param_ids
            .iter()
            .map(|id| subst.get(id).expect("dom completion").clone())
            .collect();

        // Requirements can run broader verification. Do not reuse a stale
        // read-only matching snapshot if this candidate fails there.
        *equality = ForallMatchEqualityContext::default();
        // Stage 4: param-type obligations, then dom facts (shared helper).
        let Some(instantiation_requirements) =
            self.prove_forall_instantiation_requirements(&forall, &subst, verify_state)?
        else {
            return Ok(None);
        };

        Ok(Some(SearchProofByKnownForallFact {
            cite: cite.clone(),
            forall_parameters_match_what_args,
            arg_match_proofs,
            instantiation_requirements,
        }))
    }

    pub(crate) fn fact_by_id_in_stack(&self, fact_id: FactId) -> Option<&Fact> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(fact) = env.facts.facts_by_id.get(&fact_id) {
                return Some(fact);
            }
        }
        None
    }
}
