//! Non-equality atomic → user-defined known strategy.
//!
//! Stage sits after by-definition and before known forall.
//! Source: `strategy_definitions` on the ExecEnv stack (not ambient known_forall).
//!
//! Apply pipeline for one strategy then-clause (soft miss → continue):
//! 1. then must be a direct AtomicFact with matching prop / polarity
//! 2. `match_forall_conclusion_args`
//! 3. `prove_forall_instantiation_requirements`
//!
//! Example:
//!   strategy use_is_one: ? forall x R: x = 1 =>: $is_one(x)
//!   goal `$is_one(a)` with `a = 1` known
//!   → ByKnownStrategy { strategy_name: use_is_one, then_index: 0, … }

use crate::new_pipeline::ast::fact::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity, AtomicFact, ExistOrAndChainAtomicFact,
    ForallFact,
};
use crate::new_pipeline::ast::names::PlainName;
use crate::new_pipeline::ast::stmt::DefStrategyStmt;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::match_forall_conclusion_args::subst_from_ordered_params;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::SearchProofByKnownStrategy;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_known_strategy(
        &mut self,
        goal: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownStrategy>> {
        if !verify_state.can_use_forall_fact {
            return Ok(None);
        }
        let candidates = self.visible_strategy_definitions();
        for (name, stmt) in candidates {
            if let Some(proof) =
                self.try_apply_known_strategy(goal, &name, &stmt.forall_fact, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    fn visible_strategy_definitions(&self) -> Vec<(PlainName, DefStrategyStmt)> {
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            for (name, stmt) in env.definitions.strategy_definitions.iter() {
                out.push((name.clone(), stmt.clone()));
            }
        }
        out
    }

    fn try_apply_known_strategy(
        &mut self,
        goal: &AtomicFact,
        strategy_name: &PlainName,
        forall: &ForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownStrategy>> {
        for (then_index, then) in forall.then_facts.iter().enumerate() {
            let ExistOrAndChainAtomicFact::AtomicFact(conclusion) = then else {
                continue;
            };
            // Equality conclusions belong to the equality search path, not here.
            if matches!(conclusion, AtomicFact::EqualFact(_)) {
                continue;
            }
            if conclusion.prop_name() != goal.prop_name()
                || atomic_fact_has_positive_polarity(conclusion)
                    != atomic_fact_has_positive_polarity(goal)
            {
                continue;
            }

            let param_ids = forall.typed_parameters.ordered_param_ids();
            let conclusion_args = atomic_fact_args_ref(conclusion);
            let goal_args = atomic_fact_args_ref(goal);

            let Some(matched) =
                self.match_forall_conclusion_args(&conclusion_args, &goal_args, &param_ids)?
            else {
                continue;
            };

            let subst =
                subst_from_ordered_params(&param_ids, &matched.forall_parameters_match_what_args);
            let Some(instantiation_requirements) =
                self.prove_forall_instantiation_requirements(forall, &subst, verify_state.clone())?
            else {
                continue;
            };

            return Ok(Some(SearchProofByKnownStrategy {
                strategy_name: strategy_name.clone(),
                then_index,
                forall_parameters_match_what_args: matched.forall_parameters_match_what_args,
                arg_match_proofs: matched.arg_match_proofs,
                instantiation_requirements,
            }));
        }
        Ok(None)
    }
}
