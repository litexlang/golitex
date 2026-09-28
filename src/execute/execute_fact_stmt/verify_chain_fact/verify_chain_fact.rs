use crate::ast::fact::{ChainFact, Fact};
use crate::exec_env::forall_conclusion_index_key::chain_forall_conclusion_index_key;
use crate::exec_env::known_forall_conclusion_memory::chain_at_forall_location;
use crate::execute::execute_fact_stmt::verify_atomic_fact::match_forall_conclusion_args::subst_from_ordered_params;
use crate::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_chain_fact::result::{
    chain_fact_result_from_adjacent_fail, chain_fact_result_from_success,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Prove chain by proving each adjacent atomic edge.
    // Example: `1 < 2 < 3` requires proofs of `1 < 2` and `2 < 3`.
    pub fn verify_chain_fact(
        &mut self,
        fact: &ChainFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        // `chain/adjacent_order.lit` uses the structural whole-chain key;
        // atomic edge verification remains the fallback for ordinary chains.
        let known_forall = self.search_chain_fact_by_known_forall(fact, verify_state.clone())?;
        if let Some(proof) = known_forall {
            return Ok(chain_fact_result_from_success(fact, Vec::new(), Some(proof)));
        }
        let adjacent_atomics = self.chain_adjacent_atomics(fact)?;
        let mut adjacent = Vec::with_capacity(adjacent_atomics.len());
        for (failed_index, atomic) in adjacent_atomics.iter().enumerate() {
            let step = self.verify_atomic_fact(atomic, verify_state.clone())?;
            if step.is_failed() {
                return Ok(chain_fact_result_from_adjacent_fail(
                    fact,
                    failed_index,
                    adjacent,
                    step,
                ));
            }
            adjacent.push(step);
        }
        Ok(chain_fact_result_from_success(fact, adjacent, known_forall))
    }

    fn search_chain_fact_by_known_forall(&mut self, goal: &ChainFact, verify_state: VerifyState) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        if !verify_state.can_use_forall_fact { return Ok(None); }
        let key = chain_forall_conclusion_index_key(goal);
        let mut cites = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(entries) = env.facts.known_forall_conclusions.by_chain.get(&key) { cites.extend(entries.iter().cloned()); }
        }

        for cite in cites {
            let Some(forall) = self.fact_by_id_in_stack(cite.fact_id).and_then(|f| match f { Fact::ForallFact(x) => Some(x.clone()), _ => None }) else { continue; };
            let Some(conclusion) = chain_at_forall_location(&forall, &cite.location) else { continue; };
            let params = forall.typed_parameters.ordered_param_ids();
            let conclusion_args: Vec<&crate::ast::obj::Obj> = conclusion.objs.iter().collect();
            let goal_args: Vec<&crate::ast::obj::Obj> = goal.objs.iter().collect();
            let Some(matched) = self.match_forall_conclusion_args(&conclusion_args, &goal_args, &params)? else { continue; };
            let subst = subst_from_ordered_params(&params, &matched.forall_parameters_match_what_args);
            let Some(req) = self.prove_forall_instantiation_requirements(&forall, &subst, verify_state.clone())? else { continue; };
            return Ok(Some(SearchProofByKnownForallFact { cite, forall_parameters_match_what_args: matched.forall_parameters_match_what_args, arg_match_proofs: matched.arg_match_proofs, instantiation_requirements: req }));
        }
        Ok(None)
    }

}
