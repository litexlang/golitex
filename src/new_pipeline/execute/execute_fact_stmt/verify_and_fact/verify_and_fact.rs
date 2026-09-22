use crate::new_pipeline::ast::fact::{AndFact, Fact, atomic_fact_args_ref};
use crate::new_pipeline::exec_env::forall_conclusion_index_key::and_forall_conclusion_index_key;
use crate::new_pipeline::exec_env::known_forall_conclusion_memory::and_at_forall_location;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::match_forall_conclusion_args::subst_from_ordered_params;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_and_fact::result::{
    and_fact_result_from_component_fail, and_fact_result_from_success,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Prove and by proving each atomic component.
    // Example: `1 < 2 and 2 < 3` requires proofs of `1 < 2` and `2 < 3`.
    pub fn verify_and_fact(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let known_forall = self.search_and_fact_by_known_forall(fact, verify_state.clone())?;
        let mut components = Vec::with_capacity(fact.facts.len());
        for (failed_index, atomic) in fact.facts.iter().enumerate() {
            let component = self.verify_atomic_fact(atomic, verify_state.clone())?;
            if component.is_failed() {
                return Ok(and_fact_result_from_component_fail(
                    fact,
                    failed_index,
                    components,
                    component,
                ));
            }
            components.push(component);
        }
        Ok(and_fact_result_from_success(fact, components, known_forall))
    }

    fn search_and_fact_by_known_forall(&mut self, goal: &AndFact, verify_state: VerifyState) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        if !verify_state.can_use_forall_fact { return Ok(None); }
        let key = and_forall_conclusion_index_key(goal);
        let mut cites = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(entries) = env.facts.known_forall_conclusions.by_and.get(&key) { cites.extend(entries.iter().cloned()); }
        }
        for cite in cites {
            let Some(forall) = self.fact_by_id_in_stack(cite.fact_id).and_then(|f| match f { Fact::ForallFact(x) => Some(x.clone()), _ => None }) else { continue; };
            let Some(conclusion) = and_at_forall_location(&forall, &cite.location) else { continue; };
            let conclusion_args: Vec<&crate::new_pipeline::ast::obj::Obj> = conclusion.facts.iter().flat_map(atomic_fact_args_ref).collect();
            let goal_args: Vec<&crate::new_pipeline::ast::obj::Obj> = goal.facts.iter().flat_map(atomic_fact_args_ref).collect();
            let params = forall.typed_parameters.ordered_param_ids();
            let Some(matched) = self.match_forall_conclusion_args(&conclusion_args, &goal_args, &params)? else { continue; };
            let subst = subst_from_ordered_params(&params, &matched.forall_parameters_match_what_args);
            let Some(req) = self.prove_forall_instantiation_requirements(&forall, &subst, verify_state.clone())? else { continue; };
            return Ok(Some(SearchProofByKnownForallFact { cite, forall_parameters_match_what_args: matched.forall_parameters_match_what_args, arg_match_proofs: matched.arg_match_proofs, instantiation_requirements: req }));
        }
        Ok(None)
    }

}
