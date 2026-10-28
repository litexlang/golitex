use crate::ast::fact::{atomic_fact_args_ref, AndFact, Fact};
use crate::exec_env::forall_conclusion_index_key::and_forall_conclusion_index_key;
use crate::exec_env::known_forall_conclusion_memory::and_at_forall_location;
use crate::execute::execute_fact_stmt::verify_and_fact::result::{
    and_fact_result_from_component_fail, and_fact_result_from_success,
};
use crate::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Prove and by proving each atomic component.
    // Example: `1 < 2 and 2 < 3` requires proofs of `1 < 2` and `2 < 3`.
    pub fn verify_and_fact(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        // Whole-and forall cite still requires each conjunct to be WD first.
        // Example: after `trust forall x R: abs(x)=x and x=x`, `abs(a)=a and a=a`
        // needs `abs(a)` WD even when the structural and key matches.
        let mut known_forall = self.search_and_fact_by_known_forall(fact, verify_state.clone())?;
        if let Some(proof) = known_forall.take() {
            if matches!(
                self.verify_and_fact_well_definedness(fact, verify_state.clone())?,
                VerifyAndFactWellDefinedResult::Success(_)
            ) {
                return Ok(and_fact_result_from_success(fact, Vec::new(), Some(proof)));
            }
            // WD failed: fall through so the Failed shape matches conjunct WD misses.
        }
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
        Ok(and_fact_result_from_success(fact, components, None))
    }

    fn search_and_fact_by_known_forall(
        &mut self,
        goal: &AndFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        if !verify_state
            .allows(crate::execute::execute_fact_stmt::VerifyStateLevel::DefinitionAndForall)
        {
            return Ok(None);
        }
        let premise_state = verify_state
            .capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule);
        let key = and_forall_conclusion_index_key(goal);
        let mut cites = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(entries) = env.facts.known_forall_conclusions.by_and.get(&key) {
                cites.extend(entries.iter().cloned());
            }
        }
        for cite in cites {
            let Some(forall) = self
                .fact_by_id_in_stack(cite.fact_id)
                .and_then(|f| match f {
                    Fact::ForallFact(x) => Some(x.clone()),
                    _ => None,
                })
            else {
                continue;
            };
            let Some(conclusion) = and_at_forall_location(&forall, &cite.location) else {
                continue;
            };
            let conclusion_args: Vec<&crate::ast::obj::Obj> = conclusion
                .facts
                .iter()
                .flat_map(atomic_fact_args_ref)
                .collect();
            let goal_args: Vec<&crate::ast::obj::Obj> =
                goal.facts.iter().flat_map(atomic_fact_args_ref).collect();
            let params = forall.typed_parameters.ordered_param_ids();
            let Some(matched) =
                self.match_forall_conclusion_args(&conclusion_args, &goal_args, &params)?
            else {
                continue;
            };
            let (subst, forall_parameters_match_what_args, arg_match_proofs) =
                matched.into_parts(self.result_detail())?;
            let Some(req) = self.prove_forall_instantiation_requirements(
                &forall,
                &subst,
                premise_state.clone(),
            )?
            else {
                continue;
            };
            return Ok(Some(SearchProofByKnownForallFact::from_children(
                self.result_detail(),
                cite,
                &forall,
                forall_parameters_match_what_args,
                arg_match_proofs,
                req,
            )?));
        }
        Ok(None)
    }
}
