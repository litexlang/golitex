use crate::ast::fact::{
    and_chain_as_fact, atomic_fact_has_positive_polarity, negate_atomic_fact, or_fact_args_ref,
    AndChainAtomicFact, Fact, OrFact,
};
use crate::exec_env::or_fact_index_key::or_fact_index_key;
use crate::exec_env::known_forall_conclusion_memory::{
    or_at_forall_location, ForallConclusionCite,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::match_forall_conclusion_args::subst_from_ordered_params;
use crate::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_or_fact::result::{
    or_fact_result_from_search_fail, or_fact_result_from_success, or_fact_result_from_wd_fail,
};
use crate::execute::execute_fact_stmt::verify_or_fact::{
    AssumeNegatedOrBranchResult, OrFactSearchProofByKnownOrFact,
    OrFactSearchProofBySelectedBranch, OrFactSearchedProof,
};
use crate::execute::execute_fact_stmt::{
    VerifyFactWellDefinedResult, VerifyOrFactWellDefinedResult, VerifyState,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

impl Runtime {
    // Prove or: WD → builtin → selected branch (¬ others) → known_or → known_forall.
    // Example: known `1 = 1` proves `1 = 1 or 1 = 2` by assuming `not 1 = 2` locally.
    pub fn verify_or_fact(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof =
            match self.verify_or_fact_well_definedness(fact, verify_state.clone())? {
                VerifyOrFactWellDefinedResult::Success(proof) => proof,
                VerifyOrFactWellDefinedResult::Failed(reason) => {
                    return Ok(or_fact_result_from_wd_fail(reason));
                }
            };
        let Some(searched_proof) = self.search_or_fact_proof(fact, verify_state)? else {
            return Ok(or_fact_result_from_search_fail(fact, well_defined_proof));
        };
        Ok(or_fact_result_from_success(
            fact,
            well_defined_proof,
            searched_proof,
        ))
    }

    fn search_or_fact_proof(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        if let Some(proof) =
            self.search_or_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_or_fact_proof_by_selected_branch(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_or_fact_proof_by_known_or_fact(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.search_or_fact_proof_by_known_forall_fact(fact, verify_state)? {
            return Ok(Some(proof));
        }
        Ok(None)
    }

    fn search_or_fact_proof_by_selected_branch(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        for selected_index in 0..fact.facts.len() {
            if !other_branches_are_atomic(fact, selected_index) {
                continue;
            }
            let (attempt, local_env) = self.run_in_local_env_and_take_env(|rt| {
                rt.try_or_selected_branch_in_local(fact, selected_index, verify_state.clone())
            })?;
            if let Some((assumed_negated_branches, selected_branch)) = attempt {
                return Ok(Some(OrFactSearchedProof::BySelectedBranch(
                    OrFactSearchProofBySelectedBranch {
                        selected_index,
                        assumed_negated_branches,
                        selected_branch,
                        local_env,
                    },
                )));
            }
        }
        Ok(None)
    }

    fn try_or_selected_branch_in_local(
        &mut self,
        fact: &OrFact,
        selected_index: usize,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<(Vec<AssumeNegatedOrBranchResult>, VerifyFactResult)>> {
        let mut assumed_negated_branches = Vec::new();
        for (branch_index, branch) in fact.facts.iter().enumerate() {
            if branch_index == selected_index {
                continue;
            }
            let AndChainAtomicFact::AtomicFact(atomic) = branch else {
                return Ok(None);
            };
            let Some(negated_atomic) = negate_atomic_fact(atomic, self.global_ids.allocate_fact_id())
            else {
                return Ok(None);
            };
            let well_defined =
                match self.wrap_atomic_fact_wd(&negated_atomic, verify_state.clone())? {
                    VerifyFactWellDefinedResult::Success(proof) => proof,
                    VerifyFactWellDefinedResult::Failed(_) => return Ok(None),
                };
            let negated_fact = Fact::AtomicFact(negated_atomic);
            let store_and_infer: StoreFactAndInferResult =
                self.store_fact_and_infer(&negated_fact)?;
            assumed_negated_branches.push(AssumeNegatedOrBranchResult {
                branch_index,
                negated_fact,
                well_defined,
                store_and_infer,
            });
        }

        let selected_fact = and_chain_as_fact(&fact.facts[selected_index]);
        let selected_branch = self.verify_fact(&selected_fact, verify_state)?;
        if selected_branch.is_failed() {
            return Ok(None);
        }
        Ok(Some((assumed_negated_branches, selected_branch)))
    }

    fn search_or_fact_proof_by_known_or_fact(
        &mut self,
        fact: &OrFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        let lookup_key = or_fact_index_key(fact);
        let goal_args = or_fact_args_ref(fact);
        let class_per_arg: Vec<Vec<_>> = goal_args
            .iter()
            .map(|arg| self.equivalence_class_keys(arg))
            .collect();

        for env in self.execution_environments_stack.iter().rev() {
            let Some(knowns) = env.facts.known_or.by_key.get(&lookup_key) else {
                continue;
            };
            for known in knowns {
                if !or_facts_same_shape(known, fact) {
                    continue;
                }
                let known_args = or_fact_args_ref(known);
                if known_args.len() != goal_args.len() {
                    continue;
                }
                let args_match = known_args
                    .iter()
                    .zip(class_per_arg.iter())
                    .all(|(known_arg, class)| class.contains(&known_arg.ir()));
                if args_match {
                    return Ok(Some(OrFactSearchedProof::ByKnownOrFact(
                        OrFactSearchProofByKnownOrFact {
                            cite_fact_id: known.fact_id,
                        },
                    )));
                }
            }
        }
        Ok(None)
    }

    fn search_or_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<OrFactSearchedProof>> {
        if !verify_state.can_use_def_and_known_forall_and_known_strategy
            || verify_state.remaining_deep_search_depth == 0
        {
            return Ok(None);
        }
        let premise_state = verify_state.after_deep_search();
        let lookup_key = or_fact_index_key(fact);
        let mut candidates = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(entries) = env.facts.known_forall_conclusions.by_or.get(&lookup_key) {
                candidates.extend(entries.iter().cloned());
            }
        }
        for cite in candidates {
            if let Some(proof) =
                self.try_apply_forall_or_conclusion_cite(fact, &cite, premise_state.clone())?
            {
                return Ok(Some(OrFactSearchedProof::ByKnownForallFact(proof)));
            }
        }
        Ok(None)
    }

    fn try_apply_forall_or_conclusion_cite(
        &mut self,
        goal: &OrFact,
        cite: &ForallConclusionCite,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        let forall = {
            let mut found = None;
            for env in self.execution_environments_stack.iter().rev() {
                if let Some(Fact::ForallFact(f)) = env.facts.facts_by_id.get(&cite.fact_id) {
                    found = Some(f.clone());
                    break;
                }
            }
            match found {
                Some(f) => f,
                None => return Ok(None),
            }
        };
        let Some(conclusion) = or_at_forall_location(&forall, &cite.location) else {
            return Ok(None);
        };
        if or_fact_index_key(&conclusion) != or_fact_index_key(goal)
            || !or_facts_same_shape(&conclusion, goal)
        {
            return Ok(None);
        }

        // Step 1: list forall params in declaration order.
        let param_ids = forall.typed_parameters.ordered_param_ids();
        let conclusion_args = or_fact_args_ref(&conclusion);
        let goal_args = or_fact_args_ref(goal);

        // Step 2–3: bind params / strict-equal non-params; every param must be bound.
        let Some(matched) =
            self.match_forall_conclusion_args(&conclusion_args, &goal_args, &param_ids)?
        else {
            return Ok(None);
        };
        let subst =
            subst_from_ordered_params(&param_ids, &matched.forall_parameters_match_what_args);

        // Step 4: prove param-type obligations, then dom facts.
        let Some(instantiation_requirements) =
            self.prove_forall_instantiation_requirements(&forall, &subst, verify_state)?
        else {
            return Ok(None);
        };

        Ok(Some(SearchProofByKnownForallFact {
            cite: cite.clone(),
            forall_parameters_match_what_args: matched.forall_parameters_match_what_args,
            arg_match_proofs: matched.arg_match_proofs,
            instantiation_requirements,
        }))
    }
}

fn other_branches_are_atomic(fact: &OrFact, selected_index: usize) -> bool {
    fact.facts.iter().enumerate().all(|(i, branch)| {
        i == selected_index || matches!(branch, AndChainAtomicFact::AtomicFact(_))
    })
}

fn or_facts_same_shape(left: &OrFact, right: &OrFact) -> bool {
    if left.facts.len() != right.facts.len() {
        return false;
    }
    left.facts
        .iter()
        .zip(right.facts.iter())
        .all(|(a, b)| match (a, b) {
            (AndChainAtomicFact::AtomicFact(x), AndChainAtomicFact::AtomicFact(y)) => {
                x.prop_name() == y.prop_name()
                    && atomic_fact_has_positive_polarity(x) == atomic_fact_has_positive_polarity(y)
            }
            (AndChainAtomicFact::AndFact(x), AndChainAtomicFact::AndFact(y)) => {
                x.facts.len() == y.facts.len()
                    && x.facts.iter().zip(y.facts.iter()).all(|(xa, ya)| {
                        xa.prop_name() == ya.prop_name()
                            && atomic_fact_has_positive_polarity(xa)
                                == atomic_fact_has_positive_polarity(ya)
                    })
            }
            (AndChainAtomicFact::ChainFact(x), AndChainAtomicFact::ChainFact(y)) => {
                x.prop_names == y.prop_names && x.objs.len() == y.objs.len()
            }
            _ => false,
        })
}
