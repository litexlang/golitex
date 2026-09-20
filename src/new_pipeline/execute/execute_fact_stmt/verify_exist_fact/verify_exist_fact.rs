use crate::new_pipeline::ast::fact::{exist_fact_family_from_fact, exist_fact_family_to_fact, 
    exist_fact_family_free_args_ref, exist_fact_family_id, ExistFactFamily, Fact, InFact,
};
use crate::new_pipeline::ast::obj::{Obj, StandardSet};
use crate::new_pipeline::exec_env::exist_fact_index_key::{
    exist_fact_alpha_match_key, exist_fact_can_prove_goal, exist_fact_known_lookup_keys,
};
use crate::new_pipeline::exec_env::known_forall_conclusion_memory::{
    exist_at_forall_location, ForallConclusionCite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::match_forall_conclusion_args::subst_from_ordered_params;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_fact::helper::real_line_comparison_free_operands;
use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_fact::result::{
    exist_fact_result_from_search_fail, exist_fact_result_from_success,
    exist_fact_result_from_wd_fail, ExistBuiltinRealLineComparisonWitness,
    ExistFactSearchProofByBuiltinRule, ExistFactSearchProofByKnownExistFact, ExistFactSearchedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyExistFactWellDefinedResult, VerifyState,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Split plain exist / exist! / not exist.
    // Each: WD (Success|Failed, same shape as atomic) → Builtin → known → known_forall.
    // Example (known): stored `exist x N st {x = 1}` proves the same goal.
    // Example (forall): known `forall a N: exist x N st {x = a}` proves `exist x N st {x = 2}`.
    pub fn verify_exist_fact(
        &mut self,
        fact: &ExistFactFamily,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof =
            match self.verify_exist_fact_well_definedness(fact, verify_state.clone())? {
                VerifyExistFactWellDefinedResult::Success(proof) => proof,
                VerifyExistFactWellDefinedResult::Failed(reason) => {
                    return Ok(exist_fact_result_from_wd_fail(fact, reason));
                }
            };
        let Some(searched_proof) = self.search_exist_fact_proof(fact, verify_state)? else {
            return Ok(exist_fact_result_from_search_fail(fact, well_defined_proof));
        };
        Ok(exist_fact_result_from_success(
            fact,
            well_defined_proof,
            searched_proof,
        ))
    }

    // Builtin → known_exist → known_forall.
    fn search_exist_fact_proof(
        &mut self,
        fact: &ExistFactFamily,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistFactSearchedProof>> {
        if let Some(proof) =
            self.search_exist_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(Some(ExistFactSearchedProof::ByBuiltinRule(proof)));
        }
        if let Some(proof) =
            self.search_exist_fact_proof_by_known_exist_fact(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            self.search_exist_fact_proof_by_known_forall_fact(fact, verify_state)?
        {
            return Ok(Some(ExistFactSearchedProof::ByKnownForallFact(proof)));
        }
        Ok(None)
    }

    fn search_exist_fact_proof_by_builtin_rule(
        &mut self,
        fact: &ExistFactFamily,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistFactSearchProofByBuiltinRule>> {
        if let Some(proof) =
            self.search_exist_builtin_real_line_comparison_witness(fact, verify_state)?
        {
            return Ok(Some(
                ExistFactSearchProofByBuiltinRule::RealLineComparisonWitness(proof),
            ));
        }
        Ok(None)
    }

    // Builtin: real-line comparison witness. See ExistBuiltinRealLineComparisonWitness.
    fn search_exist_builtin_real_line_comparison_witness(
        &mut self,
        fact: &ExistFactFamily,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistBuiltinRealLineComparisonWitness>> {
        let Some(free_operands) = real_line_comparison_free_operands(fact) else {
            return Ok(None);
        };
        let line_file = fact.plain().line_file.clone();
        let child_state = verify_state.without_well_defined_storage();
        let mut requirement_facts = Vec::with_capacity(free_operands.len());
        let mut proof_of_requirement_facts = Vec::with_capacity(free_operands.len());
        let mut seen = Vec::new();
        for operand in free_operands {
            let key = operand.display_string();
            if seen.contains(&key) {
                continue;
            }
            seen.push(key);
            let premise: Fact = InFact {
                fact_id: self.ids.allocate_fact_id(),
                element: operand,
                set: Obj::StandardSet(StandardSet::R),
                line_file: line_file.clone(),
            }
            .into();
            let proof = self.verify_fact(&premise, child_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            requirement_facts.push(premise);
            proof_of_requirement_facts.push(proof);
        }
        Ok(Some(ExistBuiltinRealLineComparisonWitness {
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    fn search_exist_fact_proof_by_known_exist_fact(
        &mut self,
        fact: &ExistFactFamily,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistFactSearchedProof>> {
        let goal_id = exist_fact_family_id(fact);
        for key in exist_fact_known_lookup_keys(fact) {
            for env in self.execution_environments_stack.iter().rev() {
                if let Some(entries) = env.facts.known_exist.by_key.get(&key) {
                    for entry in entries {
                        let cite_fact_id = exist_fact_family_id(entry);
                        if cite_fact_id != goal_id {
                            return Ok(Some(ExistFactSearchedProof::ByKnownExistFact(
                                ExistFactSearchProofByKnownExistFact { cite_fact_id },
                            )));
                        }
                    }
                }
            }
        }
        Ok(None)
    }

    // After: SearchProofByKnownForallFact cite.
    fn search_exist_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &ExistFactFamily,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        if !verify_state.can_use_forall_fact {
            return Ok(None);
        }
        for lookup_key in exist_fact_known_lookup_keys(fact) {
            let mut cites = Vec::new();
            for env in self.execution_environments_stack.iter().rev() {
                if let Some(entries) = env.facts.known_forall_conclusions.by_exist.get(&lookup_key)
                {
                    cites.extend(entries.iter().cloned());
                }
            }
            for cite in cites {
                if let Some(proof) =
                    self.try_apply_forall_exist_conclusion_cite(fact, &cite, verify_state.clone())?
                {
                    return Ok(Some(proof));
                }
            }
        }
        Ok(None)
    }

    fn try_apply_forall_exist_conclusion_cite(
        &mut self,
        goal: &ExistFactFamily,
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
        let Some(conclusion) = exist_at_forall_location(&forall, &cite.location) else {
            return Ok(None);
        };
        if !exist_fact_can_prove_goal(&conclusion, goal) {
            return Ok(None);
        }

        // Step 1: list forall params in declaration order.
        let param_ids = forall.typed_parameters.ordered_param_ids();
        let conclusion_args = exist_fact_family_free_args_ref(&conclusion);
        let goal_args = exist_fact_family_free_args_ref(goal);

        // Step 2–3: bind params / strict-equal non-params; every param must be bound.
        // Example: forall a: exist x st {x = a} vs exist x st {x = 2} -> bind a ↦ 2.
        let Some(matched) =
            self.match_forall_conclusion_args(&conclusion_args, &goal_args, &param_ids)?
        else {
            return Ok(None);
        };
        let subst = subst_from_ordered_params(&param_ids, &matched.forall_parameters_match_what_args);

        // Step 4: instantiate the exist conclusion and alpha-compare to the goal.
        let instantiated = match self.inst_fact(&exist_fact_family_to_fact(&conclusion), &subst) {
            Ok(f) => match exist_fact_family_from_fact(&f) {
                Some(e) => e,
                None => return Ok(None),
            },
            Err(_) => return Ok(None),
        };
        if exist_fact_alpha_match_key(&instantiated) != exist_fact_alpha_match_key(goal) {
            return Ok(None);
        }

        // Step 5: prove param-type obligations, then dom facts.
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
