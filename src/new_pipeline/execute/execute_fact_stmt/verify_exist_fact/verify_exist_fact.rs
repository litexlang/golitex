use crate::new_pipeline::ast::fact::{
    exist_fact_free_args_ref, exist_fact_id, EqualFact, ExistFact, Fact, ForallFact,
};
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj};
use crate::new_pipeline::exec_env::exist_fact_index_key::{
    exist_fact_alpha_match_key, exist_fact_can_prove_goal, exist_fact_known_lookup_keys,
};
use crate::new_pipeline::exec_env::known_forall_conclusion_memory::{
    exist_at_forall_location, ForallConclusionCite,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualFactSearchedProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_fact::result::{
    exist_fact_result_from_search_fail, exist_fact_result_from_success,
    exist_fact_result_from_wd_fail, ExistFactSearchProofByKnownExistFact, ExistFactSearchedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyExistFactWellDefinedResult, VerifyState,
};
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::collections::{HashMap, HashSet};

impl Runtime {
    // Split plain exist / exist! / not exist.
    // Each: WD (Success|Failed, same shape as atomic) → Builtin → known → known_forall.
    // Example (known): stored `exist x N st {x = 1}` proves the same goal.
    // Example (forall): known `forall a N: exist x N st {x = a}` proves `exist x N st {x = 2}`.
    pub fn verify_exist_fact(
        &mut self,
        fact: &ExistFact,
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

    // Builtin → known_exist → known_forall. Builtin is scaffold-only for now.
    fn search_exist_fact_proof(
        &mut self,
        fact: &ExistFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistFactSearchedProof>> {
        if let Some(proof) =
            self.search_exist_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(Some(proof));
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
        _fact: &ExistFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistFactSearchedProof>> {
        Ok(None)
    }

    fn search_exist_fact_proof_by_known_exist_fact(
        &mut self,
        fact: &ExistFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ExistFactSearchedProof>> {
        let goal_id = exist_fact_id(fact);
        for key in exist_fact_known_lookup_keys(fact) {
            for env in self.execution_environments_stack.iter().rev() {
                if let Some(entries) = env.facts.known_exist.by_key.get(&key) {
                    for entry in entries {
                        let cite_fact_id = exist_fact_id(entry);
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
        fact: &ExistFact,
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
        goal: &ExistFact,
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
        let param_set: HashSet<IdentifierId> = param_ids.iter().copied().collect();
        let conclusion_args = exist_fact_free_args_ref(&conclusion);
        let goal_args = exist_fact_free_args_ref(goal);
        if conclusion_args.len() != goal_args.len() {
            return Ok(None);
        }

        // Nested equal must not invent proofs via forall / rewrite.
        let equality_state = VerifyState {
            can_use_forall_fact: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };

        // Step 2: match conclusion free args to goal free args.
        // Bind bare forall params; otherwise prove pattern = goal by strict equal.
        // Example: forall a: exist x st {x = a} vs exist x st {x = 2} -> bind a ↦ 2.
        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        let mut proof_of_arg_equalities = Vec::new();
        for (pattern_arg, goal_arg) in conclusion_args.iter().zip(goal_args.iter()) {
            match try_bind_forall_param(pattern_arg, goal_arg, &param_set, &mut subst) {
                ForallParamBindResult::Bound => {}
                ForallParamBindResult::NeedEqual(left, right) => {
                    let Some(eq_proof) =
                        self.prove_objs_equal(&left, &right, equality_state.clone())?
                    else {
                        return Ok(None);
                    };
                    proof_of_arg_equalities.push(eq_proof);
                }
                ForallParamBindResult::NotAParam => {
                    let Some(eq_proof) =
                        self.prove_objs_equal(pattern_arg, goal_arg, equality_state.clone())?
                    else {
                        return Ok(None);
                    };
                    proof_of_arg_equalities.push(eq_proof);
                }
            }
        }
        // Step 3: every forall param must appear in subst (no unused params).
        for id in &param_ids {
            if !subst.contains_key(id) {
                return Ok(None);
            }
        }

        // Step 4: instantiate the exist conclusion and alpha-compare to the goal.
        let instantiated = match self.inst_fact(&Fact::ExistFact(conclusion.clone()), &subst) {
            Ok(Fact::ExistFact(e)) => e,
            Ok(_) | Err(_) => return Ok(None),
        };
        if exist_fact_alpha_match_key(&instantiated) != exist_fact_alpha_match_key(goal) {
            return Ok(None);
        }

        let forall_parameters_match_what_args: Vec<Obj> = param_ids
            .iter()
            .map(|id| subst.get(id).expect("checked").clone())
            .collect();

        // Step 5: instantiate forall dom facts with subst, then verify each.
        let requirement_facts = match self.build_exist_forall_requirement_facts(&forall, &subst)? {
            Some(facts) => facts,
            None => return Ok(None),
        };
        let mut proof_of_requirement_facts = Vec::with_capacity(requirement_facts.len());
        for req in &requirement_facts {
            let proof = self.verify_fact(req, verify_state.clone())?;
            if proof.is_failed() {
                return Ok(None);
            }
            proof_of_requirement_facts.push(proof);
        }

        Ok(Some(SearchProofByKnownForallFact {
            cite: cite.clone(),
            forall_parameters_match_what_args,
            proof_of_arg_equalities,
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    fn build_exist_forall_requirement_facts(
        &mut self,
        forall: &ForallFact,
        subst: &HashMap<IdentifierId, Obj>,
    ) -> RuntimeResult<Option<Vec<Fact>>> {
        let mut requirements = Vec::new();
        for dom in &forall.dom_facts {
            let fact = match self.inst_fact(dom, subst) {
                Ok(fact) => fact,
                Err(_) => return Ok(None),
            };
            requirements.push(fact);
        }
        Ok(Some(requirements))
    }

    // Prove left = right with forall/rewrite off. Reject forall/rewrite certificates.
    fn prove_objs_equal(
        &mut self,
        left: &Obj,
        right: &Obj,
        equality_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        let equal_fact = EqualFact {
            fact_id: self.ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        };
        let Some(proof) = self.search_equal_fact_proof(&equal_fact, equality_state)? else {
            return Ok(None);
        };
        Ok(strict_equal_proof_without_forall_or_rewrite(proof))
    }
}

enum ForallParamBindResult {
    Bound,
    NeedEqual(Obj, Obj),
    NotAParam,
}

// If pattern is a bare forall param: first sight binds goal; later sight needs equal.
// Example: pattern `a` (param) vs goal `2` -> Bound with subst[a]=2.
fn try_bind_forall_param(
    pattern: &Obj,
    goal: &Obj,
    param_ids: &HashSet<IdentifierId>,
    subst: &mut HashMap<IdentifierId, Obj>,
) -> ForallParamBindResult {
    if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = pattern {
        if param_ids.contains(id) {
            if let Some(existing) = subst.get(id) {
                return ForallParamBindResult::NeedEqual(existing.clone(), goal.clone());
            }
            subst.insert(*id, goal.clone());
            return ForallParamBindResult::Bound;
        }
    }
    ForallParamBindResult::NotAParam
}

fn strict_equal_proof_without_forall_or_rewrite(
    proof: EqualFactSearchedProof,
) -> Option<EqualFactSearchedProof> {
    match proof {
        EqualFactSearchedProof::ByBuiltinRule(_)
        | EqualFactSearchedProof::ByKnownEquality(_)
        | EqualFactSearchedProof::ByBuiltinStrategy(_) => Some(proof),
        EqualFactSearchedProof::ByKnownForallFact(_)
        | EqualFactSearchedProof::ByBuiltinRewrite(_)
        | EqualFactSearchedProof::ByKnownRewrite(_) => None,
    }
}
