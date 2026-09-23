//! Match forall conclusion args to a goal's args.
//!
//! Same idea as legacy `match_arg_in_atomic_fact_in_known_forall_with_given_arg`:
//! 1. bare forall param → bind (or rebound + strict equal)
//! 2. same constructor shape → recurse on corresponding children
//! 3. otherwise → instantiate under current subst, then strict equal
//!
//! Example: pattern `f(a)`, goal `f(t)` with param `a` → bind `a↦t` inside
//! the application (ByStructure), not “whole term already equal”.

use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    strict_equal_arg_proof_from_searched, ForallConclusionArgMatchProof,
    MatchForallConclusionArgsProof, StrictEqualWithFact,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::collections::{HashMap, HashSet};

impl Runtime {
    // Soft miss → Ok(None). Nested equal / rebound use VerifyState all flags false.
    pub(crate) fn match_forall_conclusion_args(
        &mut self,
        pattern_args: &[&Obj],
        goal_args: &[&Obj],
        ordered_param_ids: &[IdentifierId],
    ) -> RuntimeResult<Option<MatchForallConclusionArgsProof>> {
        if pattern_args.len() != goal_args.len() {
            return Ok(None);
        }
        let param_set: HashSet<IdentifierId> = ordered_param_ids.iter().copied().collect();
        let equality_state = VerifyState {
            can_use_forall_fact: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };

        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        let mut arg_match_proofs = Vec::with_capacity(pattern_args.len());

        for (pattern_arg, goal_arg) in pattern_args.iter().zip(goal_args.iter()) {
            let Some(proof) = self.match_forall_one_arg(
                pattern_arg,
                goal_arg,
                &param_set,
                &mut subst,
                equality_state.clone(),
            )?
            else {
                return Ok(None);
            };
            arg_match_proofs.push(proof);
        }

        for id in ordered_param_ids {
            if !subst.contains_key(id) {
                return Ok(None);
            }
        }

        let forall_parameters_match_what_args: Vec<Obj> = ordered_param_ids
            .iter()
            .map(|id| subst.get(id).expect("checked").clone())
            .collect();

        Ok(Some(MatchForallConclusionArgsProof {
            forall_parameters_match_what_args,
            arg_match_proofs,
        }))
    }

    fn prove_objs_equal_strict(
        &mut self,
        left: &Obj,
        right: &Obj,
        equality_state: VerifyState,
    ) -> RuntimeResult<Option<StrictEqualWithFact>> {
        let equal_fact = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: left.clone(),
            right: right.clone(),
            line_file: None,
        };
        let Some(searched) = self.search_equal_fact_proof(&equal_fact, equality_state)? else {
            return Ok(None);
        };
        let Some(equal_proof) = strict_equal_arg_proof_from_searched(searched) else {
            return Ok(None);
        };
        Ok(Some(StrictEqualWithFact {
            equal_fact,
            equal_proof,
        }))
    }

    // Legacy-shaped: param bind → same-shape recurse (commit or fail) → else equal.
    fn match_forall_one_arg(
        &mut self,
        pattern: &Obj,
        goal: &Obj,
        param_set: &HashSet<IdentifierId>,
        subst: &mut HashMap<IdentifierId, Obj>,
        equality_state: VerifyState,
    ) -> RuntimeResult<Option<ForallConclusionArgMatchProof>> {
        match try_bind_forall_param(pattern, goal, param_set, subst) {
            ForallParamBindResult::Bound { param_id } => {
                return Ok(Some(ForallConclusionArgMatchProof::BoundParam {
                    param_id,
                    pattern: pattern.clone(),
                    goal_arg: goal.clone(),
                }));
            }
            ForallParamBindResult::NeedEqual {
                param_id,
                previous,
            } => {
                let Some(equal) =
                    self.prove_objs_equal_strict(&previous, goal, equality_state.clone())?
                else {
                    return Ok(None);
                };
                return Ok(Some(ForallConclusionArgMatchProof::ReboundParamEqual {
                    param_id,
                    previous,
                    goal_arg: goal.clone(),
                    equal,
                }));
            }
            ForallParamBindResult::NotAParam => {}
        }

        // Same constructor: recurse. No fallback to NonParamEqual (legacy-aligned).
        if let Some(pairs) = corresponding_arg_pairs(pattern, goal) {
            if !pairs.is_empty() {
                let mut child_matches = Vec::with_capacity(pairs.len());
                for (child_pattern, child_goal) in &pairs {
                    let Some(child) = self.match_forall_one_arg(
                        child_pattern,
                        child_goal,
                        param_set,
                        subst,
                        equality_state.clone(),
                    )?
                    else {
                        return Ok(None);
                    };
                    child_matches.push(child);
                }
                return Ok(Some(ForallConclusionArgMatchProof::ByStructure {
                    pattern: pattern.clone(),
                    goal_arg: goal.clone(),
                    child_matches,
                }));
            }
        }

        let pattern_after_subst = match self.inst_obj(pattern, subst) {
            Ok(obj) => obj,
            Err(_) => return Ok(None),
        };
        let Some(equal) =
            self.prove_objs_equal_strict(&pattern_after_subst, goal, equality_state)?
        else {
            return Ok(None);
        };
        Ok(Some(ForallConclusionArgMatchProof::NonParamEqual {
            pattern: pattern.clone(),
            pattern_after_subst,
            goal_arg: goal.clone(),
            equal,
        }))
    }
}

pub(crate) fn subst_from_ordered_params(
    param_ids: &[IdentifierId],
    args: &[Obj],
) -> HashMap<IdentifierId, Obj> {
    let mut subst = HashMap::new();
    for (id, arg) in param_ids.iter().zip(args.iter()) {
        subst.insert(*id, arg.clone());
    }
    subst
}

enum ForallParamBindResult {
    Bound {
        param_id: IdentifierId,
    },
    NeedEqual {
        param_id: IdentifierId,
        previous: Obj,
    },
    NotAParam,
}

fn try_bind_forall_param(
    pattern: &Obj,
    goal: &Obj,
    param_ids: &HashSet<IdentifierId>,
    subst: &mut HashMap<IdentifierId, Obj>,
) -> ForallParamBindResult {
    if let Obj::Identifier(IdentifierObj::Plain { id, .. }) = pattern {
        if param_ids.contains(id) {
            if let Some(existing) = subst.get(id) {
                return ForallParamBindResult::NeedEqual {
                    param_id: *id,
                    previous: existing.clone(),
                };
            }
            subst.insert(*id, goal.clone());
            return ForallParamBindResult::Bound { param_id: *id };
        }
    }
    ForallParamBindResult::NotAParam
}
