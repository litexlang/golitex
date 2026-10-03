//! Match forall conclusion args to a goal's args.
//!
//! Same idea as legacy `match_arg_in_atomic_fact_in_known_forall_with_given_arg`:
//! 1. bare forall param → bind (or rebound + strict equal)
//! 2. same constructor shape → recurse on corresponding children
//! 3. otherwise → instantiate under current subst, then strict equal
//!
//! Params that appear only in dom facts (not in the conclusion) stay unbound
//! here; `complete_forall_subst_from_dom_facts` fills them from known atomics.
//!
//! Example: pattern `f(a)`, goal `f(t)` with param `a` → bind `a↦t` inside
//! the application (ByStructure), not “whole term already equal”.
//! Example (dom-only middle param): known `forall x,y,z: $P(x,y), $P(y,z) => $P(x,z)`
//! goal `$P(a,c)` binds `x,z` from the conclusion; `y` is completed from a known
//! `$P(a,b)` matching the first dom under the partial subst.

use crate::ast::fact::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity, quantifier_free_fact_args_ref,
    AtomicFact, EqualFact, Fact, ForallFact,
};
use crate::ast::obj::{IdentifierObj, Obj, SetBuilder, SetFormer};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::helper::corresponding_arg_pairs;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    strict_equal_arg_proof_from_searched, ForallConclusionArgMatchProof,
    MatchForallConclusionArgsProof, StrictEqualWithFact,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::{HashMap, HashSet};

impl Runtime {
    // Soft miss → Ok(None). Nested equal / rebound use VerifyState all flags false.
    // May leave params unbound when they do not occur in the conclusion args;
    // callers that need a full subst must run `complete_forall_subst_from_dom_facts`.
    pub(crate) fn match_forall_conclusion_args(
        &mut self,
        pattern_args: &[&Obj],
        goal_args: &[&Obj],
        ordered_param_ids: &[IdentifierId],
    ) -> RuntimeResult<Option<MatchForallConclusionArgsProof>> {
        let Some((subst, arg_match_proofs)) =
            self.match_forall_conclusion_args_to_subst(pattern_args, goal_args, ordered_param_ids)?
        else {
            return Ok(None);
        };

        // Full binding required for the legacy Vec evidence shape. Prefer the
        // subst API + `complete_forall_subst_from_dom_facts` when middles exist.
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

    // Like `match_forall_conclusion_args`, but keeps a partial subst when some
    // forall params do not occur in the conclusion.
    pub(crate) fn match_forall_conclusion_args_to_subst(
        &mut self,
        pattern_args: &[&Obj],
        goal_args: &[&Obj],
        ordered_param_ids: &[IdentifierId],
    ) -> RuntimeResult<Option<(HashMap<IdentifierId, Obj>, Vec<ForallConclusionArgMatchProof>)>>
    {
        if pattern_args.len() != goal_args.len() {
            return Ok(None);
        }
        let param_set: HashSet<IdentifierId> = ordered_param_ids.iter().copied().collect();
        let equality_state = VerifyState {
            can_use_builtin_rule: false,
            remaining_deep_search_depth: 0,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            equality_class_search: crate::execute::execute_fact_stmt::EqualityClassSearchMode::AllowPeerComparison,
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

        Ok(Some((subst, arg_match_proofs)))
    }

    // Bind params that appear only in dom facts by matching each atomic dom
    // against known ambient atomics under the current partial subst.
    // Example: after `$P(x,z)` bound `x,z`, match dom `$P(x,y)` to known `$P(a,b)`.
    pub(crate) fn complete_forall_subst_from_dom_facts(
        &mut self,
        forall: &ForallFact,
        subst: &mut HashMap<IdentifierId, Obj>,
        ordered_param_ids: &[IdentifierId],
    ) -> RuntimeResult<bool> {
        let param_set: HashSet<IdentifierId> = ordered_param_ids.iter().copied().collect();
        let equality_state = VerifyState {
            can_use_builtin_rule: false,
            remaining_deep_search_depth: 0,
            can_use_def_and_known_forall_and_known_strategy: false,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            equality_class_search: crate::execute::execute_fact_stmt::EqualityClassSearchMode::AllowPeerComparison,
        };

        // Binder types are implicit premises too. Recover hidden parameters
        // only from the type of an already matched object (for example K and
        // field from space : VectorSpace<K, field, V>), never by choosing an
        // arbitrary object to fill a missing theorem argument.
        let parameters: Vec<Obj> = forall.typed_parameters.groups.iter()
            .flat_map(|group| &group.params)
            .map(|p| Obj::Identifier(IdentifierObj::from_bound_name(p))).collect();
        let type_facts = self.type_facts_for_typed_arguments(&forall.typed_parameters, &parameters)
            .map_err(crate::runtime::RuntimeError::InternalBug)?;

        let mut guard = 0;
        while ordered_param_ids.iter().any(|id| !subst.contains_key(id)) {
            guard += 1;
            if guard > ordered_param_ids.len() + 2 {
                return Ok(false);
            }
            let mut progress = false;
            let anchored_types = type_facts.iter().filter(|fact| {
                matches!(fact, Fact::AtomicFact(AtomicFact::InFact(in_fact))
                    if matches!(&in_fact.element, Obj::Identifier(IdentifierObj::Plain {id, ..})
                        if subst.contains_key(id)))
            }).cloned().collect::<Vec<_>>();
            for dom in forall.dom_facts.iter().chain(anchored_types.iter()) {
                let Fact::AtomicFact(pattern_atomic) = dom else {
                    continue;
                };
                let candidates = self.visible_known_atomics_matching_prop(pattern_atomic);
                for known in candidates {
                    let mut trial = subst.clone();
                    let pattern_args = atomic_fact_args_ref(pattern_atomic);
                    let known_args = atomic_fact_args_ref(&known);
                    if pattern_args.len() != known_args.len() {
                        continue;
                    }
                    let mut ok = true;
                    for (pattern_arg, goal_arg) in pattern_args.iter().zip(known_args.iter()) {
                        if self
                            .match_forall_one_arg(
                                pattern_arg,
                                goal_arg,
                                &param_set,
                                &mut trial,
                                equality_state.clone(),
                            )?
                            .is_none()
                        {
                            ok = false;
                            break;
                        }
                    }
                    if ok && trial.len() > subst.len() {
                        *subst = trial;
                        progress = true;
                        break;
                    }
                }
                if progress {
                    break;
                }
            }
            if !progress {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn visible_known_atomics_matching_prop(&self, pattern: &AtomicFact) -> Vec<AtomicFact> {
        let key = (pattern.prop_name(), atomic_fact_has_positive_polarity(pattern));
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(entries) = env.facts.known_atomic_except_equality_facts.by_prop.get(&key) {
                out.extend(entries.iter().cloned());
            }
        }
        out
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

        if let (Obj::SetFormer(SetFormer::SetBuilder(left)), Obj::SetFormer(SetFormer::SetBuilder(right))) = (pattern, goal) {
            let mut trial = subst.clone();
            if !self.match_set_builder_free_parameters(left, right, param_set, &mut trial, equality_state.clone())? {
                return Ok(None);
            }
            let pattern_after_subst = match self.inst_obj(pattern, &trial) {
                Ok(obj) => obj,
                Err(_) => return Ok(None),
            };
            // Argument pairing proposes a substitution only. The complete
            // builder (carrier, polarity, connectives, free owners and bound
            // occurrences) must still match under the existing alpha proof.
            let Some(equal) = self.prove_objs_equal_strict(&pattern_after_subst, goal, equality_state)? else {
                return Ok(None);
            };
            *subst = trial;
            return Ok(Some(ForallConclusionArgMatchProof::NonParamEqual {
                pattern: pattern.clone(), pattern_after_subst, goal_arg: goal.clone(), equal,
            }));
        }

        // Same constructor: recurse. No fallback to NonParamEqual (legacy-aligned).
        // A template occurrence is a constructor with definition-owned identity
        // and ordinary object arguments. Bind its parameters without unfolding.
        // Example: `\member<S> $in S` matches `\member<R> $in R` via S = R.
        let pairs = match (pattern, goal) {
            (Obj::InstantiatedTemplateObj(left), Obj::InstantiatedTemplateObj(right))
                if left.template_name == right.template_name && left.args.len() == right.args.len() =>
            {
                Some(left.args.iter().cloned().zip(right.args.iter().cloned()).collect())
            }
            _ => corresponding_arg_pairs(pattern, goal),
        };
        if let Some(pairs) = pairs {
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

    // Infer a free forall argument inside a builder while keeping its local
    // binder rigid. Example: `{x X: f(x) in U}` matches `{y X: f(y) in V}`
    // with U = V. It must never infer a free argument equal to the local y.
    fn match_set_builder_free_parameters(
        &mut self,
        pattern: &SetBuilder,
        goal: &SetBuilder,
        param_set: &HashSet<IdentifierId>,
        subst: &mut HashMap<IdentifierId, Obj>,
        equality_state: VerifyState,
    ) -> RuntimeResult<bool> {
        if pattern.facts.len() != goal.facts.len() {
            return Ok(false);
        }
        if self.match_forall_one_arg(&pattern.param_set, &goal.param_set, param_set, subst, equality_state.clone())?.is_none() {
            return Ok(false);
        }
        let rename = HashMap::from([(
            pattern.param_binding.id,
            Obj::Identifier(IdentifierObj::from_bound_name(&goal.param_binding)),
        )]);
        for (left, right) in pattern.facts.iter().zip(&goal.facts) {
            let left = match self.inst_quantifier_free_fact(left, &rename) {
                Ok(fact) => fact,
                Err(_) => return Ok(false),
            };
            let left_args = quantifier_free_fact_args_ref(&left);
            let right_args = quantifier_free_fact_args_ref(right);
            if left_args.len() != right_args.len() { return Ok(false); }
            for (left_arg, right_arg) in left_args.into_iter().zip(right_args) {
                if self.match_forall_one_arg(left_arg, right_arg, param_set, subst, equality_state.clone())?.is_none() {
                    return Ok(false);
                }
            }
        }
        for value in subst.values() {
            let mut free = HashSet::new();
            crate::instantiate::collect_free_plain_ids(value, &HashSet::new(), &mut free);
            if free.contains(&goal.param_binding.id) { return Ok(false); }
        }
        Ok(true)
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
