//! Apply a stored forall's atomic then to prove a goal atomic.
//!
//! Phase 1 matching: each conclusion arg is either a forall param identifier
//! (bind to the goal arg) or a closed term matching by `ir()`. Nested param
//! occurrences inside compound objs are not matched yet.

use crate::new_pipeline::ast::fact::{
    AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, InFact, IsSetFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::param::TypedParameterList;
use crate::new_pipeline::exec_env::helper::{
    atomic_fact_args_ref, atomic_fact_has_positive_polarity,
};
use crate::new_pipeline::exec_env::known_forall_conclusion_memory::IndexedForallAtomicConclusion;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};
use std::collections::{HashMap, HashSet};

impl Runtime {
    pub fn search_atomic_fact_proof_by_known_forall_fact(
        &mut self,
        goal: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        if !verify_state.can_use_forall_fact {
            return Ok(None);
        }
        let candidates = self.visible_forall_atomic_conclusion_candidates(goal);
        for entry in candidates {
            if let Some(proof) =
                self.try_apply_indexed_forall_conclusion(goal, &entry, verify_state.clone())?
            {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    fn visible_forall_atomic_conclusion_candidates(
        &self,
        goal: &AtomicFact,
    ) -> Vec<IndexedForallAtomicConclusion> {
        let mut out = Vec::new();
        for env in self.execution_environments_stack.iter().rev() {
            match goal {
                AtomicFact::EqualFact(_) => {
                    out.extend(env.facts.known_forall_conclusions.equal_conclusions.iter().cloned());
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

    fn try_apply_indexed_forall_conclusion(
        &mut self,
        goal: &AtomicFact,
        entry: &IndexedForallAtomicConclusion,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        let forall = match self.fact_by_id_in_stack(entry.source_fact_id) {
            Some(Fact::ForallFact(f)) => f.clone(),
            _ => return Ok(None),
        };
        let Some(conclusion) = then_atomic_at(&forall, entry.then_fact_index) else {
            return Ok(None);
        };
        if conclusion.prop_name() != goal.prop_name()
            || atomic_fact_has_positive_polarity(&conclusion)
                != atomic_fact_has_positive_polarity(goal)
        {
            return Ok(None);
        }

        let param_names = ordered_param_names(&forall.typed_parameters);
        let param_set: HashSet<String> = param_names.iter().cloned().collect();
        let conclusion_args = atomic_fact_args_ref(&conclusion);
        let goal_args = atomic_fact_args_ref(goal);
        if conclusion_args.len() != goal_args.len() {
            return Ok(None);
        }

        let mut subst: HashMap<String, Obj> = HashMap::new();
        for (pattern_arg, goal_arg) in conclusion_args.iter().zip(goal_args.iter()) {
            if !unify_obj_phase1(pattern_arg, goal_arg, &param_set, &mut subst) {
                return Ok(None);
            }
        }
        for name in &param_names {
            if !subst.contains_key(name) {
                return Ok(None);
            }
        }

        let forall_parameters_match_what_args: Vec<Obj> = param_names
            .iter()
            .map(|name| subst.get(name).expect("checked").clone())
            .collect();

        let requirement_facts = match build_requirement_facts(self, &forall, &param_names, &subst)? {
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
            cite_fact_id: entry.source_fact_id,
            then_fact_index: entry.then_fact_index,
            forall_parameters_match_what_args,
            requirement_facts,
            proof_of_requirement_facts,
        }))
    }

    fn fact_by_id_in_stack(&self, fact_id: FactId) -> Option<&Fact> {
        for env in self.execution_environments_stack.iter().rev() {
            if let Some(fact) = env.facts.facts_by_id.get(&fact_id) {
                return Some(fact);
            }
        }
        None
    }
}

fn then_atomic_at(forall: &ForallFact, then_fact_index: usize) -> Option<AtomicFact> {
    match forall.then_facts.get(then_fact_index)? {
        ExistOrAndChainAtomicFact::AtomicFact(atomic) => Some(atomic.clone()),
        _ => None,
    }
}

fn ordered_param_names(params: &TypedParameterList) -> Vec<String> {
    let mut names = Vec::new();
    for group in &params.groups {
        for param in &group.params {
            names.push(param.name.clone());
        }
    }
    names
}

// Pattern arg is a param identifier → bind; otherwise require exact ir match.
fn unify_obj_phase1(
    pattern: &Obj,
    goal: &Obj,
    param_names: &HashSet<String>,
    subst: &mut HashMap<String, Obj>,
) -> bool {
    if let Obj::Identifier(id) = pattern {
        if let AtomicName::Plain { name } = &id.name {
            if param_names.contains(name) {
                if let Some(existing) = subst.get(name) {
                    return existing.ir() == goal.ir();
                }
                subst.insert(name.clone(), goal.clone());
                return true;
            }
        }
    }
    pattern.ir() == goal.ir()
}

fn build_requirement_facts(
    _runtime: &mut Runtime,
    forall: &ForallFact,
    _param_names: &[String],
    subst: &HashMap<String, Obj>,
) -> RuntimeResult<Option<Vec<Fact>>> {
    // Phase 1: only instantiate dom facts. Param-type obligations (x ∈ S, …)
    // wait until introduce_typed_parameters stores type facts reliably.
    let mut requirements = Vec::new();
    for dom in &forall.dom_facts {
        let Some(fact) = substitute_fact_phase1(dom, subst) else {
            return Ok(None);
        };
        requirements.push(fact);
    }
    Ok(Some(requirements))
}

fn substitute_fact_phase1(fact: &Fact, subst: &HashMap<String, Obj>) -> Option<Fact> {
    match fact {
        Fact::AtomicFact(atomic) => {
            Some(Fact::AtomicFact(substitute_atomic_phase1(atomic, subst)?))
        }
        _ => None,
    }
}

fn substitute_atomic_phase1(
    atomic: &AtomicFact,
    subst: &HashMap<String, Obj>,
) -> Option<AtomicFact> {
    // Rebuild by substituting each arg; only supports args that are identifiers
    // or closed terms (unify_obj_phase1 rules via substitute_obj_phase1).
    let args = atomic_fact_args_ref(atomic);
    let mut new_args = Vec::with_capacity(args.len());
    for arg in args {
        new_args.push(substitute_obj_phase1(arg, subst)?);
    }
    rebuild_atomic_with_args(atomic, &new_args)
}

fn substitute_obj_phase1(obj: &Obj, subst: &HashMap<String, Obj>) -> Option<Obj> {
    if let Obj::Identifier(id) = obj {
        if let AtomicName::Plain { name } = &id.name {
            if let Some(replacement) = subst.get(name) {
                return Some(replacement.clone());
            }
        }
    }
    // Closed term or free name not in subst: keep as-is only if no param name
    // appears inside. Phase 1: require ir stable (no nested params).
    if obj_contains_param_name(obj, &subst.keys().cloned().collect()) {
        return None;
    }
    Some(obj.clone())
}

fn obj_contains_param_name(obj: &Obj, param_names: &HashSet<String>) -> bool {
    if let Obj::Identifier(id) = obj {
        if let AtomicName::Plain { name } = &id.name {
            return param_names.contains(name);
        }
    }
    false
}

fn rebuild_atomic_with_args(atomic: &AtomicFact, args: &[Obj]) -> Option<AtomicFact> {
    match atomic {
        AtomicFact::EqualFact(f) => {
            let [left, right] = take_two(args)?;
            Some(AtomicFact::EqualFact(crate::new_pipeline::ast::fact::EqualFact {
                fact_id: f.fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::NotEqualFact(f) => {
            let [left, right] = take_two(args)?;
            Some(AtomicFact::NotEqualFact(
                crate::new_pipeline::ast::fact::NotEqualFact {
                    fact_id: f.fact_id,
                    left,
                    right,
                    line_file: f.line_file.clone(),
                },
            ))
        }
        AtomicFact::InFact(f) => {
            let [element, set] = take_two(args)?;
            Some(AtomicFact::InFact(InFact {
                fact_id: f.fact_id,
                element,
                set,
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::NormalAtomicFact(f) => Some(AtomicFact::NormalAtomicFact(
            crate::new_pipeline::ast::fact::NormalAtomicFact {
                fact_id: f.fact_id,
                predicate: f.predicate.clone(),
                body: args.to_vec(),
                line_file: f.line_file.clone(),
            },
        )),
        AtomicFact::NotNormalAtomicFact(f) => Some(AtomicFact::NotNormalAtomicFact(
            crate::new_pipeline::ast::fact::NotNormalAtomicFact {
                fact_id: f.fact_id,
                predicate: f.predicate.clone(),
                body: args.to_vec(),
                line_file: f.line_file.clone(),
            },
        )),
        // Phase 1: rebuild common shapes used in requirements / then matching.
        AtomicFact::LessFact(f) => {
            let [left, right] = take_two(args)?;
            Some(AtomicFact::LessFact(crate::new_pipeline::ast::fact::LessFact {
                fact_id: f.fact_id,
                left,
                right,
                line_file: f.line_file.clone(),
            }))
        }
        AtomicFact::GreaterFact(f) => {
            let [left, right] = take_two(args)?;
            Some(AtomicFact::GreaterFact(
                crate::new_pipeline::ast::fact::GreaterFact {
                    fact_id: f.fact_id,
                    left,
                    right,
                    line_file: f.line_file.clone(),
                },
            ))
        }
        AtomicFact::IsSetFact(f) => {
            let [set] = take_one(args)?;
            Some(AtomicFact::IsSetFact(IsSetFact {
                fact_id: f.fact_id,
                set,
                line_file: f.line_file.clone(),
            }))
        }
        _ => None,
    }
}

fn take_one(args: &[Obj]) -> Option<[Obj; 1]> {
    match args {
        [a] => Some([a.clone()]),
        _ => None,
    }
}

fn take_two(args: &[Obj]) -> Option<[Obj; 2]> {
    match args {
        [a, b] => Some([a.clone(), b.clone()]),
        _ => None,
    }
}
