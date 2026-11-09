//! Structural identity for a stored forall's nested conditions and conclusions.
use crate::ast::fact::{exist_shaped_fact_from_fact, Fact, ForallFact};
use crate::ast::obj::{IdentifierObj, Obj};
use crate::ast::param::ParamType;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::{
    compound_objs_alpha_equal, plain_exist_facts_alpha_equal,
    quantifier_free_source_facts_alpha_equal,
};
use crate::runtime::Runtime;
use std::collections::HashMap;
use std::mem::discriminant;

// A nested forall is the same proposition after its own bound names are
// renamed. Free identities, carriers, guards and existential polarity stay exact.
// Example: forall x X: exist! k closed_range(1,n) st {e(k)=x}.
pub(super) fn same_source_fact(rt: &mut Runtime, source: &Fact, goal: &Fact) -> bool {
    if discriminant(source) != discriminant(goal) {
        return false;
    }
    if let (Fact::ForallFact(source), Fact::ForallFact(goal)) = (source, goal) {
        return same_nested_forall(rt, source, goal);
    }
    match (
        exist_shaped_fact_from_fact(source),
        exist_shaped_fact_from_fact(goal),
    ) {
        (Some(source), Some(goal)) => plain_exist_facts_alpha_equal(
            crate::exec_env::exist_shaped_fact_index_key::plain_exist_fact(&source),
            crate::exec_env::exist_shaped_fact_index_key::plain_exist_fact(&goal),
        ),
        _ => source.ir() == goal.ir() || quantifier_free_source_facts_alpha_equal(source, goal),
    }
}

fn same_nested_forall(rt: &mut Runtime, source: &ForallFact, goal: &ForallFact) -> bool {
    let mut source_params = Vec::new();
    for group in &source.typed_parameters.groups {
        for param in &group.params {
            source_params.push((param, &group.param_type));
        }
    }
    let mut goal_params = Vec::new();
    for group in &goal.typed_parameters.groups {
        for param in &group.params {
            goal_params.push((param, &group.param_type));
        }
    }
    if source_params.len() != goal_params.len()
        || source.dom_facts.len() != goal.dom_facts.len()
        || source.then_facts.len() != goal.then_facts.len()
    {
        return false;
    }
    let mut subst = HashMap::new();
    let mut used_targets = std::collections::HashSet::new();
    for ((source, _), (goal, _)) in source_params.iter().zip(&goal_params) {
        if subst.contains_key(&source.id) || !used_targets.insert(goal.id) {
            return false;
        }
        let value: Obj = Obj::Identifier(IdentifierObj::from_bound_name(goal));
        subst.insert(source.id, value);
    }
    for ((_, source), (_, goal)) in source_params.iter().zip(&goal_params) {
        let Ok(inst) = rt.inst_param_type(source, &subst) else {
            return false;
        };
        let same = match (&inst, *goal) {
            (ParamType::Obj(source), ParamType::Obj(goal)) => {
                compound_objs_alpha_equal(source, goal)
            }
            (ParamType::Set(_), ParamType::Set(_))
            | (ParamType::NonemptySet(_), ParamType::NonemptySet(_))
            | (ParamType::FiniteSet(_), ParamType::FiniteSet(_)) => true,
            _ => false,
        };
        if !same {
            return false;
        }
    }
    for (source, goal) in source.dom_facts.iter().zip(&goal.dom_facts) {
        let Ok(inst) = rt.inst_fact(source, &subst) else {
            return false;
        };
        if !same_source_fact(rt, &inst, goal) {
            return false;
        }
    }
    for (source, goal) in source.then_facts.iter().zip(&goal.then_facts) {
        let Ok(inst) = rt.inst_fact(&Fact::from(source.clone()), &subst) else {
            return false;
        };
        if !same_source_fact(rt, &inst, &Fact::from(goal.clone())) {
            return false;
        }
    }
    true
}

#[cfg(test)]
#[test]
fn nested_forall_alpha_requires_distinct_target_binders() {
    use crate::prelude::*;
    let mut runtime = Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    });
    let blocks = crate::tokenize::Tokenizer::new()
        .tokenize("forall a,b R:\n    a=a", runtime.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::ForallFact(source)) = runtime.parse(&blocks).unwrap().remove(0) else {
        panic!("forall source");
    };
    assert!(same_nested_forall(&mut runtime, &source, &source));
    let mut target = source.clone();
    target.typed_parameters.groups[0].params[1] =
        target.typed_parameters.groups[0].params[0].clone();
    assert!(!same_nested_forall(&mut runtime, &source, &target));
}
