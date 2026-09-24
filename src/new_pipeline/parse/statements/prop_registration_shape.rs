use crate::new_pipeline::ast::fact::{
    AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, NormalAtomicFact,
};
use crate::new_pipeline::ast::names::{AtomicName, BoundName};
use crate::new_pipeline::ast::obj::{IdentifierObj, Obj};
use crate::new_pipeline::ast::param::ParamType;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use std::collections::HashMap;

// Shape check for `register reflexive`: forall x set: $p(x, x).
pub fn reflexive_prop_name_from_forall(forall_fact: &ForallFact) -> Result<AtomicName, String> {
    let params = flatten_set_params(forall_fact, "register reflexive")?;
    if params.len() != 1 {
        return Err("register reflexive: forall must bind exactly one parameter".to_string());
    }
    if !forall_fact.dom_facts.is_empty() {
        return Err("register reflexive: forall dom must be empty".to_string());
    }
    if forall_fact.then_facts.len() != 1 {
        return Err("register reflexive: forall then must contain exactly one fact".to_string());
    }
    let then = normal_atomic_from_then(&forall_fact.then_facts[0], "register reflexive")?;
    let x = &params[0];
    if then.body.len() != 2
        || !obj_is_bound_param(&then.body[0], x)
        || !obj_is_bound_param(&then.body[1], x)
    {
        return Err("register reflexive: expected `forall x set: $p(x, x)`".to_string());
    }
    Ok(then.predicate.clone())
}

// Shape check for `register symmetric`: returns (prop, gather) where gather maps
// then-arg index -> dom-arg index.
pub fn symmetric_prop_registration_from_forall(
    forall_fact: &ForallFact,
) -> Result<(AtomicName, Vec<usize>), String> {
    let params = flatten_set_params(forall_fact, "register symmetric")?;
    if params.len() < 2 {
        return Err("register symmetric: forall must bind at least two parameters".to_string());
    }
    if forall_fact.dom_facts.len() != 1 {
        return Err("register symmetric: forall dom must contain exactly one fact".to_string());
    }
    if forall_fact.then_facts.len() != 1 {
        return Err("register symmetric: forall then must contain exactly one fact".to_string());
    }
    let n = params.len();
    let dom_f = normal_atomic_from_dom(&forall_fact.dom_facts[0], "register symmetric")?;
    let then_f = normal_atomic_from_then(&forall_fact.then_facts[0], "register symmetric")?;
    if dom_f.predicate != then_f.predicate {
        return Err("register symmetric: dom and then must use the same prop".to_string());
    }
    if dom_f.body.len() != n || then_f.body.len() != n {
        return Err(format!(
            "register symmetric: dom and then must each have {} arguments",
            n
        ));
    }
    let dom_ids = bound_param_ids_in_order(&dom_f.body, "register symmetric")?;
    let then_ids = bound_param_ids_in_order(&then_f.body, "register symmetric")?;

    let mut param_ids: Vec<_> = params.iter().map(|p| p.id).collect();
    param_ids.sort_by_key(|id| id.value());
    let mut dom_sorted = dom_ids.clone();
    dom_sorted.sort_by_key(|id| id.value());
    if dom_sorted != param_ids {
        return Err(
            "register symmetric: dom fact must use each forall parameter exactly once".to_string(),
        );
    }
    let mut then_sorted = then_ids.clone();
    then_sorted.sort_by_key(|id| id.value());
    if then_sorted != param_ids {
        return Err(
            "register symmetric: then fact must use each forall parameter exactly once".to_string(),
        );
    }

    let mut id_to_dom_ix: HashMap<u64, usize> = HashMap::new();
    for (i, id) in dom_ids.iter().enumerate() {
        if id_to_dom_ix.insert(id.value(), i).is_some() {
            return Err("register symmetric: duplicate parameter in dom arguments".to_string());
        }
    }
    let mut gather = Vec::with_capacity(n);
    for id in &then_ids {
        let Some(&i) = id_to_dom_ix.get(&id.value()) else {
            return Err("register symmetric: then argument is not a forall parameter".to_string());
        };
        gather.push(i);
    }
    if gather.iter().enumerate().all(|(k, &g)| g == k) {
        return Err("register symmetric: dom and then argument order are identical".to_string());
    }
    Ok((dom_f.predicate.clone(), gather))
}

fn flatten_set_params(
    forall_fact: &ForallFact,
    syntax: &str,
) -> Result<Vec<BoundName>, String> {
    let mut params = Vec::new();
    for group in &forall_fact.typed_parameters.groups {
        match &group.param_type {
            ParamType::Set(_) => {}
            _ => {
                return Err(format!("{syntax}: each forall parameter type must be set"));
            }
        }
        for p in &group.params {
            params.push(p.clone());
        }
    }
    Ok(params)
}

fn normal_atomic_from_then<'a>(
    fact: &'a ExistOrAndChainAtomicFact,
    syntax: &str,
) -> Result<&'a NormalAtomicFact, String> {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NormalAtomicFact(f)) => Ok(f),
        _ => Err(format!(
            "{syntax}: then fact must be a positive user-defined prop fact"
        )),
    }
}

fn normal_atomic_from_dom<'a>(fact: &'a Fact, syntax: &str) -> Result<&'a NormalAtomicFact, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(f)) => Ok(f),
        _ => Err(format!(
            "{syntax}: dom fact must be a positive user-defined prop fact"
        )),
    }
}

fn obj_is_bound_param(obj: &Obj, param: &BoundName) -> bool {
    match obj {
        Obj::Identifier(IdentifierObj::Plain { id, .. }) => *id == param.id,
        _ => false,
    }
}

fn bound_param_ids_in_order(body: &[Obj], syntax: &str) -> Result<Vec<IdentifierId>, String> {
    let mut ids = Vec::new();
    for obj in body {
        match obj {
            Obj::Identifier(IdentifierObj::Plain { id, .. }) => ids.push(*id),
            _ => {
                return Err(format!(
                    "{syntax}: each argument must be a forall parameter"
                ));
            }
        }
    }
    Ok(ids)
}


// Shape check for `register transitive`:
// forall x, y, z set: $p(x, y); $p(y, z) => $p(x, z).
pub fn transitive_prop_name_from_forall(forall_fact: &ForallFact) -> Result<AtomicName, String> {
    let params = flatten_set_params(forall_fact, "register transitive")?;
    if params.len() != 3 {
        return Err("register transitive: forall must bind exactly three parameters".to_string());
    }
    if forall_fact.dom_facts.len() != 2 {
        return Err("register transitive: forall dom must contain exactly two facts".to_string());
    }
    if forall_fact.then_facts.len() != 1 {
        return Err("register transitive: forall then must contain exactly one fact".to_string());
    }
    let x = &params[0];
    let y = &params[1];
    let z = &params[2];
    let first = normal_atomic_from_dom(&forall_fact.dom_facts[0], "register transitive")?;
    let second = normal_atomic_from_dom(&forall_fact.dom_facts[1], "register transitive")?;
    let then = normal_atomic_from_then(&forall_fact.then_facts[0], "register transitive")?;
    if first.predicate != second.predicate || first.predicate != then.predicate {
        return Err("register transitive: all facts must use the same prop".to_string());
    }
    if first.body.len() != 2
        || second.body.len() != 2
        || then.body.len() != 2
        || !obj_is_bound_param(&first.body[0], x)
        || !obj_is_bound_param(&first.body[1], y)
        || !obj_is_bound_param(&second.body[0], y)
        || !obj_is_bound_param(&second.body[1], z)
        || !obj_is_bound_param(&then.body[0], x)
        || !obj_is_bound_param(&then.body[1], z)
    {
        return Err(
            "register transitive: expected `$p(x, y)`, `$p(y, z)` => `$p(x, z)`".to_string(),
        );
    }
    Ok(first.predicate.clone())
}

pub fn plain_prop_name(prop: &AtomicName) -> &str {
    prop.local_name()
}
