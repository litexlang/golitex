use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByTransitivePropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl fmt::Display for ByTransitivePropStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}:\n{}",
            BY,
            TRANSITIVE_PROP,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &format!("{} {}", QUESTION_GOAL, self.forall_fact),
                1
            )
        )?;
        if !self.proof.is_empty() {
            write!(
                f,
                "\n{}",
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
            )?;
        }
        Ok(())
    }
}

impl ByTransitivePropStmt {
    pub fn new(forall_fact: ForallFact, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByTransitivePropStmt {
            forall_fact,
            proof,
            line_file,
        }
    }

    pub fn transitive_prop_name(&self) -> Result<String, String> {
        transitive_prop_name_from_forall(&self.forall_fact)
    }
}

fn transitive_prop_name_from_forall(forall_fact: &ForallFact) -> Result<String, String> {
    let params = forall_fact
        .params_def_with_type
        .collect_param_names_with_types();
    if params.len() != 3 {
        return Err("by transitive_prop: forall must declare exactly three parameters".to_string());
    }
    for (_, param_type) in params.iter() {
        match param_type {
            ParamType::Set(_) => {}
            _ => {
                return Err(
                    "by transitive_prop: each forall parameter type must be set".to_string()
                );
            }
        }
    }

    if forall_fact.dom_facts.len() != 2 {
        return Err("by transitive_prop: forall dom must contain exactly two facts".to_string());
    }
    if forall_fact.then_facts.len() != 1 {
        return Err("by transitive_prop: forall then must contain exactly one fact".to_string());
    }

    let x = &params[0].0;
    let y = &params[1].0;
    let z = &params[2].0;
    let first = normal_atomic_from_dom_fact(&forall_fact.dom_facts[0])?;
    let second = normal_atomic_from_dom_fact(&forall_fact.dom_facts[1])?;
    let then = normal_atomic_from_then_fact(&forall_fact.then_facts[0])?;

    let prop_name = first.predicate.to_string();
    if second.predicate.to_string() != prop_name || then.predicate.to_string() != prop_name {
        return Err("by transitive_prop: all facts must use the same prop".to_string());
    }

    if !normal_atomic_has_args(first, x, y)
        || !normal_atomic_has_args(second, y, z)
        || !normal_atomic_has_args(then, x, z)
    {
        return Err("by transitive_prop: expected $p(x, y), $p(y, z) => $p(x, z)".to_string());
    }

    Ok(prop_name)
}

fn normal_atomic_from_dom_fact(fact: &Fact) -> Result<&NormalAtomicFact, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(f)) => Ok(f),
        _ => Err("by transitive_prop: dom facts must be positive prop facts".to_string()),
    }
}

fn normal_atomic_from_then_fact(
    fact: &ExistOrAndChainAtomicFact,
) -> Result<&NormalAtomicFact, String> {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NormalAtomicFact(f)) => Ok(f),
        _ => Err("by transitive_prop: then fact must be a positive prop fact".to_string()),
    }
}

fn normal_atomic_has_args(fact: &NormalAtomicFact, left: &str, right: &str) -> bool {
    if fact.body.len() != 2 {
        return false;
    }
    obj_is_forall_param(&fact.body[0], left) && obj_is_forall_param(&fact.body[1], right)
}

fn obj_is_forall_param(obj: &Obj, name: &str) -> bool {
    match obj {
        Obj::Atom(AtomObj::Forall(p)) => p.name == name,
        _ => false,
    }
}
