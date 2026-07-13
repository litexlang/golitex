use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByAntisymmetricPropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl fmt::Display for ByAntisymmetricPropStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}:\n{}",
            BY,
            ANTISYMMETRIC_PROP,
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

impl ByAntisymmetricPropStmt {
    pub fn new(forall_fact: ForallFact, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByAntisymmetricPropStmt {
            forall_fact,
            proof,
            line_file,
        }
    }

    pub fn antisymmetric_prop_name(&self) -> Result<String, String> {
        antisymmetric_prop_name_from_forall(&self.forall_fact)
    }
}

fn antisymmetric_prop_name_from_forall(forall_fact: &ForallFact) -> Result<String, String> {
    let params = forall_fact
        .params_def_with_type
        .collect_param_names_with_types();
    if params.len() != 2 {
        return Err(
            "by antisymmetric_prop: forall must declare exactly two parameters".to_string(),
        );
    }
    for (_, param_type) in params.iter() {
        match param_type {
            ParamType::Set(_) => {}
            _ => {
                return Err(
                    "by antisymmetric_prop: each forall parameter type must be set".to_string(),
                );
            }
        }
    }

    if forall_fact.dom_facts.len() != 2 {
        return Err("by antisymmetric_prop: forall dom must contain exactly two facts".to_string());
    }
    if forall_fact.then_facts.len() != 1 {
        return Err("by antisymmetric_prop: forall then must contain exactly one fact".to_string());
    }

    let x = &params[0].0;
    let y = &params[1].0;
    let first = normal_atomic_from_dom_fact_antisym(&forall_fact.dom_facts[0])?;
    let second = normal_atomic_from_dom_fact_antisym(&forall_fact.dom_facts[1])?;
    let then = equal_fact_from_then_fact_antisym(&forall_fact.then_facts[0])?;

    let prop_name = first.predicate.to_string();
    if second.predicate.to_string() != prop_name {
        return Err("by antisymmetric_prop: dom facts must use the same prop".to_string());
    }

    if !normal_atomic_has_args_antisym(first, x, y)
        || !normal_atomic_has_args_antisym(second, y, x)
        || !equal_fact_has_args_antisym(then, x, y)
    {
        return Err("by antisymmetric_prop: expected $p(x, y), $p(y, x) => x = y".to_string());
    }

    Ok(prop_name)
}

fn normal_atomic_from_dom_fact_antisym(fact: &Fact) -> Result<&NormalAtomicFact, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(f)) => Ok(f),
        _ => Err(
            "by antisymmetric_prop: dom facts must be positive user-defined prop facts".to_string(),
        ),
    }
}

fn equal_fact_from_then_fact_antisym(
    fact: &ExistOrAndChainAtomicFact,
) -> Result<&EqualFact, String> {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(f)) => Ok(f),
        _ => Err("by antisymmetric_prop: then fact must be an equality".to_string()),
    }
}

fn normal_atomic_has_args_antisym(fact: &NormalAtomicFact, left: &str, right: &str) -> bool {
    if fact.body.len() != 2 {
        return false;
    }
    obj_is_forall_param_antisym(&fact.body[0], left)
        && obj_is_forall_param_antisym(&fact.body[1], right)
}

fn equal_fact_has_args_antisym(fact: &EqualFact, left: &str, right: &str) -> bool {
    obj_is_forall_param_antisym(&fact.left, left) && obj_is_forall_param_antisym(&fact.right, right)
}

fn obj_is_forall_param_antisym(obj: &Obj, name: &str) -> bool {
    match obj {
        Obj::Atom(AtomObj::Forall(p)) => p.name == name,
        _ => false,
    }
}
