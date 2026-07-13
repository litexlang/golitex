use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByReflexivePropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl fmt::Display for ByReflexivePropStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}:\n{}",
            BY,
            REFLEXIVE_PROP,
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

impl ByReflexivePropStmt {
    pub fn new(forall_fact: ForallFact, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByReflexivePropStmt {
            forall_fact,
            proof,
            line_file,
        }
    }

    pub fn reflexive_prop_name(&self) -> Result<String, String> {
        reflexive_prop_name_from_forall(&self.forall_fact)
    }
}

fn reflexive_prop_name_from_forall(forall_fact: &ForallFact) -> Result<String, String> {
    let params = forall_fact
        .params_def_with_type
        .collect_param_names_with_types();
    if params.len() != 1 {
        return Err("by reflexive_prop: forall must declare exactly one parameter".to_string());
    }
    for (_, param_type) in params.iter() {
        match param_type {
            ParamType::Set(_) => {}
            _ => {
                return Err("by reflexive_prop: each forall parameter type must be set".to_string());
            }
        }
    }

    if !forall_fact.dom_facts.is_empty() {
        return Err("by reflexive_prop: forall dom must be empty".to_string());
    }
    if forall_fact.then_facts.len() != 1 {
        return Err("by reflexive_prop: forall then must contain exactly one fact".to_string());
    }

    let x = &params[0].0;
    let then = normal_atomic_from_then_fact_refl(&forall_fact.then_facts[0])?;
    if !normal_atomic_has_args_refl(then, x, x) {
        return Err("by reflexive_prop: expected `forall x set: $p(x, x)`".to_string());
    }

    Ok(then.predicate.to_string())
}

fn normal_atomic_from_then_fact_refl(
    fact: &ExistOrAndChainAtomicFact,
) -> Result<&NormalAtomicFact, String> {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NormalAtomicFact(f)) => Ok(f),
        _ => Err(
            "by reflexive_prop: then fact must be a positive user-defined prop fact".to_string(),
        ),
    }
}

fn normal_atomic_has_args_refl(fact: &NormalAtomicFact, left: &str, right: &str) -> bool {
    if fact.body.len() != 2 {
        return false;
    }
    obj_is_forall_param_refl(&fact.body[0], left) && obj_is_forall_param_refl(&fact.body[1], right)
}

fn obj_is_forall_param_refl(obj: &Obj, name: &str) -> bool {
    match obj {
        Obj::Atom(AtomObj::Forall(p)) => p.name == name,
        _ => false,
    }
}
