use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct ByCommutativePropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl fmt::Display for ByCommutativePropStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}:\n{}{}\n{}",
            BY,
            COMMUTATIVE_PROP,
            add_four_spaces_at_beginning(PROVE.to_string(), 1),
            COLON,
            to_string_and_add_four_spaces_at_beginning_of_each_line(
                &self.forall_fact.to_string(),
                2
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

impl ByCommutativePropStmt {
    pub fn new(forall_fact: ForallFact, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByCommutativePropStmt {
            forall_fact,
            proof,
            line_file,
        }
    }

    pub fn commutative_prop_name(&self) -> Result<String, String> {
        commutative_prop_name_from_forall(&self.forall_fact)
    }
}

fn commutative_prop_name_from_forall(forall_fact: &ForallFact) -> Result<String, String> {
    let params = forall_fact
        .params_def_with_type
        .collect_param_names_with_types();
    if params.len() != 2 {
        return Err("by commutative_prop: forall must declare exactly two parameters".to_string());
    }
    for (_, param_type) in params.iter() {
        match param_type {
            ParamType::Set(_) => {}
            _ => {
                return Err(
                    "by commutative_prop: each forall parameter type must be set".to_string(),
                );
            }
        }
    }

    if forall_fact.dom_facts.len() != 1 {
        return Err("by commutative_prop: forall dom must contain exactly one fact".to_string());
    }
    if forall_fact.then_facts.len() != 1 {
        return Err("by commutative_prop: forall then must contain exactly one fact".to_string());
    }

    let x = &params[0].0;
    let y = &params[1].0;
    let dom_f = normal_atomic_from_dom_fact_comm(&forall_fact.dom_facts[0])?;
    let then_f = normal_atomic_from_then_fact_comm(&forall_fact.then_facts[0])?;

    let prop_name = dom_f.predicate.to_string();
    if then_f.predicate.to_string() != prop_name {
        return Err("by commutative_prop: dom and then must use the same prop".to_string());
    }

    if !normal_atomic_has_args_comm(dom_f, x, y) || !normal_atomic_has_args_comm(then_f, y, x) {
        return Err("by commutative_prop: expected $p(x, y) => $p(y, x)".to_string());
    }

    Ok(prop_name)
}

fn normal_atomic_from_dom_fact_comm(fact: &Fact) -> Result<&NormalAtomicFact, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(f)) => Ok(f),
        _ => Err("by commutative_prop: dom fact must be a positive prop fact".to_string()),
    }
}

fn normal_atomic_from_then_fact_comm(
    fact: &ExistOrAndChainAtomicFact,
) -> Result<&NormalAtomicFact, String> {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NormalAtomicFact(f)) => Ok(f),
        _ => Err("by commutative_prop: then fact must be a positive prop fact".to_string()),
    }
}

fn normal_atomic_has_args_comm(fact: &NormalAtomicFact, left: &str, right: &str) -> bool {
    if fact.body.len() != 2 {
        return false;
    }
    obj_is_forall_param_comm(&fact.body[0], left) && obj_is_forall_param_comm(&fact.body[1], right)
}

fn obj_is_forall_param_comm(obj: &Obj, name: &str) -> bool {
    match obj {
        Obj::Atom(AtomObj::Forall(p)) => p.name == name,
        _ => false,
    }
}
