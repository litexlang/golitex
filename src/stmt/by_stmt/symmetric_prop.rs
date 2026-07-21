use crate::prelude::*;
use std::collections::HashMap;
use std::fmt;

#[derive(Clone)]
pub struct BySymmetricPropStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl fmt::Display for BySymmetricPropStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{} {}:\n{}",
            BY,
            SYMMETRIC_PROP,
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

impl BySymmetricPropStmt {
    pub fn new(forall_fact: ForallFact, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        BySymmetricPropStmt {
            forall_fact,
            proof,
            line_file,
        }
    }

    pub fn symmetric_prop_registration(&self) -> Result<(String, Vec<usize>), String> {
        symmetric_prop_shape_from_forall(&self.forall_fact)
    }
}

fn symmetric_prop_shape_from_forall(
    forall_fact: &ForallFact,
) -> Result<(String, Vec<usize>), String> {
    let params = forall_fact
        .params_def_with_type
        .collect_param_names_with_types();
    if params.len() < 2 {
        return Err("by symmetric_prop: forall must declare at least two parameters".to_string());
    }
    for (_, param_type) in params.iter() {
        match param_type {
            ParamType::Set(_) => {}
            _ => {
                return Err("by symmetric_prop: each forall parameter type must be set".to_string());
            }
        }
    }

    if forall_fact.dom_facts.len() != 1 {
        return Err("by symmetric_prop: forall dom must contain exactly one fact".to_string());
    }
    if forall_fact.then_facts.len() != 1 {
        return Err("by symmetric_prop: forall then must contain exactly one fact".to_string());
    }

    let n = params.len();
    let dom_f = normal_atomic_from_dom_fact_sym(&forall_fact.dom_facts[0])?;
    let then_f = normal_atomic_from_then_fact_sym(&forall_fact.then_facts[0])?;

    let prop_name = dom_f.predicate.to_string();
    if then_f.predicate.to_string() != prop_name {
        return Err("by symmetric_prop: dom and then must use the same prop".to_string());
    }

    if dom_f.body.len() != n || then_f.body.len() != n {
        return Err(format!(
            "by symmetric_prop: dom and then must each have {} arguments",
            n
        ));
    }

    let dom_names = forall_param_names_in_order_sym(dom_f)?;
    let then_names = forall_param_names_in_order_sym(then_f)?;

    let mut param_sorted: Vec<String> = params.iter().map(|(name, _)| name.clone()).collect();
    param_sorted.sort();

    let mut dom_sorted = dom_names.clone();
    dom_sorted.sort();
    if dom_sorted != param_sorted {
        return Err(
            "by symmetric_prop: dom fact must use each forall parameter exactly once".to_string(),
        );
    }

    let mut then_sorted = then_names.clone();
    then_sorted.sort();
    if then_sorted != param_sorted {
        return Err(
            "by symmetric_prop: then fact must use each forall parameter exactly once".to_string(),
        );
    }

    let mut name_to_dom_ix: HashMap<String, usize> = HashMap::new();
    for (i, name) in dom_names.iter().enumerate() {
        if name_to_dom_ix.insert(name.clone(), i).is_some() {
            return Err("by symmetric_prop: duplicate parameter in dom arguments".to_string());
        }
    }

    let mut gather = Vec::with_capacity(n);
    for name in &then_names {
        let Some(&i) = name_to_dom_ix.get(name) else {
            return Err("by symmetric_prop: then argument is not a forall parameter".to_string());
        };
        gather.push(i);
    }

    if gather.iter().enumerate().all(|(k, &g)| g == k) {
        return Err("by symmetric_prop: dom and then argument order are identical".to_string());
    }

    Ok((prop_name, gather))
}

fn forall_param_names_in_order_sym(fact: &NormalAtomicFact) -> Result<Vec<String>, String> {
    let mut v = Vec::new();
    for obj in fact.body.iter() {
        match obj {
            Obj::Atom(AtomObj::Forall(p)) => v.push(p.name.clone()),
            _ => {
                return Err(
                    "by symmetric_prop: each argument must be a forall parameter".to_string(),
                );
            }
        }
    }
    Ok(v)
}

fn normal_atomic_from_dom_fact_sym(fact: &Fact) -> Result<&NormalAtomicFact, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NormalAtomicFact(f)) => Ok(f),
        _ => {
            Err("by symmetric_prop: dom fact must be a positive user-defined prop fact".to_string())
        }
    }
}

fn normal_atomic_from_then_fact_sym(
    fact: &ExistOrAndChainAtomicFact,
) -> Result<&NormalAtomicFact, String> {
    match fact {
        ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::NormalAtomicFact(f)) => Ok(f),
        _ => Err(
            "by symmetric_prop: then fact must be a positive user-defined prop fact".to_string(),
        ),
    }
}
