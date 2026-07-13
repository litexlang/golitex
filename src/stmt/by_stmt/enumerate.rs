use crate::prelude::*;
use std::fmt;

/// List-set enumeration: `by enumerate finite_set:` then `?` / one `forall`.
#[derive(Clone)]
pub struct ByEnumerateFiniteSetStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl ByEnumerateFiniteSetStmt {
    pub fn new(forall_fact: ForallFact, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByEnumerateFiniteSetStmt {
            forall_fact,
            proof,
            line_file,
        }
    }

    /// One list-set slot per parameter name (groups are expanded).
    pub fn expanded_list_set_params(&self) -> Result<(Vec<String>, Vec<ListSet>), String> {
        let mut params = Vec::new();
        let mut param_sets = Vec::new();
        for g in self.forall_fact.params_def_with_type.groups.iter() {
            let list_set = match &g.param_type {
                ParamType::Obj(Obj::ListSet(ls)) => ls.clone(),
                _ => {
                    return Err(
                        "by enumerate finite_set: each forall parameter type must be a list set `{ ... }`"
                            .to_string(),
                    );
                }
            };
            for name in g.params.iter() {
                params.push(name.clone());
                param_sets.push(list_set.clone());
            }
        }
        if params.is_empty() {
            return Err(
                "by enumerate finite_set: forall must declare at least one parameter".to_string(),
            );
        }
        Ok((params, param_sets))
    }

    pub fn to_corresponding_forall_fact(&self) -> Result<Fact, String> {
        self.expanded_list_set_params()?;
        Ok(self.forall_fact.clone().into())
    }
}

impl fmt::Display for ByEnumerateFiniteSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} {}:\n{}",
            BY,
            ENUMERATE,
            FINITE_SET,
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
