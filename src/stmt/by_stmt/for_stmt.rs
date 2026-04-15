use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ClosedRangeOrRange {
    ClosedRange(ClosedRange),
    Range(Range),
}

/// `by for:` with `prove:` and one `forall` whose parameters are `range` / `closed_range`.
#[derive(Clone)]
pub struct ByForStmt {
    pub forall_fact: ForallFact,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl fmt::Display for ByForStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {}:\n{}{}\n{}",
            BY,
            FOR,
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

impl ByForStmt {
    pub fn new(forall_fact: ForallFact, proof: Vec<Stmt>, line_file: LineFile) -> Self {
        ByForStmt {
            forall_fact,
            proof,
            line_file,
        }
    }

    /// One `range` / `closed_range` slot per parameter name (groups are expanded).
    pub fn expanded_range_params(&self) -> Result<(Vec<String>, Vec<ClosedRangeOrRange>), String> {
        let mut params = Vec::new();
        let mut param_sets = Vec::new();
        for g in self.forall_fact.params_def_with_type.groups.iter() {
            let set = match &g.param_type {
                ParamType::Obj(Obj::Range(r)) => ClosedRangeOrRange::Range(r.clone()),
                ParamType::Obj(Obj::ClosedRange(c)) => ClosedRangeOrRange::ClosedRange(c.clone()),
                _ => {
                    return Err(
                        "by for: each forall parameter type must be range or closed_range"
                            .to_string(),
                    );
                }
            };
            for name in g.params.iter() {
                params.push(name.clone());
                param_sets.push(set.clone());
            }
        }
        if params.is_empty() {
            return Err("by for: forall must declare at least one parameter".to_string());
        }
        Ok((params, param_sets))
    }

    pub fn to_corresponding_forall_fact(&self) -> Result<Fact, String> {
        self.expanded_range_params()?;
        Ok(self.forall_fact.clone().into())
    }
}

impl fmt::Display for ClosedRangeOrRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClosedRangeOrRange::ClosedRange(closed_range) => write!(f, "{}", closed_range),
            ClosedRangeOrRange::Range(range) => write!(f, "{}", range),
        }
    }
}
