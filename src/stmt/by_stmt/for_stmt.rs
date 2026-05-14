use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ClosedRangeOrRange {
    ClosedRange(ClosedRange),
    Range(Range),
}

/// Expanded iteration domain for `by for` (integer ranges or one tuple parameter over a cartesian
/// product of list sets).
#[derive(Clone)]
pub enum ByForExpansion {
    Ranges {
        params: Vec<String>,
        ranges: Vec<ClosedRangeOrRange>,
    },
    CartOfListSets {
        param: String,
        factors: Vec<ListSet>,
    },
}

/// `by for:` with `prove:` and one `forall`: `range` / `closed_range` parameters, or one tuple
/// parameter with type `cart({...}, {...}, ...)` (list-set factors).
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

    fn cart_factors_if_all_list_sets(obj: &Obj) -> Option<Vec<ListSet>> {
        let Obj::Cart(cart) = obj else {
            return None;
        };
        let mut factors = Vec::new();
        for a in cart.args.iter() {
            match a.as_ref() {
                Obj::ListSet(ls) => factors.push(ls.clone()),
                _ => return None,
            }
        }
        Some(factors)
    }

    /// `range` / `closed_range` (possibly several parameters) or exactly one parameter with type
    /// `cart({...}, {...}, ...)` (each factor must be a list set; at least two factors).
    pub fn expansion(&self) -> Result<ByForExpansion, String> {
        let groups = &self.forall_fact.params_def_with_type.groups;
        if groups.is_empty() {
            return Err("by for: forall must declare at least one parameter".to_string());
        }

        if groups.len() == 1 && groups[0].params.len() == 1 {
            if let ParamType::Obj(obj) = &groups[0].param_type {
                if let Some(factors) = Self::cart_factors_if_all_list_sets(obj) {
                    if factors.len() < 2 {
                        return Err(
                            "by for: cart(...) domain needs at least two list-set factors"
                                .to_string(),
                        );
                    }
                    return Ok(ByForExpansion::CartOfListSets {
                        param: groups[0].params[0].clone(),
                        factors,
                    });
                }
            }
        }

        let mut params = Vec::new();
        let mut ranges = Vec::new();
        for g in groups.iter() {
            let set = match &g.param_type {
                ParamType::Obj(Obj::Range(r)) => ClosedRangeOrRange::Range(r.clone()),
                ParamType::Obj(Obj::ClosedRange(c)) => ClosedRangeOrRange::ClosedRange(c.clone()),
                _ => {
                    return Err(
                        "by for: each forall parameter type must be range, closed_range, or use a single parameter with type cart({...}, ...) of list sets".to_string(),
                    );
                }
            };
            for name in g.params.iter() {
                params.push(name.clone());
                ranges.push(set.clone());
            }
        }
        if params.is_empty() {
            return Err("by for: forall must declare at least one parameter".to_string());
        }
        Ok(ByForExpansion::Ranges { params, ranges })
    }

    pub fn to_corresponding_forall_fact(&self) -> Result<Fact, String> {
        self.expansion()?;
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
