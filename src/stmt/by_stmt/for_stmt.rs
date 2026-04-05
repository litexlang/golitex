use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum ClosedRangeOrRange {
    ClosedRange(ClosedRange),
    Range(Range),
}

/// Prove facts for parameters ranging over `range` / `closed_range` (`by for …`).
#[derive(Clone)]
pub struct ByForStmt {
    pub params: Vec<String>,
    pub param_sets: Vec<ClosedRangeOrRange>,
    pub dom_facts: Vec<AtomicFact>,
    pub then_facts: Vec<ExistOrAndChainAtomicFact>,
    pub proof: Vec<Stmt>,
    pub line_file: LineFile,
}

impl fmt::Display for ByForStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let head = match self.dom_facts.len() {
            0 => format!(
                "{} {} {}{}\n{}",
                BY,
                FOR,
                vec_pair_to_string(&self.params, &self.param_sets),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1)
            ),
            _ => format!(
                "{} {} {}{}\n{}\n{}{}\n{}",
                BY,
                FOR,
                vec_pair_to_string(&self.params, &self.param_sets),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.dom_facts, 1),
                add_four_spaces_at_beginning(RIGHT_ARROW.to_string(), 1),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 2)
            ),
        };

        match self.proof.len() {
            0 => write!(f, "{}", head),
            _ => write!(
                f,
                "{}\n{}{}\n{}",
                head,
                add_four_spaces_at_beginning(PROVE.to_string(), 1),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2)
            ),
        }
    }
}

impl ByForStmt {
    pub fn to_corresponding_forall_fact(&self) -> Result<Fact, String> {
        if self.params.len() != self.param_sets.len() {
            return Err("by for: number of params does not match number of param sets".to_string());
        }
        let mut params_def_with_type: Vec<ParamGroupWithParamType> = Vec::new();
        for (param_name, param_set) in self.params.iter().zip(self.param_sets.iter()) {
            let param_set_as_obj = match param_set {
                ClosedRangeOrRange::ClosedRange(closed_range) => {
                    Obj::ClosedRange(closed_range.clone())
                }
                ClosedRangeOrRange::Range(range) => Obj::Range(range.clone()),
            };
            params_def_with_type.push(ParamGroupWithParamType::new(
                vec![param_name.clone()],
                ParamType::Obj(param_set_as_obj),
            ));
        }
        Ok(Fact::ForallFact(ForallFact::new(
            params_def_with_type,
            self.dom_facts
                .iter()
                .map(|atomic_fact| ExistOrAndChainAtomicFact::AtomicFact(atomic_fact.clone()))
                .collect(),
            self.then_facts.clone(),
            self.line_file.clone(),
        )))
    }

    pub fn new(
        params: Vec<String>,
        param_sets: Vec<ClosedRangeOrRange>,
        dom_facts: Vec<AtomicFact>,
        then_facts: Vec<ExistOrAndChainAtomicFact>,
        proof: Vec<Stmt>,
        line_file: LineFile,
    ) -> Self {
        ByForStmt {
            params,
            param_sets,
            dom_facts,
            then_facts,
            proof,
            line_file,
        }
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
