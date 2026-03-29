use super::Stmt;
use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub struct WitnessNonemptySet {
    pub obj: Obj,
    pub set: Obj,
    pub proof: Vec<Stmt>,
    pub line_file: (usize, usize),
}

#[derive(Clone)]
pub struct WitnessExistFact {
    pub equal_tos: Vec<Obj>,
    pub exist_fact_in_witness: ExistFact,
    pub proof: Vec<Stmt>,
    pub line_file: (usize, usize),
}

impl WitnessExistFact {
    pub fn new(
        equal_tos: Vec<Obj>,
        exist_fact_in_witness: ExistFact,
        proof: Vec<Stmt>,
        line_file: (usize, usize),
    ) -> Self {
        WitnessExistFact {
            equal_tos,
            exist_fact_in_witness,
            proof,
            line_file,
        }
    }
}

impl fmt::Display for WitnessExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.proof.len() {
            0 => write!(
                f,
                "{} {}{} {} {} {}",
                WITNESS,
                vec_to_string_with_sep(&self.equal_tos, COMMA.to_string()),
                COLON,
                vec_to_string_join_by_comma(&self.exist_fact_in_witness.params_def_with_type),
                ST,
                vec_to_string_join_by_comma(&self.exist_fact_in_witness.facts)
            ),
            _ => write!(
                f,
                "{} {}{} {} {} {} {}\n{}",
                WITNESS,
                vec_to_string_with_sep(&self.equal_tos, COMMA.to_string()),
                COLON,
                vec_to_string_join_by_comma(&self.exist_fact_in_witness.params_def_with_type),
                ST,
                vec_to_string_join_by_comma(&self.exist_fact_in_witness.facts),
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
            ),
        }
    }
}

impl fmt::Display for WitnessNonemptySet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.proof.len() {
            0 => write!(f, "{} {} {}", WITNESS, self.obj, self.set),
            _ => write!(
                f,
                "{} {} {}{}\n{}",
                WITNESS,
                self.obj,
                self.set,
                COLON,
                vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)
            ),
        }
    }
}

impl WitnessNonemptySet {
    pub fn new(obj: Obj, set: Obj, proof: Vec<Stmt>, line_file: (usize, usize)) -> Self {
        WitnessNonemptySet {
            obj,
            set,
            proof,
            line_file,
        }
    }
}
