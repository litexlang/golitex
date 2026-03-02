use crate::helper::{vec_pair_to_string, vec_to_string_add_four_spaces_at_beginning_of_each_line, vec_to_string_join_by_comma, vec_to_string_with_sep};
use crate::parameter_type_and_property::ParameterType;
use std::fmt;
use crate::obj::Obj;
use crate::atomic_fact::AtomicFact;
use crate::stmt::Stmt;
use crate::consts::{COLON, COMMA, ST, WITNESS};

pub enum WitnessStmt {
    WitnessExistFact(WitnessExistFact),
    WitnessNonemptySet(WitnessNonemptySet),
}

pub struct WitnessNonemptySet {
    pub obj: Obj,
    pub set: Obj,
    pub proof: Vec<Stmt>,
    pub line: u32,
    pub file_index: usize,
}

pub struct WitnessExistFact {
    pub exist_params: Vec<String>,
    pub param_types: Vec<ParameterType>,
    pub equal_tos: Vec<Obj>,
    pub facts: Vec<AtomicFact>,
    pub proof: Vec<Stmt>,
    pub line: u32,
    pub file_index: usize,
}

impl WitnessExistFact {
    pub fn new(exist_params: Vec<String>, param_types: Vec<ParameterType>, equal_tos: Vec<Obj>, facts: Vec<AtomicFact>, proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        WitnessExistFact { exist_params, param_types, equal_tos, facts, proof, line, file_index }
    }
}

impl fmt::Display for WitnessExistFact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.proof.len() {
            0 => write!(f, "{} {}{} {} {} {}", WITNESS, vec_to_string_with_sep(&self.equal_tos, COMMA), COLON, vec_pair_to_string(&self.exist_params, &self.param_types), ST, vec_to_string_join_by_comma(&self.facts)),
            _ => write!(f, "{} {}{} {} {} {} {}\n{}", WITNESS, vec_to_string_with_sep(&self.equal_tos, COMMA), COLON, vec_pair_to_string(&self.exist_params, &self.param_types), ST, vec_to_string_join_by_comma(&self.facts), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)),
        }   
    }
}

impl WitnessStmt {
    pub fn line_file(&self) -> (u32, usize) {
        match self {
            WitnessStmt::WitnessExistFact(witness_exist_fact) => (witness_exist_fact.line, witness_exist_fact.file_index),
            WitnessStmt::WitnessNonemptySet(witness_nonempty_set) => (witness_nonempty_set.line, witness_nonempty_set.file_index),
        }
    }
}

impl fmt::Display for WitnessStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WitnessStmt::WitnessExistFact(witness_exist_fact) => write!(f, "{}", witness_exist_fact),
            WitnessStmt::WitnessNonemptySet(witness_nonempty_set) => write!(f, "{}", witness_nonempty_set),
        }
    }
}

impl fmt::Display for WitnessNonemptySet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.proof.len() {
            0 => write!(f, "{} {} {}", WITNESS, self.obj, self.set),
            _ => write!(f, "{} {} {}{}\n{}", WITNESS, self.obj, self.set, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)),
        }
    }
}

impl WitnessNonemptySet {
    pub fn new(obj: Obj, set: Obj, proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        WitnessNonemptySet { obj, set, proof, line, file_index }
    }
}