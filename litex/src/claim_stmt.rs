use std::fmt;
use crate::consts::{CLAIM, COLON, PROVE, CONTRA};
use crate::fact::Fact;
use crate::helper::{to_string_and_add_four_spaces_at_beginning_of_each_line,  vec_to_str_add_four_spaces_at_beginning_of_each_line};
use crate::stmt::Stmt;

pub enum ClaimStmt {
    Prove(ClaimProveStmt),
    ProveByContradiction(ClaimProveByContradictionStmt),
}

pub struct ClaimProveStmt {
    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
}

pub struct ClaimProveByContradictionStmt {
    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
}

impl ClaimProveStmt {
    pub fn new(to_prove: Fact, proof: Vec<Stmt>) -> Self {
        ClaimProveStmt { to_prove, proof }
    }
}

impl ClaimProveByContradictionStmt {
    pub fn new(to_prove: Fact, proof: Vec<Stmt>) -> Self {
        ClaimProveByContradictionStmt { to_prove, proof }
    }
}

impl fmt::Display for ClaimStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClaimStmt::Prove(claim_prove_stmt) => write!(f, "{}", claim_prove_stmt),
            ClaimStmt::ProveByContradiction(claim_prove_by_contradiction_stmt) => write!(f, "{}", claim_prove_by_contradiction_stmt),
        }
    }
}

impl fmt::Display for ClaimProveStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}\n{}\n{}{}\n{}", CLAIM, COLON,to_string_and_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1), PROVE, COLON, vec_to_str_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}

impl fmt::Display for ClaimProveByContradictionStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}\n{}\n{}{}\n{}", CLAIM, COLON,to_string_and_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1), CONTRA, COLON, vec_to_str_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}