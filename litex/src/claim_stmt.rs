use std::fmt;
use crate::forall_fact_with_iff::ForallFactWithIff;
use crate::keywords::{CLAIM, COLON, PROVE};
use crate::fact::Fact;
use crate::helper::{to_string_and_add_four_spaces_at_beginning_of_each_line,  vec_to_string_add_four_spaces_at_beginning_of_each_line, add_four_spaces_at_beginning};
use crate::stmt::Stmt;

pub enum ClaimStmt {
    ClaimProveStmt(ClaimProveStmt),
    ClaimIffStmt(ClaimIffStmt),
}

pub struct ClaimIffStmt {
    pub to_prove: ForallFactWithIff,
    pub then_to_iff_proof: Vec<Stmt>,
    pub iff_to_then_proof: Vec<Stmt>,
    pub line_file_index: Option<(usize, usize)>,
}

impl ClaimIffStmt {
    pub fn new(to_prove: ForallFactWithIff, then_to_iff_proof: Vec<Stmt>, iff_to_then_proof: Vec<Stmt>, line_file_index: Option<(usize, usize)>) -> Self {
        ClaimIffStmt { to_prove, then_to_iff_proof, iff_to_then_proof, line_file_index }
    }
}

pub struct ClaimProveStmt {
    pub to_prove: Vec<Fact>,
    pub proof: Vec<Stmt>,
    pub line_file_index: Option<(usize, usize)>,
}

impl ClaimProveStmt {
    pub fn new(to_prove: Vec<Fact>, proof: Vec<Stmt>, line_file_index: Option<(usize, usize)>) -> Self {
        ClaimProveStmt { to_prove, proof, line_file_index }
    }
}

impl fmt::Display for ClaimProveStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}\n{}\n{}{}\n{}", CLAIM, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1), add_four_spaces_at_beginning(PROVE, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}

impl fmt::Display for ClaimStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClaimStmt::ClaimProveStmt(claim_prove_stmt) => write!(f, "{}", claim_prove_stmt),
            ClaimStmt::ClaimIffStmt(claim_iff_stmt) => write!(f, "{}", claim_iff_stmt),
        }
    }
}

impl ClaimStmt {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            ClaimStmt::ClaimProveStmt(claim_prove_stmt) => claim_prove_stmt.line_file_index,
            ClaimStmt::ClaimIffStmt(claim_iff_stmt) => claim_iff_stmt.line_file_index,
        }
    }
}

impl fmt::Display for ClaimIffStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}\n{}\n{}{}\n{}\n{}{}\n{}", CLAIM, COLON, to_string_and_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1), add_four_spaces_at_beginning(PROVE, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_to_iff_proof, 2), add_four_spaces_at_beginning(PROVE, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.iff_to_then_proof, 2))
    }
}