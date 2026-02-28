use std::fmt;
use crate::consts::{CLAIM, COLON, CONTRA, CASES, CASE};
use crate::helper::{to_string_and_add_four_spaces_at_beginning_of_each_line, vec_to_string_add_four_spaces_at_beginning_of_each_line, add_four_spaces_at_beginning};
use crate::and_fact_or_specific_fact::AndFactOrSpecFact;
use crate::fact::Fact;
use crate::stmt::Stmt;

pub enum ProofTechnique {
    ProveCaseByCase(ProveCaseByCase),
    ClaimProveByContradiction(ClaimProveByContradictionStmt),
}

pub struct ProveCaseByCase {
    pub cases: Vec<AndFactOrSpecFact>,
    pub then_facts: Vec<Fact>,
    pub proofs: Vec<Vec<Stmt>>,
    pub line: u32,
    pub file_index: usize,
}

pub struct ClaimProveByContradictionStmt {
    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
    pub line: u32,
    pub file_index: usize,
}


impl ProveCaseByCase {
    pub fn new(cases: Vec<AndFactOrSpecFact>, then_facts: Vec<Fact>, proofs: Vec<Vec<Stmt>>, line: u32, file_index: usize) -> Self {
        ProveCaseByCase { cases, then_facts, proofs, line, file_index }
    }
}

impl fmt::Display for ProveCaseByCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let case_and_proof_of_each_case = self.cases.iter().zip(self.proofs.iter()).map(|(case, proof)| format!("{} {}{}\n{}", CASE,case, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2))).collect::<Vec<String>>();
        
        write!(f, "{}{}\n{}\n{}", CASES, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1), case_and_proof_of_each_case.join("\n"))
    }
}

impl ClaimProveByContradictionStmt {
    pub fn new(to_prove: Fact, proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        ClaimProveByContradictionStmt { to_prove, proof, line, file_index }
    }
}

impl fmt::Display for ClaimProveByContradictionStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}\n{}\n{}{}\n{}", CLAIM, COLON,to_string_and_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1),add_four_spaces_at_beginning(CONTRA, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}

impl fmt::Display for ProofTechnique {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofTechnique::ProveCaseByCase(prove_case_by_case) => write!(f, "{}", prove_case_by_case),
            ProofTechnique::ClaimProveByContradiction(claim_prove_by_contradiction_stmt) => write!(f, "{}", claim_prove_by_contradiction_stmt),
        }
    }
}

impl ProofTechnique {
    pub fn line_file(&self) -> (u32, usize) {
        match self {
            ProofTechnique::ProveCaseByCase(prove_case_by_case) => (prove_case_by_case.line, prove_case_by_case.file_index),
            ProofTechnique::ClaimProveByContradiction(claim_prove_by_contradiction_stmt) => (claim_prove_by_contradiction_stmt.line, claim_prove_by_contradiction_stmt.file_index),
        }
    }
}