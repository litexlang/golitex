use std::fmt;
use crate::consts::{CLAIM, COLON, CONTRA, CASES, CASE, ENUM, PROVE, INDUC, FROM};
use crate::helper::{add_four_spaces_at_beginning, to_string_and_add_four_spaces_at_beginning_of_each_line, vec_pair_to_string, vec_to_string_add_four_spaces_at_beginning_of_each_line};
use crate::and_fact_or_specific_fact::AndFactOrSpecFact;
use crate::fact::Fact;
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::stmt::Stmt;
use crate::obj::{Obj, ClosedRange, Range};

pub enum ProveByBuiltinTechniqueStmt {
    ProveCaseByCase(ProveCaseByCase),
    ProveByContradiction(ProveByContradictionStmt),
    ProveByEnumeration(ProveByEnumerationStmt),
    ProveByInduction(ProveByInductionStmt),
    ProveForStmt(ProveForStmt),
}


pub enum ClosedRangeOrRange {
    ClosedRange(ClosedRange),
    Range(Range),
}
pub struct ProveForStmt {
    pub params: Vec<String>,
    pub param_sets: ClosedRangeOrRange,
    pub dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub then_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub proof: Vec<Stmt>,
    pub line: u32,
    pub file_index: usize,
}

pub struct ProveByInductionStmt {
    pub fact: Vec<OrFactOrAndFactOrSpecFact>,
    pub param: String,
    pub proof: Vec<Stmt>,
    pub induc_from: Obj,
    pub line: u32,
    pub file_index: usize,
}

pub struct ProveByEnumerationStmt {
    pub params: Vec<String>,
    pub param_sets: Vec<Obj>,
    pub to_prove: Vec<Fact>,
    pub proof: Vec<Stmt>,
    pub line: u32,
    pub file_index: usize,
}

pub struct ProveCaseByCase {
    pub cases: Vec<AndFactOrSpecFact>,
    pub then_facts: Vec<Fact>,
    pub proofs: Vec<Vec<Stmt>>,
    pub line: u32,
    pub file_index: usize,
}

pub struct ProveByContradictionStmt {
    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
    pub line: u32,
    pub file_index: usize,
}


impl ProveByEnumerationStmt {
    pub fn new(params: Vec<String>, param_sets: Vec<Obj>, to_prove: Vec<Fact>, proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        ProveByEnumerationStmt { params, param_sets, to_prove, proof, line, file_index }
    }
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

impl ProveByContradictionStmt {
    pub fn new(to_prove: Fact, proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        ProveByContradictionStmt { to_prove, proof, line, file_index }
    }
}

impl fmt::Display for ProveByContradictionStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}\n{}\n{}{}\n{}", CLAIM, COLON,to_string_and_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1),add_four_spaces_at_beginning(CONTRA, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}

impl fmt::Display for ProveByBuiltinTechniqueStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProveByBuiltinTechniqueStmt::ProveCaseByCase(prove_case_by_case) => write!(f, "{}", prove_case_by_case),
            ProveByBuiltinTechniqueStmt::ProveByContradiction(prove_by_contradiction_stmt) => write!(f, "{}", prove_by_contradiction_stmt),
            ProveByBuiltinTechniqueStmt::ProveByEnumeration(prove_by_enumeration_stmt) => write!(f, "{}", prove_by_enumeration_stmt),
            ProveByBuiltinTechniqueStmt::ProveByInduction(prove_by_induction_stmt) => write!(f, "{}", prove_by_induction_stmt),
            ProveByBuiltinTechniqueStmt::ProveForStmt(prove_for_stmt) => write!(f, "{}", prove_for_stmt),
        }
    }
}

impl ProveByBuiltinTechniqueStmt {
    pub fn line_file(&self) -> (u32, usize) {
        match self {
            ProveByBuiltinTechniqueStmt::ProveCaseByCase(prove_case_by_case) => (prove_case_by_case.line, prove_case_by_case.file_index),
            ProveByBuiltinTechniqueStmt::ProveByContradiction(claim_prove_by_contradiction_stmt) => (claim_prove_by_contradiction_stmt.line, claim_prove_by_contradiction_stmt.file_index),
            ProveByBuiltinTechniqueStmt::ProveByEnumeration(prove_by_enumeration_stmt) => (prove_by_enumeration_stmt.line, prove_by_enumeration_stmt.file_index),
            ProveByBuiltinTechniqueStmt::ProveByInduction(prove_by_induction_stmt) => (prove_by_induction_stmt.line, prove_by_induction_stmt.file_index),
            ProveByBuiltinTechniqueStmt::ProveForStmt(prove_for_stmt) => (prove_for_stmt.line, prove_for_stmt.file_index),
        }
    }
}

impl fmt::Display for ProveByEnumerationStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}\n{}\n{}{}\n{}", ENUM, vec_pair_to_string(&self.params, &self.param_sets), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1), add_four_spaces_at_beginning(PROVE, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}

impl ProveByInductionStmt {
    pub fn new(fact: Vec<OrFactOrAndFactOrSpecFact>, param: String, proof: Vec<Stmt>, induc_from: Obj, line: u32, file_index: usize) -> Self {
        ProveByInductionStmt { fact, param, proof, induc_from, line, file_index }
    }
}

impl fmt::Display for ProveByInductionStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}{}\n{}\n{}{}\n{}", INDUC, self.param, FROM, self.induc_from, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.fact, 1), add_four_spaces_at_beginning(PROVE, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}

impl fmt::Display for ProveForStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        panic!("ProveForStmt is not implemented");
    }
}

impl ProveForStmt {
    pub fn new(params: Vec<String>, param_sets: ClosedRangeOrRange, dom_facts: Vec<OrFactOrAndFactOrSpecFact>, then_facts: Vec<OrFactOrAndFactOrSpecFact>, proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        ProveForStmt { params, param_sets, dom_facts, then_facts, proof, line, file_index }
    }
}