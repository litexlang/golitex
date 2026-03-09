use std::fmt;
use crate::keywords::{CASE, CASES, CLAIM, COLON, CONTRA, ENUM, FOR, FROM, INDUC, PROVE, RIGHT_ARROW, EQUAL_SET, EQUAL, IMPOSSIBLE, VIEW_FN_AS_SET};
use crate::helper::{add_four_spaces_at_beginning, to_string_and_add_four_spaces_at_beginning_of_each_line, vec_pair_to_string, vec_to_string_add_four_spaces_at_beginning_of_each_line};
use crate::fact::AndFactOrSpecFact;
use crate::fact::Fact;
use crate::fact::OrFactOrAndFactOrSpecFact;
use super::Stmt;
use crate::obj::{ClosedRange, Obj, Range };

pub enum ProofTechniqueStmt {
    ProveCaseByCase(ProveCaseByCaseStmt),
    ProveByContradiction(ProveByContradictionStmt),
    ProveByEnumeration(ProveByEnumerationStmt),
    ProveByInduction(ProveByInductionStmt),
    ProveForStmt(ProveForStmt),
    ProveByEqualSet(ProveByEqualSetStmt),
    ViewFnAsSet(ViewFnAsSetStmt),
}

// f $in fn(A, B) C => forall a A, b B => ((a, b), f(a, b)) $in f; forall x f: exist a A, b B st ((a, b), f(a, b)) = x
// f $in fn(a A, b B: $p(a, b)) C {$q(a, b, f)} => forall a A, b B: $p(a, b) => ((a, b), f(a, b)) $in f; forall x f: exist a A, b B st {$p(a, b), ((a, b), f(a, b)) = x}
pub struct ViewFnAsSetStmt {
    pub function: Obj,
    pub line_file_index: Option<(usize, usize)>,
}


pub struct ProveByEqualSetStmt {
    pub left: Obj,
    pub right: Obj,
    pub proof: Vec<Stmt>,
    pub line_file_index: Option<(usize, usize)>,
}


pub enum ClosedRangeOrRange {
    ClosedRange(ClosedRange),
    Range(Range),
}

pub struct ProveForStmt {
    pub params: Vec<String>,
    pub param_sets: Vec<ClosedRangeOrRange>,
    pub dom_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub then_facts: Vec<OrFactOrAndFactOrSpecFact>,
    pub proof: Vec<Stmt>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct ProveByInductionStmt {
    pub fact: Vec<OrFactOrAndFactOrSpecFact>,
    pub param: String,
    pub proof: Vec<Stmt>,
    pub induc_from: Obj,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct ProveByEnumerationStmt {
    pub params: Vec<String>,
    pub param_sets: Vec<Obj>,
    pub to_prove: Vec<Fact>,
    pub proof: Vec<Stmt>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct ProveCaseByCaseStmt {
    pub cases: Vec<AndFactOrSpecFact>,
    pub then_facts: Vec<Fact>,
    pub proofs: Vec<Vec<Stmt>>,
    pub impossible_facts: Vec<Option<OrFactOrAndFactOrSpecFact>>,
    pub line_file_index: Option<(usize, usize)>,
}

pub struct ProveByContradictionStmt {
    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
    pub impossible_fact: OrFactOrAndFactOrSpecFact,
    pub line_file_index: Option<(usize, usize)>,
}


impl ProveByEnumerationStmt {
    pub fn new(params: Vec<String>, param_sets: Vec<Obj>, to_prove: Vec<Fact>, proof: Vec<Stmt>, line_file_index: Option<(usize, usize)>) -> Self {
        ProveByEnumerationStmt { params, param_sets, to_prove, proof, line_file_index }
    }
}

impl ProveCaseByCaseStmt {
    pub fn new(cases: Vec<AndFactOrSpecFact>, then_facts: Vec<Fact>, proofs: Vec<Vec<Stmt>>, impossible_facts: Vec<Option<OrFactOrAndFactOrSpecFact>>, line_file_index: Option<(usize, usize)>) -> Self {
        ProveCaseByCaseStmt { cases, then_facts, proofs, impossible_facts, line_file_index }
    }
}

impl fmt::Display for ProveCaseByCaseStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let case_and_proof_of_each_case = self.cases.iter().zip(self.proofs.iter()).zip(self.impossible_facts.iter()).map(|((case, proof), impossible_fact)| {
            if let Some(impossible_fact) = impossible_fact {
                format!("{} {}{}\n{}\n{} {}", add_four_spaces_at_beginning(CASE, 1),case, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2), add_four_spaces_at_beginning(IMPOSSIBLE, 2), &impossible_fact.to_string())
            } else {
                format!("{} {}{}\n{}", add_four_spaces_at_beginning(CASE, 1),case, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2))
            }
        }).collect::<Vec<String>>();
        
        write!(f, "{}{}\n{}\n{}", CASES, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1), case_and_proof_of_each_case.join("\n"))
    }
}

impl ProveByContradictionStmt {
    pub fn new(to_prove: Fact, proof: Vec<Stmt>, impossible_fact: OrFactOrAndFactOrSpecFact, line_file_index: Option<(usize, usize)>) -> Self {
        ProveByContradictionStmt { to_prove, proof, impossible_fact, line_file_index }
    }
}

impl fmt::Display for ProveByContradictionStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}\n{}\n{}{}\n{}\n{} {}", CLAIM, COLON,to_string_and_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1),add_four_spaces_at_beginning(CONTRA, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2), add_four_spaces_at_beginning(IMPOSSIBLE, 2), &self.impossible_fact.to_string())
    }
}

impl fmt::Display for ProofTechniqueStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofTechniqueStmt::ProveCaseByCase(prove_case_by_case) => write!(f, "{}", prove_case_by_case),
            ProofTechniqueStmt::ProveByContradiction(prove_by_contradiction_stmt) => write!(f, "{}", prove_by_contradiction_stmt),
            ProofTechniqueStmt::ProveByEnumeration(prove_by_enumeration_stmt) => write!(f, "{}", prove_by_enumeration_stmt),
            ProofTechniqueStmt::ProveByInduction(prove_by_induction_stmt) => write!(f, "{}", prove_by_induction_stmt),
            ProofTechniqueStmt::ProveForStmt(prove_for_stmt) => write!(f, "{}", prove_for_stmt),
            ProofTechniqueStmt::ProveByEqualSet(prove_equal_set_stmt) => write!(f, "{}", prove_equal_set_stmt),
            ProofTechniqueStmt::ViewFnAsSet(prove_fn_is_set_stmt) => write!(f, "{}", prove_fn_is_set_stmt),
        }
    }
}

impl ProofTechniqueStmt {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            ProofTechniqueStmt::ProveCaseByCase(prove_case_by_case) => prove_case_by_case.line_file_index,
            ProofTechniqueStmt::ProveByContradiction(claim_prove_by_contradiction_stmt) => claim_prove_by_contradiction_stmt.line_file_index,
            ProofTechniqueStmt::ProveByEnumeration(prove_by_enumeration_stmt) => prove_by_enumeration_stmt.line_file_index,
            ProofTechniqueStmt::ProveByInduction(prove_by_induction_stmt) => prove_by_induction_stmt.line_file_index,
            ProofTechniqueStmt::ProveForStmt(prove_for_stmt) => prove_for_stmt.line_file_index,
            ProofTechniqueStmt::ProveByEqualSet(prove_equal_set_stmt) => prove_equal_set_stmt.line_file_index,
            ProofTechniqueStmt::ViewFnAsSet(prove_fn_is_set_stmt) => prove_fn_is_set_stmt.line_file_index,
        }
    }
}

impl fmt::Display for ProveByEnumerationStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}{}\n{}\n{}{}\n{}", ENUM, vec_pair_to_string(&self.params, &self.param_sets), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1), add_four_spaces_at_beginning(PROVE, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}

impl ProveByInductionStmt {
    pub fn new(fact: Vec<OrFactOrAndFactOrSpecFact>, param: String, proof: Vec<Stmt>, induc_from: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        ProveByInductionStmt { fact, param, proof, induc_from, line_file_index }
    }
}

impl fmt::Display for ProveByInductionStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} {}{}\n{}\n{}{}\n{}", INDUC, self.param, FROM, self.induc_from, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.fact, 1), add_four_spaces_at_beginning(PROVE, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2))
    }
}

impl fmt::Display for ProveForStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let head = match self.dom_facts.len() {
            0 => format!("{} {}{}\n{}", FOR, vec_pair_to_string(&self.params, &self.param_sets), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1)),
            _ => format!("{} {}{}\n{}\n{}{}\n{}", FOR, vec_pair_to_string(&self.params, &self.param_sets), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.dom_facts, 1), add_four_spaces_at_beginning(RIGHT_ARROW, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 2)),
        };

        match self.proof.len() {
            0 => write!(f, "{}", head),
            _ => write!(f, "{}\n{}{}\n{}", head, add_four_spaces_at_beginning(PROVE, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2)),
        }
    }
}

impl ProveForStmt {
    pub fn new(params: Vec<String>, param_sets: Vec<ClosedRangeOrRange>, dom_facts: Vec<OrFactOrAndFactOrSpecFact>, then_facts: Vec<OrFactOrAndFactOrSpecFact>, proof: Vec<Stmt>, line_file_index: Option<(usize, usize)>) -> Self {
        ProveForStmt { params, param_sets, dom_facts, then_facts, proof, line_file_index }
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

impl fmt::Display for ProveByEqualSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.proof.len() {
            0 => write!(f, "{} {} {} {}", EQUAL_SET, self.left, EQUAL, self.right),
            _ => write!(f, "{} {} {} {}{}\n{}", EQUAL_SET, self.left, EQUAL, self.right, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)),
        }
    }
}

impl ProveByEqualSetStmt {
    pub fn new(left: Obj, right: Obj, proof: Vec<Stmt>, line_file_index: Option<(usize, usize)>) -> Self {
        ProveByEqualSetStmt { left, right, proof, line_file_index }
    }
}

impl fmt::Display for ViewFnAsSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", VIEW_FN_AS_SET, self.function)
    }
}

impl ViewFnAsSetStmt {
    pub fn new(function: Obj, line_file_index: Option<(usize, usize)>) -> Self {
        ViewFnAsSetStmt { function, line_file_index }
    }
}

