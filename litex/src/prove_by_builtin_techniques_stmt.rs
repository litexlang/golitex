use std::fmt;
use crate::atom::Atom;
use crate::consts::{CASE, CASES, CLAIM, COLON, CONTRA, ENUM, FOR, FROM, INDUC, PROVE, RIGHT_ARROW, EQUAL_SET, EQUAL, IMPOSSIBLE, FN_SET_AS_SET};
use crate::helper::{add_four_spaces_at_beginning, braced_vec_to_string, to_string_and_add_four_spaces_at_beginning_of_each_line, vec_pair_to_string, vec_to_string_add_four_spaces_at_beginning_of_each_line};
use crate::and_fact_or_specific_fact::AndFactOrSpecFact;
use crate::fact::Fact;
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::stmt::Stmt;
use crate::obj::{ClosedRange, FnSetObj, Obj, Range };

pub enum ProveByBuiltinTechniqueStmt {
    ProveCaseByCase(ProveCaseByCase),
    ProveByContradiction(ProveByContradictionStmt),
    ProveByEnumeration(ProveByEnumerationStmt),
    ProveByInduction(ProveByInductionStmt),
    ProveForStmt(ProveForStmt),
    ProveEqualSet(ProveEqualSetStmt),
    FnSetAsSet(ProveFnSetAsSetStmt),
}

// TODO: 改成 cart(A, B, C)
// fn f(A, B) C = {t cart(cart(A, B), C): forall x cart(A, B) => exist z t st st z[1] = x; forall x t, y t: x[1] = y[1] => x = y}
// fn f(a A, b B: $p(a, b)) C {$q(a, b, f)} = {t cart(cart(A, B), C): forall x cart(A, B) => exist z t st st z[1] = x; forall x t, y t: x[1] = y[1] => x = y; forall x t: $p(x[1][1], x[1][2]); forall x cart(A, B): $p(x[1], x[2]) => exist z t st st z[1] = x; forall z t: $q(z[1][1], z[1][2], t)}
// 这里的 forall x t: $p(x[1][1], x[1][2]) 可能表示不了，因为 $p 对 kernel 来说是变量，所以要让用户自己传入一个和这个fact等价的prop进来。
pub struct ProveFnSetAsSetStmt {
    pub props: Vec<Atom>,
    pub fn_obj: FnSetObj,
    pub line: u32,
    pub file_index: usize,
}


pub struct ProveEqualSetStmt {
    pub left: Obj,
    pub right: Obj,
    pub proof: Vec<Stmt>,
    pub line: u32,
    pub file_index: usize,
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
    pub impossible_facts: Vec<Option<OrFactOrAndFactOrSpecFact>>,
    pub line: u32,
    pub file_index: usize,
}

pub struct ProveByContradictionStmt {
    pub to_prove: Fact,
    pub proof: Vec<Stmt>,
    pub impossible_fact: OrFactOrAndFactOrSpecFact,
    pub line: u32,
    pub file_index: usize,
}


impl ProveByEnumerationStmt {
    pub fn new(params: Vec<String>, param_sets: Vec<Obj>, to_prove: Vec<Fact>, proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        ProveByEnumerationStmt { params, param_sets, to_prove, proof, line, file_index }
    }
}

impl ProveCaseByCase {
    pub fn new(cases: Vec<AndFactOrSpecFact>, then_facts: Vec<Fact>, proofs: Vec<Vec<Stmt>>, impossible_facts: Vec<Option<OrFactOrAndFactOrSpecFact>>, line: u32, file_index: usize) -> Self {
        ProveCaseByCase { cases, then_facts, proofs, impossible_facts, line, file_index }
    }
}

impl fmt::Display for ProveCaseByCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 还要考虑：如果这一位的 impossible_fact 是 None，则不输出 impossible_fact；否则再在后面一行写上 impossible ...
        let case_and_proof_of_each_case = self.cases.iter().zip(self.proofs.iter()).zip(self.impossible_facts.iter()).map(|((case, proof), impossible_fact)| {
            if let Some(impossible_fact) = impossible_fact {
                format!("{} {}{}\n{}\n{} {}", CASE,case, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2), IMPOSSIBLE, add_four_spaces_at_beginning(&impossible_fact.to_string(), 2))
            } else {
                format!("{} {}{}\n{}", CASE,case, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(proof, 2))
            }
        }).collect::<Vec<String>>();
        
        write!(f, "{}{}\n{}\n{}", CASES, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.then_facts, 1), case_and_proof_of_each_case.join("\n"))
    }
}

impl ProveByContradictionStmt {
    pub fn new(to_prove: Fact, proof: Vec<Stmt>, impossible_fact: OrFactOrAndFactOrSpecFact, line: u32, file_index: usize) -> Self {
        ProveByContradictionStmt { to_prove, proof, impossible_fact, line, file_index }
    }
}

impl fmt::Display for ProveByContradictionStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}\n{}\n{}{}\n{}\n{} {}", CLAIM, COLON,to_string_and_add_four_spaces_at_beginning_of_each_line(&self.to_prove, 1),add_four_spaces_at_beginning(CONTRA, 1), COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 2), IMPOSSIBLE, add_four_spaces_at_beginning(&self.impossible_fact.to_string(), 2))
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
            ProveByBuiltinTechniqueStmt::ProveEqualSet(prove_equal_set_stmt) => write!(f, "{}", prove_equal_set_stmt),
            ProveByBuiltinTechniqueStmt::FnSetAsSet(prove_fn_is_set_stmt) => write!(f, "{}", prove_fn_is_set_stmt),
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
            ProveByBuiltinTechniqueStmt::ProveEqualSet(prove_equal_set_stmt) => (prove_equal_set_stmt.line, prove_equal_set_stmt.file_index),
            ProveByBuiltinTechniqueStmt::FnSetAsSet(prove_fn_is_set_stmt) => (prove_fn_is_set_stmt.line, prove_fn_is_set_stmt.file_index),
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
    pub fn new(params: Vec<String>, param_sets: Vec<ClosedRangeOrRange>, dom_facts: Vec<OrFactOrAndFactOrSpecFact>, then_facts: Vec<OrFactOrAndFactOrSpecFact>, proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        ProveForStmt { params, param_sets, dom_facts, then_facts, proof, line, file_index }
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

impl fmt::Display for ProveEqualSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.proof.len() {
            0 => write!(f, "{} {} {} {}", EQUAL_SET, self.left, EQUAL, self.right),
            _ => write!(f, "{} {} {} {}{}\n{}", EQUAL_SET, self.left, EQUAL, self.right, COLON, vec_to_string_add_four_spaces_at_beginning_of_each_line(&self.proof, 1)),
        }
    }
}

impl ProveEqualSetStmt {
    pub fn new(left: Obj, right: Obj, proof: Vec<Stmt>, line: u32, file_index: usize) -> Self {
        ProveEqualSetStmt { left, right, proof, line, file_index }
    }
}

impl fmt::Display for ProveFnSetAsSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{} {}", FN_SET_AS_SET, braced_vec_to_string(&self.props), self.fn_obj)
    }
}

impl ProveFnSetAsSetStmt {
    pub fn new(props: Vec<Atom>, fn_obj: FnSetObj, line: u32, file_index: usize) -> Self {
        ProveFnSetAsSetStmt { props, fn_obj, line, file_index }
    }
}