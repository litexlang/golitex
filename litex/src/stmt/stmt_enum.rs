use std::fmt;
use crate::fact::Fact;
use super::definition_stmt::{
    DefLetStmt, DefPropStmt, DefPropWithoutMeaningStmt, DefStructWithFieldsStmt, DefStructWithNoFieldStmt,
    HaveObjInNonemptySetOrParamTypeStmt, HaveObjEqualStmt, HaveExistObjStmt, HaveFnEqualStmt, HaveFnEqualCaseByCaseStmt,
};
use super::define_algorithm_stmt::DefAlgoStmt;
use super::claim_stmt::ClaimStmt;
use super::know_stmt::KnowStmt;
use super::proof_technique_stmt::{
    ProveCaseByCaseStmt, ProveByContradictionStmt, ProveByEnumerationStmt, ProveByInductionStmt,
    ProveForStmt, ProveByEqualSetStmt, ViewFnAsSetStmt,
};
use super::tooling_stmt::ToolingStmt;
use super::prove_stmt::ProveStmt;
use super::eval_stmt::EvalStmt;
use super::witness_stmt::{WitnessExistFact, WitnessNonemptySet};

pub enum Stmt {
    Fact(Fact),
    DefLetStmt(DefLetStmt),
    DefPropStmt(DefPropStmt),
    DefPropWithoutMeaningStmt(DefPropWithoutMeaningStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveExistObjStmt(HaveExistObjStmt),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    DefStructWithFieldsStmt(DefStructWithFieldsStmt),
    DefStructWithNoFieldStmt(DefStructWithNoFieldStmt),
    DefAlgoStmt(DefAlgoStmt),
    ClaimStmt(ClaimStmt),
    KnowStmt(KnowStmt),
    ProveStmt(ProveStmt),
    ToolingStmt(ToolingStmt),
    EvalStmt(EvalStmt),
    WitnessExistFact(WitnessExistFact),
    WitnessNonemptySet(WitnessNonemptySet),
    ProveCaseByCaseStmt(ProveCaseByCaseStmt),
    ProveByContradictionStmt(ProveByContradictionStmt),
    ProveByEnumerationStmt(ProveByEnumerationStmt),
    ProveByInductionStmt(ProveByInductionStmt),
    ProveForStmt(ProveForStmt),
    ProveByEqualSetStmt(ProveByEqualSetStmt),
    ViewFnAsSetStmt(ViewFnAsSetStmt),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Fact(x) => write!(f, "{}", x),
            Stmt::DefLetStmt(x) => write!(f, "{}", x),
            Stmt::DefPropStmt(x) => write!(f, "{}", x),
            Stmt::DefPropWithoutMeaningStmt(x) => write!(f, "{}", x),
            Stmt::HaveObjInNonemptySetStmt(x) => write!(f, "{}", x),
            Stmt::HaveObjEqualStmt(x) => write!(f, "{}", x),
            Stmt::HaveExistObjStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnEqualStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnEqualCaseByCaseStmt(x) => write!(f, "{}", x),
            Stmt::DefStructWithFieldsStmt(x) => write!(f, "{}", x),
            Stmt::DefStructWithNoFieldStmt(x) => write!(f, "{}", x),
            Stmt::DefAlgoStmt(x) => write!(f, "{}", x),
            Stmt::ClaimStmt(x) => write!(f, "{}", x),
            Stmt::KnowStmt(x) => write!(f, "{}", x),
            Stmt::ProveStmt(x) => write!(f, "{}", x),
            Stmt::ToolingStmt(x) => write!(f, "{}", x),
            Stmt::EvalStmt(x) => write!(f, "{}", x),
            Stmt::WitnessExistFact(x) => write!(f, "{}", x),
            Stmt::WitnessNonemptySet(x) => write!(f, "{}", x),
            Stmt::ProveCaseByCaseStmt(x) => write!(f, "{}", x),
            Stmt::ProveByContradictionStmt(x) => write!(f, "{}", x),
            Stmt::ProveByEnumerationStmt(x) => write!(f, "{}", x),
            Stmt::ProveByInductionStmt(x) => write!(f, "{}", x),
            Stmt::ProveForStmt(x) => write!(f, "{}", x),
            Stmt::ProveByEqualSetStmt(x) => write!(f, "{}", x),
            Stmt::ViewFnAsSetStmt(x) => write!(f, "{}", x),
        }
    }
}

impl Stmt {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            Stmt::Fact(x) => x.line_file(),
            Stmt::DefLetStmt(x) => x.line_file_index,
            Stmt::DefPropStmt(x) => x.line_file_index,
            Stmt::DefPropWithoutMeaningStmt(x) => x.line_file_index,
            Stmt::HaveObjInNonemptySetStmt(x) => x.line_file_index,
            Stmt::HaveObjEqualStmt(x) => x.line_file_index,
            Stmt::HaveExistObjStmt(x) => x.line_file_index,
            Stmt::HaveFnEqualStmt(x) => x.line_file_index,
            Stmt::HaveFnEqualCaseByCaseStmt(x) => x.line_file_index,
            Stmt::DefStructWithFieldsStmt(x) => x.line_file_index,
            Stmt::DefStructWithNoFieldStmt(x) => x.line_file_index,
            Stmt::DefAlgoStmt(x) => x.line_file_index,
            Stmt::ClaimStmt(x) => x.line_file(),
            Stmt::KnowStmt(x) => x.line_file_index,
            Stmt::ProveStmt(x) => x.line_file_index,
            Stmt::ToolingStmt(x) => x.line_file(),
            Stmt::EvalStmt(x) => x.line_file_index,
            Stmt::WitnessExistFact(x) => x.line_file_index,
            Stmt::WitnessNonemptySet(x) => x.line_file_index,
            Stmt::ProveCaseByCaseStmt(x) => x.line_file_index,
            Stmt::ProveByContradictionStmt(x) => x.line_file_index,
            Stmt::ProveByEnumerationStmt(x) => x.line_file_index,
            Stmt::ProveByInductionStmt(x) => x.line_file_index,
            Stmt::ProveForStmt(x) => x.line_file_index,
            Stmt::ProveByEqualSetStmt(x) => x.line_file_index,
            Stmt::ViewFnAsSetStmt(x) => x.line_file_index,
        }
    }
}
