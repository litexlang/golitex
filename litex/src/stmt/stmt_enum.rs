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
use super::tooling_stmt::{ImportStmt, ClearStmt, DoNothingStmt, RunFileStmt};
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
    ImportStmt(ImportStmt),
    ClearStmt(ClearStmt),
    DoNothingStmt(DoNothingStmt),
    RunFileStmt(RunFileStmt),
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
            Stmt::ImportStmt(x) => write!(f, "{}", x),
            Stmt::ClearStmt(x) => write!(f, "{}", x),
            Stmt::DoNothingStmt(x) => write!(f, "{}", x),
            Stmt::RunFileStmt(x) => write!(f, "{}", x),
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

