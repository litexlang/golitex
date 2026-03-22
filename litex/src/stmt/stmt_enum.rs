use super::axiom_stmt::{
    ByCartDefAxiomStmt, ByCasesAxiomStmt, ByContraAxiomStmt, ByExtensionAxiomStmt,
    ByFnDefAxiomStmt, ByInducAxiomStmt, EnumerateAxiomStmt, ForAxiomStmt,
};
use super::claim_stmt::ClaimStmt;
use super::define_algorithm_stmt::DefAlgoStmt;
use super::definition_stmt::{
    DefLetStmt, DefPropWithMeaningStmt, DefPropWithoutMeaningStmt, DefStructWithFieldsStmt,
    DefStructWithNoFieldStmt, HaveExistObjStmt, HaveFnEqualCaseByCaseStmt, HaveFnEqualStmt,
    HaveObjEqualStmt, HaveObjInNonemptySetOrParamTypeStmt,
};
use super::eval_stmt::EvalStmt;
use super::know_stmt::KnowStmt;
use super::prove_stmt::ProveStmt;
use super::tooling_stmt::{ClearStmt, DoNothingStmt, ImportStmt, RunFileStmt};
use super::witness_stmt::{WitnessExistFact, WitnessNonemptySet};
use crate::fact::Fact;
use std::fmt;

pub enum Stmt {
    Fact(Fact),
    DefLetStmt(DefLetStmt),
    DefPropWithMeaningStmt(DefPropWithMeaningStmt),
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
    ByCasesAxiomStmt(ByCasesAxiomStmt),
    ByContraAxiomStmt(ByContraAxiomStmt),
    EnumerateAxiomStmt(EnumerateAxiomStmt),
    ByInducAxiomStmt(ByInducAxiomStmt),
    ForAxiomStmt(ForAxiomStmt),
    ByExtensionAxiomStmt(ByExtensionAxiomStmt),
    ByFnDefAxiomStmt(ByFnDefAxiomStmt),
    ByCartDefAxiomStmt(ByCartDefAxiomStmt),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Fact(x) => write!(f, "{}", x),
            Stmt::DefLetStmt(x) => write!(f, "{}", x),
            Stmt::DefPropWithMeaningStmt(x) => write!(f, "{}", x),
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
            Stmt::ByCasesAxiomStmt(x) => write!(f, "{}", x),
            Stmt::ByContraAxiomStmt(x) => write!(f, "{}", x),
            Stmt::EnumerateAxiomStmt(x) => write!(f, "{}", x),
            Stmt::ByInducAxiomStmt(x) => write!(f, "{}", x),
            Stmt::ForAxiomStmt(x) => write!(f, "{}", x),
            Stmt::ByExtensionAxiomStmt(x) => write!(f, "{}", x),
            Stmt::ByFnDefAxiomStmt(x) => write!(f, "{}", x),
            Stmt::ByCartDefAxiomStmt(x) => write!(f, "{}", x),
        }
    }
}
