use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum Stmt {
    Fact(Fact),
    DefLetStmt(DefLetStmt),
    DefPropWithMeaningStmt(DefPropWithMeaningStmt),
    DefAbstractPropStmt(DefAbstractPropStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveExistObjStmt(HaveExistObjStmt),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    DefParamTypeStructStmt(DefParamTypeStructStmt),
    DefFamilyStmt(DefFamilyStmt),
    DefAlgoStmt(DefAlgoStmt),
    ClaimStmt(ClaimStmt),
    KnowStmt(KnowStmt),
    ProveStmt(ProveStmt),
    ImportStmt(ImportStmt),
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

impl fmt::Debug for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Fact(x) => write!(f, "{}", x),
            Stmt::DefLetStmt(x) => write!(f, "{}", x),
            Stmt::DefPropWithMeaningStmt(x) => write!(f, "{}", x),
            Stmt::DefAbstractPropStmt(x) => write!(f, "{}", x),
            Stmt::HaveObjInNonemptySetStmt(x) => write!(f, "{}", x),
            Stmt::HaveObjEqualStmt(x) => write!(f, "{}", x),
            Stmt::HaveExistObjStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnEqualStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnEqualCaseByCaseStmt(x) => write!(f, "{}", x),
            Stmt::DefParamTypeStructStmt(x) => write!(f, "{}", x),
            Stmt::DefFamilyStmt(x) => write!(f, "{}", x),
            Stmt::DefAlgoStmt(x) => write!(f, "{}", x),
            Stmt::ClaimStmt(x) => write!(f, "{}", x),
            Stmt::KnowStmt(x) => write!(f, "{}", x),
            Stmt::ProveStmt(x) => write!(f, "{}", x),
            Stmt::ImportStmt(x) => write!(f, "{}", x),
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

impl Stmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            Stmt::Fact(fact) => fact.line_file(),
            Stmt::DefLetStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefPropWithMeaningStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefAbstractPropStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveObjInNonemptySetStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveObjEqualStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveExistObjStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveFnEqualStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefParamTypeStructStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefFamilyStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefAlgoStmt(stmt) => stmt.line_file.clone(),
            Stmt::ClaimStmt(stmt) => stmt.line_file.clone(),
            Stmt::KnowStmt(stmt) => stmt.line_file.clone(),
            Stmt::ProveStmt(stmt) => stmt.line_file.clone(),
            Stmt::ImportStmt(stmt) => stmt.line_file(),
            Stmt::DoNothingStmt(stmt) => stmt.line_file.clone(),
            Stmt::RunFileStmt(stmt) => stmt.line_file.clone(),
            Stmt::EvalStmt(stmt) => stmt.line_file.clone(),
            Stmt::WitnessExistFact(stmt) => stmt.line_file.clone(),
            Stmt::WitnessNonemptySet(stmt) => stmt.line_file.clone(),
            Stmt::ByCasesAxiomStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByContraAxiomStmt(stmt) => stmt.line_file.clone(),
            Stmt::EnumerateAxiomStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByInducAxiomStmt(stmt) => stmt.line_file.clone(),
            Stmt::ForAxiomStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByExtensionAxiomStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByFnDefAxiomStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByCartDefAxiomStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            Stmt::Fact(_) => "Fact".to_string(),
            Stmt::DefLetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefPropWithMeaningStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefAbstractPropStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveObjInNonemptySetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveObjEqualStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveExistObjStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveFnEqualStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefParamTypeStructStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefFamilyStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefAlgoStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ClaimStmt(stmt) => stmt.stmt_type_name(),
            Stmt::KnowStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ProveStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ImportStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DoNothingStmt(stmt) => stmt.stmt_type_name(),
            Stmt::RunFileStmt(stmt) => stmt.stmt_type_name(),
            Stmt::EvalStmt(stmt) => stmt.stmt_type_name(),
            Stmt::WitnessExistFact(stmt) => stmt.stmt_type_name(),
            Stmt::WitnessNonemptySet(stmt) => stmt.stmt_type_name(),
            Stmt::ByCasesAxiomStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByContraAxiomStmt(stmt) => stmt.stmt_type_name(),
            Stmt::EnumerateAxiomStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByInducAxiomStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ForAxiomStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByExtensionAxiomStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByFnDefAxiomStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByCartDefAxiomStmt(stmt) => stmt.stmt_type_name(),
        }
    }
}
