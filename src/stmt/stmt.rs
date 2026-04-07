use crate::prelude::*;
use std::fmt;

#[derive(Clone)]
pub enum Stmt {
    Fact(Fact),
    DefLetStmt(DefLetStmt),
    DefPropStmt(DefPropStmt),
    DefAbstractPropStmt(DefAbstractPropStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveExistObjStmt(HaveExistObjStmt),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    HaveFnByInducStmt(HaveFnByInducStmt),
    DefStructStmt(DefStructStmt),
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
    ByCasesStmt(ByCasesStmt),
    ByContraStmt(ByContraStmt),
    ByEnumerateStmt(ByEnumerateStmt),
    ByInducStmt(ByInducStmt),
    ByForStmt(ByForStmt),
    ByExtensionStmt(ByExtensionStmt),
    ByFnStmt(ByFnStmt),
    ByFamilyStmt(ByFamilyStmt),
    ByStructStmt(ByStructStmt),
    ByTuple(ByTupleStmt),
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
            Stmt::DefPropStmt(x) => write!(f, "{}", x),
            Stmt::DefAbstractPropStmt(x) => write!(f, "{}", x),
            Stmt::HaveObjInNonemptySetStmt(x) => write!(f, "{}", x),
            Stmt::HaveObjEqualStmt(x) => write!(f, "{}", x),
            Stmt::HaveExistObjStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnEqualStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnEqualCaseByCaseStmt(x) => write!(f, "{}", x),
            Stmt::HaveFnByInducStmt(x) => write!(f, "{}", x),
            Stmt::DefStructStmt(x) => write!(f, "{}", x),
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
            Stmt::ByCasesStmt(x) => write!(f, "{}", x),
            Stmt::ByContraStmt(x) => write!(f, "{}", x),
            Stmt::ByEnumerateStmt(x) => write!(f, "{}", x),
            Stmt::ByInducStmt(x) => write!(f, "{}", x),
            Stmt::ByForStmt(x) => write!(f, "{}", x),
            Stmt::ByExtensionStmt(x) => write!(f, "{}", x),
            Stmt::ByFnStmt(x) => write!(f, "{}", x),
            Stmt::ByFamilyStmt(x) => write!(f, "{}", x),
            Stmt::ByStructStmt(x) => write!(f, "{}", x),
            Stmt::ByTuple(x) => write!(f, "{}", x),
        }
    }
}

impl Stmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            Stmt::Fact(fact) => fact.line_file(),
            Stmt::DefLetStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefPropStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefAbstractPropStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveObjInNonemptySetStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveObjEqualStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveExistObjStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveFnEqualStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.line_file.clone(),
            Stmt::HaveFnByInducStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefStructStmt(stmt) => stmt.line_file.clone(),
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
            Stmt::ByCasesStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByContraStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByEnumerateStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByInducStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByForStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByExtensionStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByFnStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByFamilyStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByStructStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByTuple(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            Stmt::Fact(_) => "Fact".to_string(),
            Stmt::DefLetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefPropStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefAbstractPropStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveObjInNonemptySetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveObjEqualStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveExistObjStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveFnEqualStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.stmt_type_name(),
            Stmt::HaveFnByInducStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefStructStmt(stmt) => stmt.stmt_type_name(),
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
            Stmt::ByCasesStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByContraStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByEnumerateStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByInducStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByForStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByExtensionStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByFnStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByFamilyStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByStructStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByTuple(stmt) => stmt.stmt_type_name(),
        }
    }
}
