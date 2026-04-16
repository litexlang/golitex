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
    HaveByExistStmt(HaveByExistStmt),
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
    ByFnSetStmt(ByFnSetStmt),
    ByFiniteSeqSetStmt(ByFiniteSeqSetStmt),
    ByMatrixSetStmt(ByMatrixSetStmt),
}

#[derive(Clone)]
pub struct ByFiniteSeqSetStmt {
    pub finite_seq_set: FiniteSeqSet,
    pub line_file: LineFile,
}

impl fmt::Display for ByFiniteSeqSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let o: Obj = self.finite_seq_set.clone().into();
        write!(f, "{} {}{} {}", BY, FINITE_SEQ, COLON, o)
    }
}

impl ByFiniteSeqSetStmt {
    pub fn new(finite_seq_set: FiniteSeqSet, line_file: LineFile) -> Self {
        ByFiniteSeqSetStmt {
            finite_seq_set,
            line_file,
        }
    }
}

#[derive(Clone)]
pub struct ByMatrixSetStmt {
    pub matrix_set: MatrixSet,
    pub line_file: LineFile,
}

impl fmt::Display for ByMatrixSetStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let o: Obj = self.matrix_set.clone().into();
        write!(f, "{} {}{} {}", BY, MATRIX, COLON, o)
    }
}

impl ByMatrixSetStmt {
    pub fn new(matrix_set: MatrixSet, line_file: LineFile) -> Self {
        ByMatrixSetStmt {
            matrix_set,
            line_file,
        }
    }
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
            Stmt::HaveByExistStmt(x) => write!(f, "{}", x),
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
            Stmt::ByFnSetStmt(x) => write!(f, "{}", x),
            Stmt::ByFiniteSeqSetStmt(x) => write!(f, "{}", x),
            Stmt::ByMatrixSetStmt(x) => write!(f, "{}", x),
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
            Stmt::HaveByExistStmt(stmt) => stmt.line_file.clone(),
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
            Stmt::ByFnSetStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByFiniteSeqSetStmt(stmt) => stmt.line_file.clone(),
            Stmt::ByMatrixSetStmt(stmt) => stmt.line_file.clone(),
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
            Stmt::HaveByExistStmt(stmt) => stmt.stmt_type_name(),
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
            Stmt::ByFnSetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByFiniteSeqSetStmt(stmt) => stmt.stmt_type_name(),
            Stmt::ByMatrixSetStmt(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl From<Fact> for Stmt {
    fn from(v: Fact) -> Self {
        Stmt::Fact(v)
    }
}

impl From<DefLetStmt> for Stmt {
    fn from(v: DefLetStmt) -> Self {
        Stmt::DefLetStmt(v)
    }
}

impl From<DefPropStmt> for Stmt {
    fn from(v: DefPropStmt) -> Self {
        Stmt::DefPropStmt(v)
    }
}

impl From<DefAbstractPropStmt> for Stmt {
    fn from(v: DefAbstractPropStmt) -> Self {
        Stmt::DefAbstractPropStmt(v)
    }
}

impl From<HaveObjInNonemptySetOrParamTypeStmt> for Stmt {
    fn from(v: HaveObjInNonemptySetOrParamTypeStmt) -> Self {
        Stmt::HaveObjInNonemptySetStmt(v)
    }
}

impl From<HaveObjEqualStmt> for Stmt {
    fn from(v: HaveObjEqualStmt) -> Self {
        Stmt::HaveObjEqualStmt(v)
    }
}

impl From<HaveByExistStmt> for Stmt {
    fn from(v: HaveByExistStmt) -> Self {
        Stmt::HaveByExistStmt(v)
    }
}

impl From<HaveFnEqualStmt> for Stmt {
    fn from(v: HaveFnEqualStmt) -> Self {
        Stmt::HaveFnEqualStmt(v)
    }
}

impl From<HaveFnEqualCaseByCaseStmt> for Stmt {
    fn from(v: HaveFnEqualCaseByCaseStmt) -> Self {
        Stmt::HaveFnEqualCaseByCaseStmt(v)
    }
}

impl From<HaveFnByInducStmt> for Stmt {
    fn from(v: HaveFnByInducStmt) -> Self {
        Stmt::HaveFnByInducStmt(v)
    }
}

impl From<DefStructStmt> for Stmt {
    fn from(v: DefStructStmt) -> Self {
        Stmt::DefStructStmt(v)
    }
}

impl From<DefFamilyStmt> for Stmt {
    fn from(v: DefFamilyStmt) -> Self {
        Stmt::DefFamilyStmt(v)
    }
}

impl From<DefAlgoStmt> for Stmt {
    fn from(v: DefAlgoStmt) -> Self {
        Stmt::DefAlgoStmt(v)
    }
}

impl From<ClaimStmt> for Stmt {
    fn from(v: ClaimStmt) -> Self {
        Stmt::ClaimStmt(v)
    }
}

impl From<KnowStmt> for Stmt {
    fn from(v: KnowStmt) -> Self {
        Stmt::KnowStmt(v)
    }
}

impl From<ProveStmt> for Stmt {
    fn from(v: ProveStmt) -> Self {
        Stmt::ProveStmt(v)
    }
}

impl From<ImportStmt> for Stmt {
    fn from(v: ImportStmt) -> Self {
        Stmt::ImportStmt(v)
    }
}

impl From<DoNothingStmt> for Stmt {
    fn from(v: DoNothingStmt) -> Self {
        Stmt::DoNothingStmt(v)
    }
}

impl From<RunFileStmt> for Stmt {
    fn from(v: RunFileStmt) -> Self {
        Stmt::RunFileStmt(v)
    }
}

impl From<EvalStmt> for Stmt {
    fn from(v: EvalStmt) -> Self {
        Stmt::EvalStmt(v)
    }
}

impl From<WitnessExistFact> for Stmt {
    fn from(v: WitnessExistFact) -> Self {
        Stmt::WitnessExistFact(v)
    }
}

impl From<WitnessNonemptySet> for Stmt {
    fn from(v: WitnessNonemptySet) -> Self {
        Stmt::WitnessNonemptySet(v)
    }
}

impl From<ByCasesStmt> for Stmt {
    fn from(v: ByCasesStmt) -> Self {
        Stmt::ByCasesStmt(v)
    }
}

impl From<ByContraStmt> for Stmt {
    fn from(v: ByContraStmt) -> Self {
        Stmt::ByContraStmt(v)
    }
}

impl From<ByEnumerateStmt> for Stmt {
    fn from(v: ByEnumerateStmt) -> Self {
        Stmt::ByEnumerateStmt(v)
    }
}

impl From<ByInducStmt> for Stmt {
    fn from(v: ByInducStmt) -> Self {
        Stmt::ByInducStmt(v)
    }
}

impl From<ByForStmt> for Stmt {
    fn from(v: ByForStmt) -> Self {
        Stmt::ByForStmt(v)
    }
}

impl From<ByExtensionStmt> for Stmt {
    fn from(v: ByExtensionStmt) -> Self {
        Stmt::ByExtensionStmt(v)
    }
}

impl From<ByFnStmt> for Stmt {
    fn from(v: ByFnStmt) -> Self {
        Stmt::ByFnStmt(v)
    }
}

impl From<ByFamilyStmt> for Stmt {
    fn from(v: ByFamilyStmt) -> Self {
        Stmt::ByFamilyStmt(v)
    }
}

impl From<ByStructStmt> for Stmt {
    fn from(v: ByStructStmt) -> Self {
        Stmt::ByStructStmt(v)
    }
}

impl From<ByTupleStmt> for Stmt {
    fn from(v: ByTupleStmt) -> Self {
        Stmt::ByTuple(v)
    }
}

impl From<ByFnSetStmt> for Stmt {
    fn from(v: ByFnSetStmt) -> Self {
        Stmt::ByFnSetStmt(v)
    }
}

impl From<ByFiniteSeqSetStmt> for Stmt {
    fn from(v: ByFiniteSeqSetStmt) -> Self {
        Stmt::ByFiniteSeqSetStmt(v)
    }
}

impl From<ByMatrixSetStmt> for Stmt {
    fn from(v: ByMatrixSetStmt) -> Self {
        Stmt::ByMatrixSetStmt(v)
    }
}
