use crate::prelude::*;
use std::fmt;
use std::ops::{Deref, DerefMut};

/// Execution evidence shared by every successful non-factual statement.
///
/// `inside_results` is the ordered certificate produced while executing the
/// statement. It is empty when the statement has no child checks or proof
/// steps; it is not a second copy of the source statement body.
#[derive(Debug)]
pub struct VerifiedStmtCommonIr {
    pub well_definedness: WellDefinednessCertificate,
    pub infers: InferResult,
    pub inside_results: Vec<StmtResult>,
    pub execution_trace: Option<StatementExecutionTrace>,
}

impl VerifiedStmtCommonIr {
    pub fn new(infers: InferResult, inside_results: Vec<StmtResult>) -> Self {
        Self {
            well_definedness: WellDefinednessCertificate::default(),
            infers,
            inside_results,
            execution_trace: None,
        }
    }
}

/// Evidence shared by every factual statement after its exact `Fact` variant
/// has been selected by `VerifiedFactStmtIr`.
#[derive(Debug)]
pub struct VerifiedFactStmtDataIr {
    /// Filled only when the proved fact is stored in an environment.
    pub fact_id: Option<FactId>,
    pub well_definedness: WellDefinednessCertificate,
    pub infers: InferResult,
    pub verified_by: VerifiedByResult,
    pub execution_trace: Option<StatementExecutionTrace>,
}

impl VerifiedFactStmtDataIr {
    pub fn new(infers: InferResult, verified_by: VerifiedByResult) -> Self {
        Self {
            fact_id: None,
            well_definedness: WellDefinednessCertificate::default(),
            infers,
            verified_by,
            execution_trace: None,
        }
    }
}

/// Canonical successful IR for a factual statement. This enum deliberately
/// mirrors `Fact`; a fact cannot be retargeted by changing a generic
/// `statement: Fact` field after construction.
pub enum VerifiedFactStmtIr {
    AtomicFact {
        statement: AtomicFact,
        data: VerifiedFactStmtDataIr,
    },
    ExistFact {
        statement: ExistFactEnum,
        data: VerifiedFactStmtDataIr,
    },
    OrFact {
        statement: OrFact,
        data: VerifiedFactStmtDataIr,
    },
    AndFact {
        statement: AndFact,
        data: VerifiedFactStmtDataIr,
    },
    ChainFact {
        statement: ChainFact,
        data: VerifiedFactStmtDataIr,
    },
    ForallFact {
        statement: ForallFact,
        data: VerifiedFactStmtDataIr,
    },
    ForallFactWithIff {
        statement: ForallFactWithIff,
        data: VerifiedFactStmtDataIr,
    },
    NotForall {
        statement: NotForallFact,
        data: VerifiedFactStmtDataIr,
    },
}

impl VerifiedFactStmtIr {
    pub fn new(statement: Fact, infers: InferResult, verified_by: VerifiedByResult) -> Self {
        let data = VerifiedFactStmtDataIr::new(infers, verified_by);
        match statement {
            Fact::AtomicFact(statement) => Self::AtomicFact { statement, data },
            Fact::ExistFact(statement) => Self::ExistFact { statement, data },
            Fact::OrFact(statement) => Self::OrFact { statement, data },
            Fact::AndFact(statement) => Self::AndFact { statement, data },
            Fact::ChainFact(statement) => Self::ChainFact { statement, data },
            Fact::ForallFact(statement) => Self::ForallFact { statement, data },
            Fact::ForallFactWithIff(statement) => Self::ForallFactWithIff { statement, data },
            Fact::NotForall(statement) => Self::NotForall { statement, data },
        }
    }

    pub fn fact(&self) -> Fact {
        match self {
            Self::AtomicFact { statement, .. } => statement.clone().into(),
            Self::ExistFact { statement, .. } => statement.clone().into(),
            Self::OrFact { statement, .. } => statement.clone().into(),
            Self::AndFact { statement, .. } => statement.clone().into(),
            Self::ChainFact { statement, .. } => statement.clone().into(),
            Self::ForallFact { statement, .. } => statement.clone().into(),
            Self::ForallFactWithIff { statement, .. } => statement.clone().into(),
            Self::NotForall { statement, .. } => statement.clone().into(),
        }
    }

    pub fn into_parts(self) -> (Fact, VerifiedFactStmtDataIr) {
        match self {
            Self::AtomicFact { statement, data } => (statement.into(), data),
            Self::ExistFact { statement, data } => (statement.into(), data),
            Self::OrFact { statement, data } => (statement.into(), data),
            Self::AndFact { statement, data } => (statement.into(), data),
            Self::ChainFact { statement, data } => (statement.into(), data),
            Self::ForallFact { statement, data } => (statement.into(), data),
            Self::ForallFactWithIff { statement, data } => (statement.into(), data),
            Self::NotForall { statement, data } => (statement.into(), data),
        }
    }

    fn data(&self) -> &VerifiedFactStmtDataIr {
        match self {
            Self::AtomicFact { data, .. }
            | Self::ExistFact { data, .. }
            | Self::OrFact { data, .. }
            | Self::AndFact { data, .. }
            | Self::ChainFact { data, .. }
            | Self::ForallFact { data, .. }
            | Self::ForallFactWithIff { data, .. }
            | Self::NotForall { data, .. } => data,
        }
    }

    fn data_mut(&mut self) -> &mut VerifiedFactStmtDataIr {
        match self {
            Self::AtomicFact { data, .. }
            | Self::ExistFact { data, .. }
            | Self::OrFact { data, .. }
            | Self::AndFact { data, .. }
            | Self::ChainFact { data, .. }
            | Self::ForallFact { data, .. }
            | Self::ForallFactWithIff { data, .. }
            | Self::NotForall { data, .. } => data,
        }
    }
}

impl Deref for VerifiedFactStmtIr {
    type Target = VerifiedFactStmtDataIr;

    fn deref(&self) -> &Self::Target {
        self.data()
    }
}

impl DerefMut for VerifiedFactStmtIr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data_mut()
    }
}

impl fmt::Debug for VerifiedFactStmtIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VerifiedFactStmtIr")
            .field("statement", &self.fact())
            .field("data", self.data())
            .finish()
    }
}

/// Canonical successful statement IR. Its shape mirrors `Stmt` recursively;
/// statement-specific evidence is owned only by the matching leaf variant.
pub enum VerifiedStmtIr {
    Fact(VerifiedFactStmtIr),
    UnsafeStmt(VerifiedUnsafeStmtIr),
    DefObjStmt(VerifiedDefObjStmtIr),
    DefPredicateStmt(VerifiedDefPredicateStmtIr),
    DefInterfaceStmt(VerifiedDefInterfaceStmtIr),
    DefAlgoStmt {
        statement: DefAlgoStmt,
        common: VerifiedStmtCommonIr,
    },
    DefThmStmt {
        statement: DefThmStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<TheoremVerificationResult>,
    },
    AxiomStmt {
        statement: AxiomStmt,
        common: VerifiedStmtCommonIr,
    },
    DefStrategyStmt {
        statement: DefStrategyStmt,
        common: VerifiedStmtCommonIr,
    },
    By(VerifiedByStmtIr),
    Witness(VerifiedWitnessStmtIr),
    ProofBlock(VerifiedProofBlockStmtIr),
    Command(VerifiedCommandStmtIr),
}

pub enum VerifiedUnsafeStmtIr {
    TrustStmt {
        statement: TrustStmt,
        common: VerifiedStmtCommonIr,
    },
    TrustHaveStmt {
        statement: TrustHaveStmt,
        common: VerifiedStmtCommonIr,
    },
}

pub enum VerifiedDefObjStmtIr {
    LetObjStmt {
        statement: LetObjStmt,
        common: VerifiedStmtCommonIr,
    },
    HaveObjInNonemptySetStmt {
        statement: HaveObjInNonemptySetOrParamTypeStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ObjectChoiceVerificationResult>,
    },
    HaveObjEqualStmt {
        statement: HaveObjEqualStmt,
        common: VerifiedStmtCommonIr,
    },
    HaveObjByExistFactsStmt {
        statement: HaveObjByExistFactsStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ExistentialEliminationVerificationResult>,
    },
    ObtainObjFromExistFact {
        statement: ObtainObjFromExistFact,
        common: VerifiedStmtCommonIr,
        verification: Option<ExistentialEliminationVerificationResult>,
    },
    ObtainObjFromAtomicFact {
        statement: ObtainObjFromAtomicFact,
        common: VerifiedStmtCommonIr,
        verification: Option<ExistentialEliminationVerificationResult>,
    },
    ObtainObjFromThm {
        statement: ObtainObjFromThm,
        common: VerifiedStmtCommonIr,
        verification: Option<ExistentialEliminationVerificationResult>,
    },
    HaveByPreimageStmt {
        statement: HaveByPreimageStmt,
        common: VerifiedStmtCommonIr,
    },
    HaveFnEqualStmt {
        statement: HaveFnEqualStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<FunctionDefinitionVerificationResult>,
    },
    HaveFnEqualCaseByCaseStmt {
        statement: HaveFnEqualCaseByCaseStmt,
        common: VerifiedStmtCommonIr,
    },
    HaveFnByInducStmt {
        statement: HaveFnByInducStmt,
        common: VerifiedStmtCommonIr,
    },
    HaveFnByForallExistUniqueStmt {
        statement: HaveFnByForallExistUniqueStmt,
        common: VerifiedStmtCommonIr,
    },
    HaveTupleStmt {
        statement: HaveTupleStmt,
        common: VerifiedStmtCommonIr,
    },
    HaveCartStmt {
        statement: HaveCartStmt,
        common: VerifiedStmtCommonIr,
    },
    HaveSeqStmt {
        statement: HaveSeqStmt,
        common: VerifiedStmtCommonIr,
    },
    HaveFiniteSeqStmt {
        statement: HaveFiniteSeqStmt,
        common: VerifiedStmtCommonIr,
    },
    HaveMatrixStmt {
        statement: HaveMatrixStmt,
        common: VerifiedStmtCommonIr,
    },
}

pub enum VerifiedDefPredicateStmtIr {
    DefPropStmt {
        statement: DefPropStmt,
        common: VerifiedStmtCommonIr,
    },
    DefAbstractPropStmt {
        statement: DefAbstractPropStmt,
        common: VerifiedStmtCommonIr,
    },
}

pub enum VerifiedDefInterfaceStmtIr {
    DefSettingStmt {
        statement: DefSettingStmt,
        common: VerifiedStmtCommonIr,
    },
    DefTemplateStmt {
        statement: DefTemplateStmt,
        common: VerifiedStmtCommonIr,
    },
    DefStructStmt {
        statement: DefStructStmt,
        common: VerifiedStmtCommonIr,
    },
}

pub enum VerifiedByStmtIr {
    ByCasesStmt {
        statement: ByCasesStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByCasesVerificationResult>,
    },
    ByContraStmt {
        statement: ByContraStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByContraVerificationResult>,
    },
    ByEnumerateFiniteSetStmt {
        statement: ByEnumerateFiniteSetStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByEnumerateFiniteSetVerificationResult>,
    },
    ByFiniteSetInducStmt {
        statement: ByFiniteSetInducStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByInducVerificationResult>,
    },
    ByInducStmt {
        statement: ByInducStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByInducVerificationResult>,
    },
    ByForStmt {
        statement: ByForStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByForVerificationResult>,
    },
    ByExtensionStmt {
        statement: ByExtensionStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByExtensionVerificationResult>,
    },
    ByEnumerateRangeStmt {
        statement: ByEnumerateRangeStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByEnumerateRangeVerificationResult>,
    },
    ByClosedRangeAsCasesStmt {
        statement: ByClosedRangeAsCasesStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByEnumerateRangeVerificationResult>,
    },
    ByTransitivePropStmt {
        statement: ByTransitivePropStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByPropRegistrationVerificationResult>,
    },
    BySymmetricPropStmt {
        statement: BySymmetricPropStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByPropRegistrationVerificationResult>,
    },
    ByReflexivePropStmt {
        statement: ByReflexivePropStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByPropRegistrationVerificationResult>,
    },
    ByAntisymmetricPropStmt {
        statement: ByAntisymmetricPropStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByPropRegistrationVerificationResult>,
    },
    ByZornLemmaStmt {
        statement: ByZornLemmaStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByChoiceVerificationResult>,
    },
    ByAxiomOfChoiceStmt {
        statement: ByAxiomOfChoiceStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByChoiceVerificationResult>,
    },
    ByRegularityAxiomStmt {
        statement: ByRegularityAxiomStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByChoiceVerificationResult>,
    },
    ByDefStmt {
        statement: ByDefStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByDefinitionVerificationResult>,
    },
    ByThmStmt {
        statement: ByThmStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ByTheoremVerificationResult>,
    },
}

pub enum VerifiedWitnessStmtIr {
    WitnessExistFact {
        statement: WitnessExistFact,
        common: VerifiedStmtCommonIr,
        verification: Option<WitnessExistVerificationResult>,
    },
    WitnessAtomicFact {
        statement: WitnessAtomicFact,
        common: VerifiedStmtCommonIr,
        verification: Option<WitnessAtomicFactVerificationResult>,
    },
    WitnessNonemptySet {
        statement: WitnessNonemptySet,
        common: VerifiedStmtCommonIr,
    },
}

pub enum VerifiedProofBlockStmtIr {
    ClaimStmt {
        statement: ClaimStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ClaimVerificationResult>,
        local_scope: Option<LocalProofScopeVerificationResult>,
    },
    ExampleStmt {
        statement: ExampleStmt,
        common: VerifiedStmtCommonIr,
        verification: Option<ClaimVerificationResult>,
        local_scope: Option<LocalProofScopeVerificationResult>,
    },
    SketchStmt {
        statement: SketchStmt,
        common: VerifiedStmtCommonIr,
        local_scope: Option<LocalProofScopeVerificationResult>,
    },
    TryStmt {
        statement: TryStmt,
        common: VerifiedStmtCommonIr,
    },
}

pub enum VerifiedCommandStmtIr {
    ImportStmt {
        statement: ImportStmt,
        common: VerifiedStmtCommonIr,
    },
    DoNothingStmt {
        statement: DoNothingStmt,
        common: VerifiedStmtCommonIr,
    },
    ClearStmt {
        statement: ClearStmt,
        common: VerifiedStmtCommonIr,
    },
    EvalStmt {
        statement: EvalStmt,
        common: VerifiedStmtCommonIr,
        reported_store_facts: Vec<StoreFactOutput>,
    },
    UseStrategyStmt {
        statement: UseStrategyStmt,
        common: VerifiedStmtCommonIr,
    },
    StopStrategyStmt {
        statement: StopStrategyStmt,
        common: VerifiedStmtCommonIr,
    },
}

impl fmt::Debug for VerifiedStmtIr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VerifiedStmtIr")
            .field("statement", &self.statement())
            .field("common", &self.common())
            .finish()
    }
}

impl VerifiedStmtIr {
    pub fn statement(&self) -> Stmt {
        match self {
            Self::Fact(statement) => statement.fact().into(),
            Self::UnsafeStmt(statement) => statement.statement(),
            Self::DefObjStmt(statement) => statement.statement(),
            Self::DefPredicateStmt(statement) => statement.statement(),
            Self::DefInterfaceStmt(statement) => statement.statement(),
            Self::DefAlgoStmt { statement, .. } => statement.clone().into(),
            Self::DefThmStmt { statement, .. } => statement.clone().into(),
            Self::AxiomStmt { statement, .. } => statement.clone().into(),
            Self::DefStrategyStmt { statement, .. } => statement.clone().into(),
            Self::By(statement) => statement.statement(),
            Self::Witness(statement) => statement.statement(),
            Self::ProofBlock(statement) => statement.statement(),
            Self::Command(statement) => statement.statement(),
        }
    }

    pub fn fact(&self) -> Option<&VerifiedFactStmtIr> {
        match self {
            Self::Fact(statement) => Some(statement),
            _ => None,
        }
    }

    pub fn fact_mut(&mut self) -> Option<&mut VerifiedFactStmtIr> {
        match self {
            Self::Fact(statement) => Some(statement),
            _ => None,
        }
    }

    pub fn common(&self) -> Option<&VerifiedStmtCommonIr> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.common()),
            Self::DefObjStmt(statement) => Some(statement.common()),
            Self::DefPredicateStmt(statement) => Some(statement.common()),
            Self::DefInterfaceStmt(statement) => Some(statement.common()),
            Self::DefAlgoStmt { common, .. }
            | Self::DefThmStmt { common, .. }
            | Self::AxiomStmt { common, .. }
            | Self::DefStrategyStmt { common, .. } => Some(common),
            Self::By(statement) => Some(statement.common()),
            Self::Witness(statement) => Some(statement.common()),
            Self::ProofBlock(statement) => Some(statement.common()),
            Self::Command(statement) => Some(statement.common()),
        }
    }

    pub fn common_mut(&mut self) -> Option<&mut VerifiedStmtCommonIr> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.common_mut()),
            Self::DefObjStmt(statement) => Some(statement.common_mut()),
            Self::DefPredicateStmt(statement) => Some(statement.common_mut()),
            Self::DefInterfaceStmt(statement) => Some(statement.common_mut()),
            Self::DefAlgoStmt { common, .. }
            | Self::DefThmStmt { common, .. }
            | Self::AxiomStmt { common, .. }
            | Self::DefStrategyStmt { common, .. } => Some(common),
            Self::By(statement) => Some(statement.common_mut()),
            Self::Witness(statement) => Some(statement.common_mut()),
            Self::ProofBlock(statement) => Some(statement.common_mut()),
            Self::Command(statement) => Some(statement.common_mut()),
        }
    }

    pub fn into_common(self) -> Option<VerifiedStmtCommonIr> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.into_common()),
            Self::DefObjStmt(statement) => Some(statement.into_common()),
            Self::DefPredicateStmt(statement) => Some(statement.into_common()),
            Self::DefInterfaceStmt(statement) => Some(statement.into_common()),
            Self::DefAlgoStmt { common, .. }
            | Self::DefThmStmt { common, .. }
            | Self::AxiomStmt { common, .. }
            | Self::DefStrategyStmt { common, .. } => Some(common),
            Self::By(statement) => Some(statement.into_common()),
            Self::Witness(statement) => Some(statement.into_common()),
            Self::ProofBlock(statement) => Some(statement.into_common()),
            Self::Command(statement) => Some(statement.into_common()),
        }
    }
}

impl VerifiedUnsafeStmtIr {
    fn into_common(self) -> VerifiedStmtCommonIr {
        match self {
            Self::TrustStmt { common, .. } | Self::TrustHaveStmt { common, .. } => common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::TrustStmt { statement, .. } => statement.clone().into(),
            Self::TrustHaveStmt { statement, .. } => statement.clone().into(),
        }
    }

    fn common(&self) -> &VerifiedStmtCommonIr {
        match self {
            Self::TrustStmt { common, .. } | Self::TrustHaveStmt { common, .. } => common,
        }
    }

    fn common_mut(&mut self) -> &mut VerifiedStmtCommonIr {
        match self {
            Self::TrustStmt { common, .. } | Self::TrustHaveStmt { common, .. } => common,
        }
    }
}

impl VerifiedDefObjStmtIr {
    fn into_common(self) -> VerifiedStmtCommonIr {
        match self {
            Self::LetObjStmt { common, .. }
            | Self::HaveObjInNonemptySetStmt { common, .. }
            | Self::HaveObjEqualStmt { common, .. }
            | Self::HaveObjByExistFactsStmt { common, .. }
            | Self::ObtainObjFromExistFact { common, .. }
            | Self::ObtainObjFromAtomicFact { common, .. }
            | Self::ObtainObjFromThm { common, .. }
            | Self::HaveByPreimageStmt { common, .. }
            | Self::HaveFnEqualStmt { common, .. }
            | Self::HaveFnEqualCaseByCaseStmt { common, .. }
            | Self::HaveFnByInducStmt { common, .. }
            | Self::HaveFnByForallExistUniqueStmt { common, .. }
            | Self::HaveTupleStmt { common, .. }
            | Self::HaveCartStmt { common, .. }
            | Self::HaveSeqStmt { common, .. }
            | Self::HaveFiniteSeqStmt { common, .. }
            | Self::HaveMatrixStmt { common, .. } => common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::LetObjStmt { statement, .. } => statement.clone().into(),
            Self::HaveObjInNonemptySetStmt { statement, .. } => statement.clone().into(),
            Self::HaveObjEqualStmt { statement, .. } => statement.clone().into(),
            Self::HaveObjByExistFactsStmt { statement, .. } => statement.clone().into(),
            Self::ObtainObjFromExistFact { statement, .. } => statement.clone().into(),
            Self::ObtainObjFromAtomicFact { statement, .. } => statement.clone().into(),
            Self::ObtainObjFromThm { statement, .. } => statement.clone().into(),
            Self::HaveByPreimageStmt { statement, .. } => statement.clone().into(),
            Self::HaveFnEqualStmt { statement, .. } => statement.clone().into(),
            Self::HaveFnEqualCaseByCaseStmt { statement, .. } => statement.clone().into(),
            Self::HaveFnByInducStmt { statement, .. } => statement.clone().into(),
            Self::HaveFnByForallExistUniqueStmt { statement, .. } => statement.clone().into(),
            Self::HaveTupleStmt { statement, .. } => statement.clone().into(),
            Self::HaveCartStmt { statement, .. } => statement.clone().into(),
            Self::HaveSeqStmt { statement, .. } => statement.clone().into(),
            Self::HaveFiniteSeqStmt { statement, .. } => statement.clone().into(),
            Self::HaveMatrixStmt { statement, .. } => statement.clone().into(),
        }
    }

    fn common(&self) -> &VerifiedStmtCommonIr {
        match self {
            Self::LetObjStmt { common, .. }
            | Self::HaveObjInNonemptySetStmt { common, .. }
            | Self::HaveObjEqualStmt { common, .. }
            | Self::HaveObjByExistFactsStmt { common, .. }
            | Self::ObtainObjFromExistFact { common, .. }
            | Self::ObtainObjFromAtomicFact { common, .. }
            | Self::ObtainObjFromThm { common, .. }
            | Self::HaveByPreimageStmt { common, .. }
            | Self::HaveFnEqualStmt { common, .. }
            | Self::HaveFnEqualCaseByCaseStmt { common, .. }
            | Self::HaveFnByInducStmt { common, .. }
            | Self::HaveFnByForallExistUniqueStmt { common, .. }
            | Self::HaveTupleStmt { common, .. }
            | Self::HaveCartStmt { common, .. }
            | Self::HaveSeqStmt { common, .. }
            | Self::HaveFiniteSeqStmt { common, .. }
            | Self::HaveMatrixStmt { common, .. } => common,
        }
    }

    fn common_mut(&mut self) -> &mut VerifiedStmtCommonIr {
        match self {
            Self::LetObjStmt { common, .. }
            | Self::HaveObjInNonemptySetStmt { common, .. }
            | Self::HaveObjEqualStmt { common, .. }
            | Self::HaveObjByExistFactsStmt { common, .. }
            | Self::ObtainObjFromExistFact { common, .. }
            | Self::ObtainObjFromAtomicFact { common, .. }
            | Self::ObtainObjFromThm { common, .. }
            | Self::HaveByPreimageStmt { common, .. }
            | Self::HaveFnEqualStmt { common, .. }
            | Self::HaveFnEqualCaseByCaseStmt { common, .. }
            | Self::HaveFnByInducStmt { common, .. }
            | Self::HaveFnByForallExistUniqueStmt { common, .. }
            | Self::HaveTupleStmt { common, .. }
            | Self::HaveCartStmt { common, .. }
            | Self::HaveSeqStmt { common, .. }
            | Self::HaveFiniteSeqStmt { common, .. }
            | Self::HaveMatrixStmt { common, .. } => common,
        }
    }
}

impl VerifiedDefPredicateStmtIr {
    fn into_common(self) -> VerifiedStmtCommonIr {
        match self {
            Self::DefPropStmt { common, .. } | Self::DefAbstractPropStmt { common, .. } => common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::DefPropStmt { statement, .. } => statement.clone().into(),
            Self::DefAbstractPropStmt { statement, .. } => statement.clone().into(),
        }
    }

    fn common(&self) -> &VerifiedStmtCommonIr {
        match self {
            Self::DefPropStmt { common, .. } | Self::DefAbstractPropStmt { common, .. } => common,
        }
    }

    fn common_mut(&mut self) -> &mut VerifiedStmtCommonIr {
        match self {
            Self::DefPropStmt { common, .. } | Self::DefAbstractPropStmt { common, .. } => common,
        }
    }
}

impl VerifiedDefInterfaceStmtIr {
    fn into_common(self) -> VerifiedStmtCommonIr {
        match self {
            Self::DefSettingStmt { common, .. }
            | Self::DefTemplateStmt { common, .. }
            | Self::DefStructStmt { common, .. } => common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::DefSettingStmt { statement, .. } => statement.clone().into(),
            Self::DefTemplateStmt { statement, .. } => statement.clone().into(),
            Self::DefStructStmt { statement, .. } => statement.clone().into(),
        }
    }

    fn common(&self) -> &VerifiedStmtCommonIr {
        match self {
            Self::DefSettingStmt { common, .. }
            | Self::DefTemplateStmt { common, .. }
            | Self::DefStructStmt { common, .. } => common,
        }
    }

    fn common_mut(&mut self) -> &mut VerifiedStmtCommonIr {
        match self {
            Self::DefSettingStmt { common, .. }
            | Self::DefTemplateStmt { common, .. }
            | Self::DefStructStmt { common, .. } => common,
        }
    }
}

impl VerifiedByStmtIr {
    fn into_common(self) -> VerifiedStmtCommonIr {
        match self {
            Self::ByCasesStmt { common, .. }
            | Self::ByContraStmt { common, .. }
            | Self::ByEnumerateFiniteSetStmt { common, .. }
            | Self::ByFiniteSetInducStmt { common, .. }
            | Self::ByInducStmt { common, .. }
            | Self::ByForStmt { common, .. }
            | Self::ByExtensionStmt { common, .. }
            | Self::ByEnumerateRangeStmt { common, .. }
            | Self::ByClosedRangeAsCasesStmt { common, .. }
            | Self::ByTransitivePropStmt { common, .. }
            | Self::BySymmetricPropStmt { common, .. }
            | Self::ByReflexivePropStmt { common, .. }
            | Self::ByAntisymmetricPropStmt { common, .. }
            | Self::ByZornLemmaStmt { common, .. }
            | Self::ByAxiomOfChoiceStmt { common, .. }
            | Self::ByRegularityAxiomStmt { common, .. }
            | Self::ByDefStmt { common, .. }
            | Self::ByThmStmt { common, .. } => common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::ByCasesStmt { statement, .. } => statement.clone().into(),
            Self::ByContraStmt { statement, .. } => statement.clone().into(),
            Self::ByEnumerateFiniteSetStmt { statement, .. } => statement.clone().into(),
            Self::ByFiniteSetInducStmt { statement, .. } => statement.clone().into(),
            Self::ByInducStmt { statement, .. } => statement.clone().into(),
            Self::ByForStmt { statement, .. } => statement.clone().into(),
            Self::ByExtensionStmt { statement, .. } => statement.clone().into(),
            Self::ByEnumerateRangeStmt { statement, .. } => statement.clone().into(),
            Self::ByClosedRangeAsCasesStmt { statement, .. } => statement.clone().into(),
            Self::ByTransitivePropStmt { statement, .. } => statement.clone().into(),
            Self::BySymmetricPropStmt { statement, .. } => statement.clone().into(),
            Self::ByReflexivePropStmt { statement, .. } => statement.clone().into(),
            Self::ByAntisymmetricPropStmt { statement, .. } => statement.clone().into(),
            Self::ByZornLemmaStmt { statement, .. } => statement.clone().into(),
            Self::ByAxiomOfChoiceStmt { statement, .. } => statement.clone().into(),
            Self::ByRegularityAxiomStmt { statement, .. } => statement.clone().into(),
            Self::ByDefStmt { statement, .. } => statement.clone().into(),
            Self::ByThmStmt { statement, .. } => statement.clone().into(),
        }
    }

    fn common(&self) -> &VerifiedStmtCommonIr {
        match self {
            Self::ByCasesStmt { common, .. }
            | Self::ByContraStmt { common, .. }
            | Self::ByEnumerateFiniteSetStmt { common, .. }
            | Self::ByFiniteSetInducStmt { common, .. }
            | Self::ByInducStmt { common, .. }
            | Self::ByForStmt { common, .. }
            | Self::ByExtensionStmt { common, .. }
            | Self::ByEnumerateRangeStmt { common, .. }
            | Self::ByClosedRangeAsCasesStmt { common, .. }
            | Self::ByTransitivePropStmt { common, .. }
            | Self::BySymmetricPropStmt { common, .. }
            | Self::ByReflexivePropStmt { common, .. }
            | Self::ByAntisymmetricPropStmt { common, .. }
            | Self::ByZornLemmaStmt { common, .. }
            | Self::ByAxiomOfChoiceStmt { common, .. }
            | Self::ByRegularityAxiomStmt { common, .. }
            | Self::ByDefStmt { common, .. }
            | Self::ByThmStmt { common, .. } => common,
        }
    }

    fn common_mut(&mut self) -> &mut VerifiedStmtCommonIr {
        match self {
            Self::ByCasesStmt { common, .. }
            | Self::ByContraStmt { common, .. }
            | Self::ByEnumerateFiniteSetStmt { common, .. }
            | Self::ByFiniteSetInducStmt { common, .. }
            | Self::ByInducStmt { common, .. }
            | Self::ByForStmt { common, .. }
            | Self::ByExtensionStmt { common, .. }
            | Self::ByEnumerateRangeStmt { common, .. }
            | Self::ByClosedRangeAsCasesStmt { common, .. }
            | Self::ByTransitivePropStmt { common, .. }
            | Self::BySymmetricPropStmt { common, .. }
            | Self::ByReflexivePropStmt { common, .. }
            | Self::ByAntisymmetricPropStmt { common, .. }
            | Self::ByZornLemmaStmt { common, .. }
            | Self::ByAxiomOfChoiceStmt { common, .. }
            | Self::ByRegularityAxiomStmt { common, .. }
            | Self::ByDefStmt { common, .. }
            | Self::ByThmStmt { common, .. } => common,
        }
    }
}

impl VerifiedWitnessStmtIr {
    fn into_common(self) -> VerifiedStmtCommonIr {
        match self {
            Self::WitnessExistFact { common, .. }
            | Self::WitnessAtomicFact { common, .. }
            | Self::WitnessNonemptySet { common, .. } => common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::WitnessExistFact { statement, .. } => statement.clone().into(),
            Self::WitnessAtomicFact { statement, .. } => statement.clone().into(),
            Self::WitnessNonemptySet { statement, .. } => statement.clone().into(),
        }
    }

    fn common(&self) -> &VerifiedStmtCommonIr {
        match self {
            Self::WitnessExistFact { common, .. }
            | Self::WitnessAtomicFact { common, .. }
            | Self::WitnessNonemptySet { common, .. } => common,
        }
    }

    fn common_mut(&mut self) -> &mut VerifiedStmtCommonIr {
        match self {
            Self::WitnessExistFact { common, .. }
            | Self::WitnessAtomicFact { common, .. }
            | Self::WitnessNonemptySet { common, .. } => common,
        }
    }
}

impl VerifiedProofBlockStmtIr {
    fn into_common(self) -> VerifiedStmtCommonIr {
        match self {
            Self::ClaimStmt { common, .. }
            | Self::ExampleStmt { common, .. }
            | Self::SketchStmt { common, .. }
            | Self::TryStmt { common, .. } => common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::ClaimStmt { statement, .. } => statement.clone().into(),
            Self::ExampleStmt { statement, .. } => statement.clone().into(),
            Self::SketchStmt { statement, .. } => statement.clone().into(),
            Self::TryStmt { statement, .. } => statement.clone().into(),
        }
    }

    fn common(&self) -> &VerifiedStmtCommonIr {
        match self {
            Self::ClaimStmt { common, .. }
            | Self::ExampleStmt { common, .. }
            | Self::SketchStmt { common, .. }
            | Self::TryStmt { common, .. } => common,
        }
    }

    fn common_mut(&mut self) -> &mut VerifiedStmtCommonIr {
        match self {
            Self::ClaimStmt { common, .. }
            | Self::ExampleStmt { common, .. }
            | Self::SketchStmt { common, .. }
            | Self::TryStmt { common, .. } => common,
        }
    }
}

impl VerifiedCommandStmtIr {
    fn into_common(self) -> VerifiedStmtCommonIr {
        match self {
            Self::ImportStmt { common, .. }
            | Self::DoNothingStmt { common, .. }
            | Self::ClearStmt { common, .. }
            | Self::EvalStmt { common, .. }
            | Self::UseStrategyStmt { common, .. }
            | Self::StopStrategyStmt { common, .. } => common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::ImportStmt { statement, .. } => statement.clone().into(),
            Self::DoNothingStmt { statement, .. } => statement.clone().into(),
            Self::ClearStmt { statement, .. } => statement.clone().into(),
            Self::EvalStmt { statement, .. } => statement.clone().into(),
            Self::UseStrategyStmt { statement, .. } => statement.clone().into(),
            Self::StopStrategyStmt { statement, .. } => statement.clone().into(),
        }
    }

    fn common(&self) -> &VerifiedStmtCommonIr {
        match self {
            Self::ImportStmt { common, .. }
            | Self::DoNothingStmt { common, .. }
            | Self::ClearStmt { common, .. }
            | Self::EvalStmt { common, .. }
            | Self::UseStrategyStmt { common, .. }
            | Self::StopStrategyStmt { common, .. } => common,
        }
    }

    fn common_mut(&mut self) -> &mut VerifiedStmtCommonIr {
        match self {
            Self::ImportStmt { common, .. }
            | Self::DoNothingStmt { common, .. }
            | Self::ClearStmt { common, .. }
            | Self::EvalStmt { common, .. }
            | Self::UseStrategyStmt { common, .. }
            | Self::StopStrategyStmt { common, .. } => common,
        }
    }
}
