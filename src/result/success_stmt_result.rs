use crate::prelude::*;
use std::fmt;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

/// Execution evidence shared by every successful non-factual statement.
/// Recursive verification children belong to the statement-specific result,
/// never to this common execution envelope.
#[derive(Debug)]
pub struct SuccessStmtCommonResult {
    pub infers: SuccessInferResult,
    pub execution_trace: Option<StatementExecutionTrace>,
}

impl SuccessStmtCommonResult {
    pub fn new(infers: SuccessInferResult) -> Self {
        Self {
            infers,
            execution_trace: None,
        }
    }
}

pub struct SuccessVerifyAtomicFactResult {
    pub statement: AtomicFact,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyExistFactResult {
    pub statement: ExistFactEnum,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyOrFactResult {
    pub statement: OrFact,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyAndFactResult {
    pub statement: AndFact,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyChainFactResult {
    pub statement: ChainFact,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyForallFactResult {
    pub statement: ForallFact,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyForallFactWithIffResult {
    pub statement: ForallFactWithIff,
    pub proof: SuccessFactProofResult,
}

pub struct SuccessVerifyNotForallFactResult {
    pub statement: NotForallFact,
    pub proof: SuccessFactProofResult,
}

/// Successful output of the `verify_fact` family. The variants follow the
/// same semantic split as `Fact`; each payload is a named result structure.
pub enum SuccessVerifyFactResult {
    AtomicFact(Box<SuccessVerifyAtomicFactResult>),
    ExistFact(Box<SuccessVerifyExistFactResult>),
    OrFact(Box<SuccessVerifyOrFactResult>),
    AndFact(Box<SuccessVerifyAndFactResult>),
    ChainFact(Box<SuccessVerifyChainFactResult>),
    ForallFact(Box<SuccessVerifyForallFactResult>),
    ForallFactWithIff(Box<SuccessVerifyForallFactWithIffResult>),
    NotForallFact(Box<SuccessVerifyNotForallFactResult>),
}

impl SuccessVerifyFactResult {
    pub fn new(statement: Fact, proof: SuccessFactProofResult) -> Self {
        match statement {
            Fact::AtomicFact(statement) => {
                Self::AtomicFact(Box::new(SuccessVerifyAtomicFactResult { statement, proof }))
            }
            Fact::ExistFact(statement) => {
                Self::ExistFact(Box::new(SuccessVerifyExistFactResult { statement, proof }))
            }
            Fact::OrFact(statement) => {
                Self::OrFact(Box::new(SuccessVerifyOrFactResult { statement, proof }))
            }
            Fact::AndFact(statement) => {
                Self::AndFact(Box::new(SuccessVerifyAndFactResult { statement, proof }))
            }
            Fact::ChainFact(statement) => {
                Self::ChainFact(Box::new(SuccessVerifyChainFactResult { statement, proof }))
            }
            Fact::ForallFact(statement) => {
                Self::ForallFact(Box::new(SuccessVerifyForallFactResult { statement, proof }))
            }
            Fact::ForallFactWithIff(statement) => {
                Self::ForallFactWithIff(Box::new(SuccessVerifyForallFactWithIffResult {
                    statement,
                    proof,
                }))
            }
            Fact::NotForall(statement) => {
                Self::NotForallFact(Box::new(SuccessVerifyNotForallFactResult {
                    statement,
                    proof,
                }))
            }
        }
    }

    pub fn fact(&self) -> Fact {
        match self {
            Self::AtomicFact(result) => result.statement.clone().into(),
            Self::ExistFact(result) => result.statement.clone().into(),
            Self::OrFact(result) => result.statement.clone().into(),
            Self::AndFact(result) => result.statement.clone().into(),
            Self::ChainFact(result) => result.statement.clone().into(),
            Self::ForallFact(result) => result.statement.clone().into(),
            Self::ForallFactWithIff(result) => result.statement.clone().into(),
            Self::NotForallFact(result) => result.statement.clone().into(),
        }
    }

    pub fn proof(&self) -> &SuccessFactProofResult {
        match self {
            Self::AtomicFact(result) => &result.proof,
            Self::ExistFact(result) => &result.proof,
            Self::OrFact(result) => &result.proof,
            Self::AndFact(result) => &result.proof,
            Self::ChainFact(result) => &result.proof,
            Self::ForallFact(result) => &result.proof,
            Self::ForallFactWithIff(result) => &result.proof,
            Self::NotForallFact(result) => &result.proof,
        }
    }

    pub fn proof_mut(&mut self) -> &mut SuccessFactProofResult {
        match self {
            Self::AtomicFact(result) => &mut result.proof,
            Self::ExistFact(result) => &mut result.proof,
            Self::OrFact(result) => &mut result.proof,
            Self::AndFact(result) => &mut result.proof,
            Self::ChainFact(result) => &mut result.proof,
            Self::ForallFact(result) => &mut result.proof,
            Self::ForallFactWithIff(result) => &mut result.proof,
            Self::NotForallFact(result) => &mut result.proof,
        }
    }

    pub fn is_verified_by_builtin_rules_only(&self) -> bool {
        self.proof().tree_is_builtin_rules_only()
    }

    pub fn into_parts(self) -> (Fact, SuccessFactProofResult) {
        match self {
            Self::AtomicFact(result) => (result.statement.into(), result.proof),
            Self::ExistFact(result) => (result.statement.into(), result.proof),
            Self::OrFact(result) => (result.statement.into(), result.proof),
            Self::AndFact(result) => (result.statement.into(), result.proof),
            Self::ChainFact(result) => (result.statement.into(), result.proof),
            Self::ForallFact(result) => (result.statement.into(), result.proof),
            Self::ForallFactWithIff(result) => (result.statement.into(), result.proof),
            Self::NotForallFact(result) => (result.statement.into(), result.proof),
        }
    }
}

impl fmt::Debug for SuccessVerifyFactResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessVerifyFactResult")
            .field("statement", &self.fact().to_string())
            .field("proof", self.proof())
            .finish()
    }
}

/// Successful output of executing one fact statement. Verification is a
/// recursive child result.
#[derive(Clone, Debug)]
pub struct SuccessStoreFactResult {
    /// Exact proposition whose store operation this node records.
    pub fact: Fact,
    /// Exact identity assigned when the source fact is stored. Proof-only
    /// child results deliberately retain `None`.
    pub fact_id: Option<FactId>,
    /// Ordered store/infer output produced after verification. This remains the
    /// existing `SuccessInferResult` payload during the infer-rule migration, but it
    /// is now owned by the store layer rather than the statement root.
    pub infers: SuccessInferResult,
}

#[derive(Debug, Default)]
pub struct SuccessVerifyFactWellDefinedResult {
    pub recursive: Option<Box<SuccessVerifyFactWellDefinedProofResult>>,
}

impl SuccessVerifyFactWellDefinedResult {
    pub fn new_recursive(recursive: SuccessVerifyFactWellDefinedProofResult) -> Self {
        Self {
            recursive: Some(Box::new(recursive)),
        }
    }
}

impl SuccessStoreFactResult {
    pub fn new(fact: Fact, infers: SuccessInferResult) -> Self {
        Self {
            fact,
            fact_id: None,
            infers,
        }
    }
}

/// Successful output of executing one fact statement. Verification and store
/// are explicit child results owned by the statement layer.
pub struct SuccessFactStmtResult {
    pub verification: Rc<SuccessVerifyFactResult>,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
    pub store: SuccessStoreFactResult,
    pub execution_trace: Option<StatementExecutionTrace>,
}

impl SuccessFactStmtResult {
    pub fn new(statement: Fact, infers: SuccessInferResult, proof: SuccessFactProofResult) -> Self {
        Self {
            verification: Rc::new(SuccessVerifyFactResult::new(statement.clone(), proof)),
            well_definedness: SuccessVerifyFactWellDefinedResult::default(),
            store: SuccessStoreFactResult::new(statement, infers),
            execution_trace: None,
        }
    }

    pub fn fact(&self) -> Fact {
        self.verification.as_ref().fact()
    }

    pub fn proof(&self) -> &SuccessFactProofResult {
        self.verification.as_ref().proof()
    }

    pub fn with_verified_fact(mut self, statement: Fact) -> Self {
        let source = self.verification;
        self.verification = Rc::new(SuccessVerifyFactResult::new(
            statement.clone(),
            SuccessFactProofResult::Reuse(Box::new(SuccessReuseFactProofResult { source })),
        ));
        self.store.fact = statement;
        self
    }
}

impl Deref for SuccessFactStmtResult {
    type Target = SuccessStoreFactResult;

    fn deref(&self) -> &Self::Target {
        &self.store
    }
}

impl DerefMut for SuccessFactStmtResult {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.store
    }
}

impl fmt::Debug for SuccessFactStmtResult {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("SuccessFactStmtResult")
            .field("verification", &self.verification)
            .field("well_definedness", &self.well_definedness)
            .field("store", &self.store)
            .field("execution_trace", &self.execution_trace)
            .finish()
    }
}

/// Canonical successful statement result. Its shape mirrors `Stmt` recursively;
/// statement-specific evidence is owned only by the matching leaf variant.
pub struct SuccessDefAlgoStmtResult {
    pub statement: DefAlgoStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessDefThmStmtResult {
    pub statement: DefThmStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyTheoremResult>,
}

pub struct SuccessAxiomStmtResult {
    pub statement: AxiomStmt,
    pub common: SuccessStmtCommonResult,
    pub well_definedness: Option<SuccessVerifyFactWellDefinedResult>,
}

pub struct SuccessDefStrategyStmtResult {
    pub statement: DefStrategyStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyStrategyDefinitionResult>,
}

pub enum SuccessStmtResult {
    Fact(Box<SuccessFactStmtResult>),
    UnsafeStmt(SuccessUnsafeStmtResult),
    DefObjStmt(SuccessDefObjStmtResult),
    DefPredicateStmt(SuccessDefPredicateStmtResult),
    DefInterfaceStmt(SuccessDefInterfaceStmtResult),
    DefAlgoStmt(Box<SuccessDefAlgoStmtResult>),
    DefThmStmt(Box<SuccessDefThmStmtResult>),
    AxiomStmt(Box<SuccessAxiomStmtResult>),
    DefStrategyStmt(Box<SuccessDefStrategyStmtResult>),
    By(SuccessByStmtResult),
    Witness(SuccessWitnessStmtResult),
    ProofBlock(SuccessProofBlockStmtResult),
    Command(SuccessCommandStmtResult),
}

pub struct SuccessTrustStmtResult {
    pub statement: TrustStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessTrustHaveStmtResult {
    pub statement: TrustHaveStmt,
    pub common: SuccessStmtCommonResult,
}

pub enum SuccessUnsafeStmtResult {
    TrustStmt(Box<SuccessTrustStmtResult>),
    TrustHaveStmt(Box<SuccessTrustHaveStmtResult>),
}

pub struct SuccessLetObjStmtResult {
    pub statement: LetObjStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessHaveObjInNonemptySetStmtResult {
    pub statement: HaveObjInNonemptySetOrParamTypeStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyObjectChoiceResult>,
}

pub struct SuccessHaveObjEqualStmtResult {
    pub statement: HaveObjEqualStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyHaveObjEqualResult>,
}

pub struct SuccessHaveObjByExistFactsStmtResult {
    pub statement: HaveObjByExistFactsStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyExistentialEliminationResult>,
}

pub struct SuccessObtainObjFromExistFactResult {
    pub statement: ObtainObjFromExistFact,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyExistentialEliminationResult>,
}

pub struct SuccessObtainObjFromAtomicFactResult {
    pub statement: ObtainObjFromAtomicFact,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyExistentialEliminationResult>,
}

pub struct SuccessObtainObjFromThmResult {
    pub statement: ObtainObjFromThm,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyExistentialEliminationResult>,
}

pub struct SuccessHaveByPreimageStmtResult {
    pub statement: HaveByPreimageStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyPreimageResult>,
}

pub struct SuccessHaveFnEqualStmtResult {
    pub statement: HaveFnEqualStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyFunctionDefinitionResult>,
}

pub struct SuccessHaveFnEqualCaseByCaseStmtResult {
    pub statement: HaveFnEqualCaseByCaseStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyCaseFunctionDefinitionResult>,
}

pub struct SuccessHaveFnByInducStmtResult {
    pub statement: HaveFnByInducStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessHaveFnByForallExistUniqueStmtResult {
    pub statement: HaveFnByForallExistUniqueStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyFunctionFromUniqueExistenceResult>,
}

pub struct SuccessHaveTupleStmtResult {
    pub statement: HaveTupleStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyTupleOrCartDefinitionResult>,
}

pub struct SuccessHaveCartStmtResult {
    pub statement: HaveCartStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyTupleOrCartDefinitionResult>,
}

pub struct SuccessHaveSeqStmtResult {
    pub statement: HaveSeqStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyIndexedFunctionDefinitionResult>,
}

pub struct SuccessHaveFiniteSeqStmtResult {
    pub statement: HaveFiniteSeqStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyIndexedFunctionDefinitionResult>,
}

pub struct SuccessHaveMatrixStmtResult {
    pub statement: HaveMatrixStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyIndexedFunctionDefinitionResult>,
}

pub enum SuccessDefObjStmtResult {
    LetObjStmt(Box<SuccessLetObjStmtResult>),
    HaveObjInNonemptySetStmt(Box<SuccessHaveObjInNonemptySetStmtResult>),
    HaveObjEqualStmt(Box<SuccessHaveObjEqualStmtResult>),
    HaveObjByExistFactsStmt(Box<SuccessHaveObjByExistFactsStmtResult>),
    ObtainObjFromExistFact(Box<SuccessObtainObjFromExistFactResult>),
    ObtainObjFromAtomicFact(Box<SuccessObtainObjFromAtomicFactResult>),
    ObtainObjFromThm(Box<SuccessObtainObjFromThmResult>),
    HaveByPreimageStmt(Box<SuccessHaveByPreimageStmtResult>),
    HaveFnEqualStmt(Box<SuccessHaveFnEqualStmtResult>),
    HaveFnEqualCaseByCaseStmt(Box<SuccessHaveFnEqualCaseByCaseStmtResult>),
    HaveFnByInducStmt(Box<SuccessHaveFnByInducStmtResult>),
    HaveFnByForallExistUniqueStmt(Box<SuccessHaveFnByForallExistUniqueStmtResult>),
    HaveTupleStmt(Box<SuccessHaveTupleStmtResult>),
    HaveCartStmt(Box<SuccessHaveCartStmtResult>),
    HaveSeqStmt(Box<SuccessHaveSeqStmtResult>),
    HaveFiniteSeqStmt(Box<SuccessHaveFiniteSeqStmtResult>),
    HaveMatrixStmt(Box<SuccessHaveMatrixStmtResult>),
}

pub struct SuccessDefPropStmtResult {
    pub statement: DefPropStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessDefAbstractPropStmtResult {
    pub statement: DefAbstractPropStmt,
    pub common: SuccessStmtCommonResult,
}

pub enum SuccessDefPredicateStmtResult {
    DefPropStmt(Box<SuccessDefPropStmtResult>),
    DefAbstractPropStmt(Box<SuccessDefAbstractPropStmtResult>),
}

pub struct SuccessDefSettingStmtResult {
    pub statement: DefSettingStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessDefTemplateStmtResult {
    pub statement: DefTemplateStmt,
    pub template_parameter_groups: Vec<SuccessVerifyFactParameterGroupResult>,
    pub template_domain_results: Vec<SuccessVerifyLocalFactWellDefinedResult>,
    pub body_statement_result: Box<SuccessStmtResult>,
}

pub struct SuccessDefStructStmtResult {
    pub statement: DefStructStmt,
    pub common: SuccessStmtCommonResult,
}

pub enum SuccessDefInterfaceStmtResult {
    DefSettingStmt(Box<SuccessDefSettingStmtResult>),
    DefTemplateStmt(Box<SuccessDefTemplateStmtResult>),
    DefStructStmt(Box<SuccessDefStructStmtResult>),
}

pub struct SuccessByCasesStmtResult {
    pub statement: ByCasesStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByCasesResult>,
}

pub struct SuccessByContraStmtResult {
    pub statement: ByContraStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByContraResult>,
}

pub struct SuccessByEnumerateFiniteSetStmtResult {
    pub statement: ByEnumerateFiniteSetStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByEnumerateFiniteSetResult>,
}

pub struct SuccessByFiniteSetInducStmtResult {
    pub statement: ByFiniteSetInducStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByInducResult>,
}

pub struct SuccessByInducStmtResult {
    pub statement: ByInducStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByInducResult>,
}

pub struct SuccessByForStmtResult {
    pub statement: ByForStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByForResult>,
}

pub struct SuccessByExtensionStmtResult {
    pub statement: ByExtensionStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByExtensionResult>,
}

pub struct SuccessByEnumerateRangeStmtResult {
    pub statement: ByEnumerateRangeStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByEnumerateRangeResult>,
}

pub struct SuccessByClosedRangeAsCasesStmtResult {
    pub statement: ByClosedRangeAsCasesStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByEnumerateRangeResult>,
}

pub struct SuccessByTransitivePropStmtResult {
    pub statement: ByTransitivePropStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByPropRegistrationResult>,
}

pub struct SuccessBySymmetricPropStmtResult {
    pub statement: BySymmetricPropStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByPropRegistrationResult>,
}

pub struct SuccessByReflexivePropStmtResult {
    pub statement: ByReflexivePropStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByPropRegistrationResult>,
}

pub struct SuccessByAntisymmetricPropStmtResult {
    pub statement: ByAntisymmetricPropStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByPropRegistrationResult>,
}

pub struct SuccessByZornLemmaStmtResult {
    pub statement: ByZornLemmaStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByChoiceResult>,
}

pub struct SuccessByAxiomOfChoiceStmtResult {
    pub statement: ByAxiomOfChoiceStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByChoiceResult>,
}

pub struct SuccessByRegularityAxiomStmtResult {
    pub statement: ByRegularityAxiomStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByChoiceResult>,
}

pub struct SuccessByDefStmtResult {
    pub statement: ByDefStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByDefinitionResult>,
}

pub struct SuccessByStructDefStmtResult {
    pub statement: ByStructDefStmt,
    pub common: SuccessStmtCommonResult,
    pub membership_check: Option<Box<StmtResult>>,
}

pub struct SuccessByThmStmtResult {
    pub statement: ByThmStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyByTheoremResult>,
}

pub enum SuccessByStmtResult {
    ByCasesStmt(Box<SuccessByCasesStmtResult>),
    ByContraStmt(Box<SuccessByContraStmtResult>),
    ByEnumerateFiniteSetStmt(Box<SuccessByEnumerateFiniteSetStmtResult>),
    ByFiniteSetInducStmt(Box<SuccessByFiniteSetInducStmtResult>),
    ByInducStmt(Box<SuccessByInducStmtResult>),
    ByForStmt(Box<SuccessByForStmtResult>),
    ByExtensionStmt(Box<SuccessByExtensionStmtResult>),
    ByEnumerateRangeStmt(Box<SuccessByEnumerateRangeStmtResult>),
    ByClosedRangeAsCasesStmt(Box<SuccessByClosedRangeAsCasesStmtResult>),
    ByTransitivePropStmt(Box<SuccessByTransitivePropStmtResult>),
    BySymmetricPropStmt(Box<SuccessBySymmetricPropStmtResult>),
    ByReflexivePropStmt(Box<SuccessByReflexivePropStmtResult>),
    ByAntisymmetricPropStmt(Box<SuccessByAntisymmetricPropStmtResult>),
    ByZornLemmaStmt(Box<SuccessByZornLemmaStmtResult>),
    ByAxiomOfChoiceStmt(Box<SuccessByAxiomOfChoiceStmtResult>),
    ByRegularityAxiomStmt(Box<SuccessByRegularityAxiomStmtResult>),
    ByDefStmt(Box<SuccessByDefStmtResult>),
    ByStructDefStmt(Box<SuccessByStructDefStmtResult>),
    ByThmStmt(Box<SuccessByThmStmtResult>),
}

pub struct SuccessWitnessExistFactResult {
    pub statement: WitnessExistFact,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyWitnessExistResult>,
}

pub struct SuccessWitnessAtomicFactResult {
    pub statement: WitnessAtomicFact,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyWitnessAtomicFactResult>,
}

pub struct SuccessWitnessNonemptySetResult {
    pub statement: WitnessNonemptySet,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyWitnessNonemptySetResult>,
}

pub struct SuccessVerifyWitnessNonemptySetResult {
    pub proof_steps: Vec<StmtResult>,
    pub nonempty_check: Box<StmtResult>,
}

pub enum SuccessWitnessStmtResult {
    WitnessExistFact(Box<SuccessWitnessExistFactResult>),
    WitnessAtomicFact(Box<SuccessWitnessAtomicFactResult>),
    WitnessNonemptySet(Box<SuccessWitnessNonemptySetResult>),
}

pub struct SuccessClaimStmtResult {
    pub statement: ClaimStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyClaimResult>,
}

pub struct SuccessExampleStmtResult {
    pub statement: ExampleStmt,
    pub common: SuccessStmtCommonResult,
    pub verification: Option<SuccessVerifyClaimResult>,
}

pub struct SuccessSketchProofResult {
    pub proof_scope: SuccessVerifyLocalProofScopeResult,
    pub proof_steps: Vec<StmtResult>,
}

pub struct SuccessSketchStmtResult {
    pub statement: SketchStmt,
    pub common: SuccessStmtCommonResult,
    pub proof: Option<SuccessSketchProofResult>,
}

pub struct SuccessTryProofResult {
    pub proof_steps: Vec<StmtResult>,
}

pub struct SuccessTryStmtResult {
    pub statement: TryStmt,
    pub common: SuccessStmtCommonResult,
    pub proof: Option<SuccessTryProofResult>,
}

pub enum SuccessProofBlockStmtResult {
    ClaimStmt(Box<SuccessClaimStmtResult>),
    ExampleStmt(Box<SuccessExampleStmtResult>),
    SketchStmt(Box<SuccessSketchStmtResult>),
    TryStmt(Box<SuccessTryStmtResult>),
}

pub struct SuccessImportStmtResult {
    pub statement: ImportStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessDoNothingStmtResult {
    pub statement: DoNothingStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessClearStmtResult {
    pub statement: ClearStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessEvalStmtResult {
    pub statement: EvalStmt,
    pub common: SuccessStmtCommonResult,
    /// The execution layer selected for this `eval`. A trusted-prefix pass can
    /// deliberately skip evaluation; ordinary execution owns the exact source
    /// and resulting object and, when available, the recursive numeric
    /// computation selected by the evaluator.
    pub execution: SuccessEvalStmtExecutionResult,
}

pub enum SuccessEvalStmtExecutionResult {
    SkippedByTrustedPrefix,
    Evaluated(Box<SuccessEvaluatedEvalStmtResult>),
}

pub struct SuccessEvaluatedEvalStmtResult {
    pub source_object: Obj,
    pub evaluated_object: Obj,
    /// Closed numeric evaluation already has a complete recursive result.
    /// Other runtime algorithms remain explicit but fail closed in the
    /// standalone compiler until they gain their own typed computation tree.
    pub recursive_numeric_evaluation: Option<SuccessEvaluateObjResult>,
}

pub struct SuccessUseStrategyStmtResult {
    pub statement: UseStrategyStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessStopStrategyStmtResult {
    pub statement: StopStrategyStmt,
    pub common: SuccessStmtCommonResult,
}

pub enum SuccessCommandStmtResult {
    ImportStmt(Box<SuccessImportStmtResult>),
    DoNothingStmt(Box<SuccessDoNothingStmtResult>),
    ClearStmt(Box<SuccessClearStmtResult>),
    EvalStmt(Box<SuccessEvalStmtResult>),
    UseStrategyStmt(Box<SuccessUseStrategyStmtResult>),
    StopStrategyStmt(Box<SuccessStopStrategyStmtResult>),
}

impl fmt::Debug for SuccessStmtResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Self::Fact(result) = self {
            return f.debug_tuple("Fact").field(result).finish();
        }
        f.debug_struct("SuccessStmtResult")
            .field("statement", &self.statement())
            .field("common", &self.common())
            .finish()
    }
}

impl SuccessStmtResult {
    /// Visits the immediate successful composition children retained by this
    /// statement result. During the statement-family migration, legacy
    /// families still expose their ordered children through `common`; migrated
    /// families expose named recursive fields here.
    pub fn visit_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        if let Self::ProofBlock(proof_block) = self {
            proof_block.visit_named_child_results(visitor);
        }
        if let Self::DefObjStmt(def_obj) = self {
            def_obj.visit_named_child_results(visitor);
        }
        if let Self::DefThmStmt(result) = self {
            if let Some(verification) = &result.verification {
                for step in &verification.proof_steps {
                    visitor(step);
                }
                for check in &verification.conclusion_checks {
                    visitor(check);
                }
            }
        }
        if let Self::DefStrategyStmt(result) = self {
            if let Some(verification) = &result.verification {
                for step in &verification.proof_steps {
                    visitor(step);
                }
                for check in &verification.conclusion_checks {
                    visitor(check);
                }
            }
        }
        if let Self::Witness(witness) = self {
            witness.visit_named_child_results(visitor);
        }
        if let Self::By(by) = self {
            by.visit_named_child_results(visitor);
        }
    }

    pub fn try_visit_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        if let Self::ProofBlock(proof_block) = self {
            proof_block.try_visit_named_child_results_mut(visitor)?;
        }
        if let Self::DefObjStmt(def_obj) = self {
            def_obj.try_visit_named_child_results_mut(visitor)?;
        }
        if let Self::DefThmStmt(result) = self {
            if let Some(verification) = &mut result.verification {
                for step in &mut verification.proof_steps {
                    visitor(step)?;
                }
                for check in &mut verification.conclusion_checks {
                    visitor(check)?;
                }
            }
        }
        if let Self::DefStrategyStmt(result) = self {
            if let Some(verification) = &mut result.verification {
                for step in &mut verification.proof_steps {
                    visitor(step)?;
                }
                for check in &mut verification.conclusion_checks {
                    visitor(check)?;
                }
            }
        }
        if let Self::Witness(witness) = self {
            witness.try_visit_named_child_results_mut(visitor)?;
        }
        if let Self::By(by) = self {
            by.try_visit_named_child_results_mut(visitor)?;
        }
        Ok(())
    }

    pub fn visit_success_child_results(&self, visitor: &mut impl FnMut(&SuccessStmtResult)) {
        if let Self::DefInterfaceStmt(SuccessDefInterfaceStmtResult::DefTemplateStmt(result)) = self
        {
            visitor(&result.body_statement_result);
        }
    }

    pub fn try_visit_success_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut SuccessStmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        if let Self::DefInterfaceStmt(SuccessDefInterfaceStmtResult::DefTemplateStmt(result)) = self
        {
            visitor(&mut result.body_statement_result)?;
        }
        Ok(())
    }

    pub fn statement(&self) -> Stmt {
        match self {
            Self::Fact(statement) => statement.fact().into(),
            Self::UnsafeStmt(statement) => statement.statement(),
            Self::DefObjStmt(statement) => statement.statement(),
            Self::DefPredicateStmt(statement) => statement.statement(),
            Self::DefInterfaceStmt(statement) => statement.statement(),
            Self::DefAlgoStmt(result) => result.statement.clone().into(),
            Self::DefThmStmt(result) => result.statement.clone().into(),
            Self::AxiomStmt(result) => result.statement.clone().into(),
            Self::DefStrategyStmt(result) => result.statement.clone().into(),
            Self::By(statement) => statement.statement(),
            Self::Witness(statement) => statement.statement(),
            Self::ProofBlock(statement) => statement.statement(),
            Self::Command(statement) => statement.statement(),
        }
    }

    pub fn fact(&self) -> Option<&SuccessFactStmtResult> {
        match self {
            Self::Fact(statement) => Some(statement),
            _ => None,
        }
    }

    pub fn fact_mut(&mut self) -> Option<&mut SuccessFactStmtResult> {
        match self {
            Self::Fact(statement) => Some(statement),
            _ => None,
        }
    }

    pub fn common(&self) -> Option<&SuccessStmtCommonResult> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.common()),
            Self::DefObjStmt(statement) => Some(statement.common()),
            Self::DefPredicateStmt(statement) => Some(statement.common()),
            Self::DefInterfaceStmt(statement) => statement.common(),
            Self::DefAlgoStmt(result) => Some(&result.common),
            Self::DefThmStmt(result) => Some(&result.common),
            Self::AxiomStmt(result) => Some(&result.common),
            Self::DefStrategyStmt(result) => Some(&result.common),
            Self::By(statement) => Some(statement.common()),
            Self::Witness(statement) => Some(statement.common()),
            Self::ProofBlock(statement) => Some(statement.common()),
            Self::Command(statement) => Some(statement.common()),
        }
    }

    pub fn common_mut(&mut self) -> Option<&mut SuccessStmtCommonResult> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.common_mut()),
            Self::DefObjStmt(statement) => Some(statement.common_mut()),
            Self::DefPredicateStmt(statement) => Some(statement.common_mut()),
            Self::DefInterfaceStmt(statement) => statement.common_mut(),
            Self::DefAlgoStmt(result) => Some(&mut result.common),
            Self::DefThmStmt(result) => Some(&mut result.common),
            Self::AxiomStmt(result) => Some(&mut result.common),
            Self::DefStrategyStmt(result) => Some(&mut result.common),
            Self::By(statement) => Some(statement.common_mut()),
            Self::Witness(statement) => Some(statement.common_mut()),
            Self::ProofBlock(statement) => Some(statement.common_mut()),
            Self::Command(statement) => Some(statement.common_mut()),
        }
    }

    pub fn into_common(self) -> Option<SuccessStmtCommonResult> {
        match self {
            Self::Fact(_) => None,
            Self::UnsafeStmt(statement) => Some(statement.into_common()),
            Self::DefObjStmt(statement) => Some(statement.into_common()),
            Self::DefPredicateStmt(statement) => Some(statement.into_common()),
            Self::DefInterfaceStmt(statement) => statement.into_common(),
            Self::DefAlgoStmt(result) => Some(result.common),
            Self::DefThmStmt(result) => Some(result.common),
            Self::AxiomStmt(result) => Some(result.common),
            Self::DefStrategyStmt(result) => Some(result.common),
            Self::By(statement) => Some(statement.into_common()),
            Self::Witness(statement) => Some(statement.into_common()),
            Self::ProofBlock(statement) => Some(statement.into_common()),
            Self::Command(statement) => Some(statement.into_common()),
        }
    }

    pub fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::Fact(_) => Vec::new(),
            Self::ProofBlock(proof_block) => proof_block.into_child_results(),
            Self::DefObjStmt(def_obj) => def_obj.into_child_results(),
            Self::DefInterfaceStmt(SuccessDefInterfaceStmtResult::DefTemplateStmt(result)) => {
                vec![(*result.body_statement_result).into()]
            }
            Self::DefThmStmt(result) => result
                .verification
                .map(|verification| {
                    let mut children = verification.proof_steps;
                    children.extend(verification.conclusion_checks);
                    children
                })
                .unwrap_or_default(),
            Self::DefStrategyStmt(result) => result
                .verification
                .map(|verification| {
                    let mut children = verification.proof_steps;
                    children.extend(verification.conclusion_checks);
                    children
                })
                .unwrap_or_default(),
            Self::Witness(witness) => witness.into_child_results(),
            Self::By(by) => by.into_child_results(),
            _other => Vec::new(),
        }
    }
}

impl SuccessByStmtResult {
    fn visit_named_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        match self {
            Self::ByCasesStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.coverage_check);
                    for branch in &verification.branches {
                        for step in &branch.proof_steps {
                            visitor(step);
                        }
                        match &branch.exit {
                            SuccessVerifyByCaseBranchExitResult::Conclusions(result) => {
                                for check in &result.checks {
                                    visitor(check);
                                }
                            }
                            SuccessVerifyByCaseBranchExitResult::Contradiction(result) => {
                                visitor(&result.contradiction.impossible_check);
                                visitor(&result.contradiction.negated_impossible_check);
                            }
                        }
                    }
                }
            }
            Self::ByContraStmt(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor(step);
                    }
                    visitor(&verification.contradiction.impossible_check);
                    visitor(&verification.contradiction.negated_impossible_check);
                }
            }
            Self::ByEnumerateFiniteSetStmt(result) => {
                if let Some(verification) = &result.verification {
                    for assignment in &verification.assignments {
                        visit_assignment_children(assignment, visitor);
                    }
                }
            }
            Self::ByFiniteSetInducStmt(result) => {
                visit_induc_children(result.verification.as_ref(), visitor)
            }
            Self::ByInducStmt(result) => {
                visit_induc_children(result.verification.as_ref(), visitor)
            }
            Self::ByForStmt(result) => {
                if let Some(verification) = &result.verification {
                    for assignment in verification.assignments() {
                        visit_assignment_children(assignment, visitor);
                    }
                }
            }
            Self::ByEnumerateRangeStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.membership_check);
                    for check in &verification.endpoint_checks {
                        visitor(&check.verification);
                    }
                }
            }
            Self::ByClosedRangeAsCasesStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.membership_check);
                    for check in &verification.endpoint_checks {
                        visitor(&check.verification);
                    }
                }
            }
            Self::ByExtensionStmt(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor(step);
                    }
                    visitor(&verification.left_to_right_check);
                    visitor(&verification.right_to_left_check);
                }
            }
            Self::ByTransitivePropStmt(result) => {
                visit_prop_registration_children(result.verification.as_ref(), visitor)
            }
            Self::BySymmetricPropStmt(result) => {
                visit_prop_registration_children(result.verification.as_ref(), visitor)
            }
            Self::ByReflexivePropStmt(result) => {
                visit_prop_registration_children(result.verification.as_ref(), visitor)
            }
            Self::ByAntisymmetricPropStmt(result) => {
                visit_prop_registration_children(result.verification.as_ref(), visitor)
            }
            Self::ByZornLemmaStmt(result) => {
                visit_choice_children(result.verification.as_ref(), visitor)
            }
            Self::ByAxiomOfChoiceStmt(result) => {
                visit_choice_children(result.verification.as_ref(), visitor)
            }
            Self::ByRegularityAxiomStmt(result) => {
                visit_choice_children(result.verification.as_ref(), visitor)
            }
            Self::ByDefStmt(result) => {
                if let Some(verification) = &result.verification {
                    if let Some(arguments) = &verification.argument_verification {
                        for check in &arguments.checks {
                            visitor(check);
                        }
                    }
                    for check in &verification.clause_checks {
                        visitor(check);
                    }
                }
            }
            Self::ByStructDefStmt(result) => {
                if let Some(check) = &result.membership_check {
                    visitor(check);
                }
            }
            Self::ByThmStmt(result) => {
                if let Some(verification) = &result.verification {
                    if let Some(arguments) = &verification.argument_verification {
                        for check in &arguments.checks {
                            visitor(check);
                        }
                    }
                    for check in &verification.requirement_checks {
                        visitor(check);
                    }
                    for check in &verification.domain_checks {
                        visitor(check);
                    }
                    if let Some(check) = &verification.selected_fact_check {
                        visitor(check);
                    }
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::ByCasesStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.coverage_check)?;
                    for branch in &mut verification.branches {
                        for step in &mut branch.proof_steps {
                            visitor(step)?;
                        }
                        match &mut branch.exit {
                            SuccessVerifyByCaseBranchExitResult::Conclusions(result) => {
                                for check in &mut result.checks {
                                    visitor(check)?;
                                }
                            }
                            SuccessVerifyByCaseBranchExitResult::Contradiction(result) => {
                                visitor(&mut result.contradiction.impossible_check)?;
                                visitor(&mut result.contradiction.negated_impossible_check)?;
                            }
                        }
                    }
                }
            }
            Self::ByContraStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor(step)?;
                    }
                    visitor(&mut verification.contradiction.impossible_check)?;
                    visitor(&mut verification.contradiction.negated_impossible_check)?;
                }
            }
            Self::ByEnumerateFiniteSetStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for assignment in &mut verification.assignments {
                        try_visit_assignment_children_mut(assignment, visitor)?;
                    }
                }
            }
            Self::ByFiniteSetInducStmt(result) => {
                try_visit_induc_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByInducStmt(result) => {
                try_visit_induc_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByForStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for assignment in verification.assignments_mut() {
                        try_visit_assignment_children_mut(assignment, visitor)?;
                    }
                }
            }
            Self::ByEnumerateRangeStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.membership_check)?;
                    for check in &mut verification.endpoint_checks {
                        visitor(&mut check.verification)?;
                    }
                }
            }
            Self::ByClosedRangeAsCasesStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.membership_check)?;
                    for check in &mut verification.endpoint_checks {
                        visitor(&mut check.verification)?;
                    }
                }
            }
            Self::ByExtensionStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor(step)?;
                    }
                    visitor(&mut verification.left_to_right_check)?;
                    visitor(&mut verification.right_to_left_check)?;
                }
            }
            Self::ByTransitivePropStmt(result) => {
                try_visit_prop_registration_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::BySymmetricPropStmt(result) => {
                try_visit_prop_registration_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByReflexivePropStmt(result) => {
                try_visit_prop_registration_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByAntisymmetricPropStmt(result) => {
                try_visit_prop_registration_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByZornLemmaStmt(result) => {
                try_visit_choice_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByAxiomOfChoiceStmt(result) => {
                try_visit_choice_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByRegularityAxiomStmt(result) => {
                try_visit_choice_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::ByDefStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    if let Some(arguments) = &mut verification.argument_verification {
                        for check in &mut arguments.checks {
                            visitor(check)?;
                        }
                    }
                    for check in &mut verification.clause_checks {
                        visitor(check)?;
                    }
                }
            }
            Self::ByStructDefStmt(result) => {
                if let Some(check) = &mut result.membership_check {
                    visitor(check)?;
                }
            }
            Self::ByThmStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    if let Some(arguments) = &mut verification.argument_verification {
                        for check in &mut arguments.checks {
                            visitor(check)?;
                        }
                    }
                    for check in &mut verification.requirement_checks {
                        visitor(check)?;
                    }
                    for check in &mut verification.domain_checks {
                        visitor(check)?;
                    }
                    if let Some(check) = &mut verification.selected_fact_check {
                        visitor(check)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::ByCasesStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.coverage_check);
                    for branch in verification.branches {
                        children.extend(branch.proof_steps);
                        match branch.exit {
                            SuccessVerifyByCaseBranchExitResult::Conclusions(result) => {
                                children.extend(result.checks);
                            }
                            SuccessVerifyByCaseBranchExitResult::Contradiction(result) => {
                                children.push(*result.contradiction.impossible_check);
                                children.push(*result.contradiction.negated_impossible_check);
                            }
                        }
                    }
                }
                children
            }
            Self::ByContraStmt(result) => result
                .verification
                .map(|verification| {
                    let mut children = verification.proof_steps;
                    children.push(*verification.contradiction.impossible_check);
                    children.push(*verification.contradiction.negated_impossible_check);
                    children
                })
                .unwrap_or_default(),
            Self::ByEnumerateFiniteSetStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    for assignment in verification.assignments {
                        children.extend(into_assignment_children(assignment));
                    }
                }
                children
            }
            Self::ByFiniteSetInducStmt(result) => {
                into_induc_children(result.common, result.verification)
            }
            Self::ByInducStmt(result) => into_induc_children(result.common, result.verification),
            Self::ByForStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    for assignment in verification.into_assignments() {
                        children.extend(into_assignment_children(assignment));
                    }
                }
                children
            }
            Self::ByEnumerateRangeStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.membership_check);
                    children.extend(
                        verification
                            .endpoint_checks
                            .into_iter()
                            .map(|check| *check.verification),
                    );
                }
                children
            }
            Self::ByClosedRangeAsCasesStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.membership_check);
                    children.extend(
                        verification
                            .endpoint_checks
                            .into_iter()
                            .map(|check| *check.verification),
                    );
                }
                children
            }
            Self::ByExtensionStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.extend(verification.proof_steps);
                    children.push(*verification.left_to_right_check);
                    children.push(*verification.right_to_left_check);
                }
                children
            }
            Self::ByTransitivePropStmt(result) => {
                into_prop_registration_children(result.common, result.verification)
            }
            Self::BySymmetricPropStmt(result) => {
                into_prop_registration_children(result.common, result.verification)
            }
            Self::ByReflexivePropStmt(result) => {
                into_prop_registration_children(result.common, result.verification)
            }
            Self::ByAntisymmetricPropStmt(result) => {
                into_prop_registration_children(result.common, result.verification)
            }
            Self::ByZornLemmaStmt(result) => {
                into_choice_children(result.common, result.verification)
            }
            Self::ByAxiomOfChoiceStmt(result) => {
                into_choice_children(result.common, result.verification)
            }
            Self::ByRegularityAxiomStmt(result) => {
                into_choice_children(result.common, result.verification)
            }
            Self::ByDefStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    if let Some(arguments) = verification.argument_verification {
                        children.extend(arguments.checks);
                    }
                    children.extend(verification.clause_checks);
                }
                children
            }
            Self::ByStructDefStmt(result) => result
                .membership_check
                .into_iter()
                .map(|check| *check)
                .collect(),
            Self::ByThmStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    if let Some(arguments) = verification.argument_verification {
                        children.extend(arguments.checks);
                    }
                    children.extend(verification.requirement_checks);
                    children.extend(verification.domain_checks);
                    if let Some(check) = verification.selected_fact_check {
                        children.push(*check);
                    }
                }
                children
            }
        }
    }
}

fn visit_assignment_children(
    assignment: &SuccessVerifyByAssignmentResult,
    visitor: &mut impl FnMut(&StmtResult),
) {
    for domain in &assignment.domain_checks {
        visitor(&domain.check);
        if let Some(check) = &domain.negated_check {
            visitor(check);
        }
    }
    for step in &assignment.proof_steps {
        visitor(step);
    }
    for check in &assignment.conclusion_checks {
        visitor(check);
    }
}

fn try_visit_assignment_children_mut<E>(
    assignment: &mut SuccessVerifyByAssignmentResult,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    for domain in &mut assignment.domain_checks {
        visitor(&mut domain.check)?;
        if let Some(check) = &mut domain.negated_check {
            visitor(check)?;
        }
    }
    for step in &mut assignment.proof_steps {
        visitor(step)?;
    }
    for check in &mut assignment.conclusion_checks {
        visitor(check)?;
    }
    Ok(())
}

fn into_assignment_children(assignment: SuccessVerifyByAssignmentResult) -> Vec<StmtResult> {
    let mut children = Vec::new();
    for domain in assignment.domain_checks {
        children.push(*domain.check);
        if let Some(check) = domain.negated_check {
            children.push(*check);
        }
    }
    children.extend(assignment.proof_steps);
    children.extend(assignment.conclusion_checks);
    children
}

fn visit_prop_registration_children(
    verification: Option<&SuccessVerifyByPropRegistrationResult>,
    visitor: &mut impl FnMut(&StmtResult),
) {
    if let Some(verification) = verification {
        for step in &verification.proof_steps {
            visitor(step);
        }
        visitor(&verification.forall_check);
    }
}

fn try_visit_prop_registration_children_mut<E>(
    verification: Option<&mut SuccessVerifyByPropRegistrationResult>,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    if let Some(verification) = verification {
        for step in &mut verification.proof_steps {
            visitor(step)?;
        }
        visitor(&mut verification.forall_check)?;
    }
    Ok(())
}

fn into_prop_registration_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyByPropRegistrationResult>,
) -> Vec<StmtResult> {
    let mut children = Vec::new();
    if let Some(verification) = verification {
        children.extend(verification.proof_steps);
        children.push(*verification.forall_check);
    }
    children
}

fn visit_choice_children(
    verification: Option<&SuccessVerifyByChoiceResult>,
    visitor: &mut impl FnMut(&StmtResult),
) {
    if let Some(verification) = verification {
        for step in &verification.proof_steps {
            visitor(step);
        }
        for obligation in &verification.obligations {
            if let Some(check) = &obligation.check {
                visitor(check);
            }
        }
    }
}

fn try_visit_choice_children_mut<E>(
    verification: Option<&mut SuccessVerifyByChoiceResult>,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    if let Some(verification) = verification {
        for step in &mut verification.proof_steps {
            visitor(step)?;
        }
        for obligation in &mut verification.obligations {
            if let Some(check) = &mut obligation.check {
                visitor(check)?;
            }
        }
    }
    Ok(())
}

fn into_choice_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyByChoiceResult>,
) -> Vec<StmtResult> {
    let mut children = Vec::new();
    if let Some(verification) = verification {
        children.extend(verification.proof_steps);
        children.extend(
            verification
                .obligations
                .into_iter()
                .filter_map(|obligation| obligation.check.map(|check| *check)),
        );
    }
    children
}

fn visit_induc_children(
    verification: Option<&SuccessVerifyByInducResult>,
    visitor: &mut impl FnMut(&StmtResult),
) {
    let Some(verification) = verification else {
        return;
    };
    match &verification.proof {
        SuccessVerifyByInducProofResult::IntegerUnstructured(proof) => {
            for step in &proof.proof_steps {
                visitor(step);
            }
            for goal in &proof.goals {
                visitor(&goal.base_check);
                visitor(&goal.start_in_z_check);
                visitor(&goal.step_check);
            }
        }
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => {
            visitor(&proof.start_in_z_check);
            visit_induc_case_children(&proof.base, visitor);
            visit_induc_case_children(&proof.step, visitor);
        }
        SuccessVerifyByInducProofResult::FiniteSet(proof) => {
            visit_induc_case_children(&proof.base, visitor);
            visit_induc_case_children(&proof.step, visitor);
        }
    }
}

fn visit_induc_case_children(
    result: &SuccessVerifyByInducCaseResult,
    visitor: &mut impl FnMut(&StmtResult),
) {
    for step in &result.proof_steps {
        visitor(step);
    }
    for check in &result.conclusion_checks {
        visitor(check);
    }
}

fn try_visit_induc_children_mut<E>(
    verification: Option<&mut SuccessVerifyByInducResult>,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    let Some(verification) = verification else {
        return Ok(());
    };
    match &mut verification.proof {
        SuccessVerifyByInducProofResult::IntegerUnstructured(proof) => {
            for step in &mut proof.proof_steps {
                visitor(step)?;
            }
            for goal in &mut proof.goals {
                visitor(&mut goal.base_check)?;
                visitor(&mut goal.start_in_z_check)?;
                visitor(&mut goal.step_check)?;
            }
        }
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => {
            visitor(&mut proof.start_in_z_check)?;
            try_visit_induc_case_children_mut(&mut proof.base, visitor)?;
            try_visit_induc_case_children_mut(&mut proof.step, visitor)?;
        }
        SuccessVerifyByInducProofResult::FiniteSet(proof) => {
            try_visit_induc_case_children_mut(&mut proof.base, visitor)?;
            try_visit_induc_case_children_mut(&mut proof.step, visitor)?;
        }
    }
    Ok(())
}

fn try_visit_induc_case_children_mut<E>(
    result: &mut SuccessVerifyByInducCaseResult,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    for step in &mut result.proof_steps {
        visitor(step)?;
    }
    for check in &mut result.conclusion_checks {
        visitor(check)?;
    }
    Ok(())
}

fn into_induc_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyByInducResult>,
) -> Vec<StmtResult> {
    let mut children = Vec::new();
    let Some(verification) = verification else {
        return children;
    };
    match verification.proof {
        SuccessVerifyByInducProofResult::IntegerUnstructured(proof) => {
            children.extend(proof.proof_steps);
            for goal in proof.goals {
                children.push(*goal.base_check);
                children.push(*goal.start_in_z_check);
                children.push(*goal.step_check);
            }
        }
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => {
            children.push(*proof.start_in_z_check);
            children.extend(into_induc_case_children(proof.base));
            children.extend(into_induc_case_children(proof.step));
        }
        SuccessVerifyByInducProofResult::FiniteSet(proof) => {
            children.extend(into_induc_case_children(proof.base));
            children.extend(into_induc_case_children(proof.step));
        }
    }
    children
}

fn into_induc_case_children(result: SuccessVerifyByInducCaseResult) -> Vec<StmtResult> {
    let mut children = result.proof_steps;
    children.extend(result.conclusion_checks);
    children
}

impl SuccessWitnessStmtResult {
    fn visit_named_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        match self {
            Self::WitnessExistFact(result) => {
                if let Some(verification) = &result.verification {
                    visit_witness_exist_children(verification, visitor);
                }
            }
            Self::WitnessAtomicFact(result) => {
                if let Some(verification) = &result.verification {
                    for check in &verification.definition_parameter_verification.checks {
                        visitor(check);
                    }
                    visit_witness_exist_children(&verification.witness_verification, visitor);
                }
            }
            Self::WitnessNonemptySet(result) => {
                if let Some(verification) = &result.verification {
                    for step in &verification.proof_steps {
                        visitor(step);
                    }
                    visitor(&verification.nonempty_check);
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::WitnessExistFact(result) => {
                if let Some(verification) = &mut result.verification {
                    try_visit_witness_exist_children_mut(verification, visitor)?;
                }
            }
            Self::WitnessAtomicFact(result) => {
                if let Some(verification) = &mut result.verification {
                    for check in &mut verification.definition_parameter_verification.checks {
                        visitor(check)?;
                    }
                    try_visit_witness_exist_children_mut(
                        &mut verification.witness_verification,
                        visitor,
                    )?;
                }
            }
            Self::WitnessNonemptySet(result) => {
                if let Some(verification) = &mut result.verification {
                    for step in &mut verification.proof_steps {
                        visitor(step)?;
                    }
                    visitor(&mut verification.nonempty_check)?;
                }
            }
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::WitnessExistFact(result) => result
                .verification
                .map(into_witness_exist_children)
                .unwrap_or_default(),
            Self::WitnessAtomicFact(result) => result
                .verification
                .map(|verification| {
                    let mut children = verification.definition_parameter_verification.checks;
                    children.extend(into_witness_exist_children(
                        verification.witness_verification,
                    ));
                    children
                })
                .unwrap_or_default(),
            Self::WitnessNonemptySet(result) => result
                .verification
                .map(|verification| {
                    let mut children = verification.proof_steps;
                    children.push(*verification.nonempty_check);
                    children
                })
                .unwrap_or_default(),
        }
    }
}

fn visit_witness_exist_children(
    verification: &SuccessVerifyWitnessExistResult,
    visitor: &mut impl FnMut(&StmtResult),
) {
    for check in verification.parameter_checks.iter().flatten() {
        visitor(check);
    }
    for step in &verification.proof_steps {
        visitor(step);
    }
    for check in &verification.body_checks {
        visitor(check);
    }
    if let Some(check) = &verification.uniqueness_check {
        visitor(check);
    }
}

fn try_visit_witness_exist_children_mut<E>(
    verification: &mut SuccessVerifyWitnessExistResult,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    for check in verification.parameter_checks.iter_mut().flatten() {
        visitor(check)?;
    }
    for step in &mut verification.proof_steps {
        visitor(step)?;
    }
    for check in &mut verification.body_checks {
        visitor(check)?;
    }
    if let Some(check) = &mut verification.uniqueness_check {
        visitor(check)?;
    }
    Ok(())
}

fn into_witness_exist_children(verification: SuccessVerifyWitnessExistResult) -> Vec<StmtResult> {
    let mut children = verification
        .parameter_checks
        .into_iter()
        .flatten()
        .map(|check| *check)
        .collect::<Vec<_>>();
    children.extend(verification.proof_steps);
    children.extend(verification.body_checks);
    if let Some(check) = verification.uniqueness_check {
        children.push(*check);
    }
    children
}

impl SuccessProofBlockStmtResult {
    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::ClaimStmt(result) => claim_child_results(result.verification),
            Self::ExampleStmt(result) => claim_child_results(result.verification),
            Self::SketchStmt(result) => result
                .proof
                .map(|proof| proof.proof_steps)
                .unwrap_or_default(),
            Self::TryStmt(result) => result
                .proof
                .map(|proof| proof.proof_steps)
                .unwrap_or_default(),
        }
    }

    fn visit_named_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        match self {
            Self::ClaimStmt(result) => {
                if let Some(verification) = &result.verification {
                    verification.visit_child_results(visitor);
                }
            }
            Self::ExampleStmt(result) => {
                if let Some(verification) = &result.verification {
                    verification.visit_child_results(visitor);
                }
            }
            Self::SketchStmt(result) => {
                if let Some(proof) = &result.proof {
                    for step in &proof.proof_steps {
                        visitor(step);
                    }
                }
            }
            Self::TryStmt(result) => {
                if let Some(proof) = &result.proof {
                    for step in &proof.proof_steps {
                        visitor(step);
                    }
                }
            }
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::ClaimStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    verification.try_visit_child_results_mut(visitor)?;
                }
            }
            Self::ExampleStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    verification.try_visit_child_results_mut(visitor)?;
                }
            }
            Self::SketchStmt(result) => {
                if let Some(proof) = &mut result.proof {
                    for step in &mut proof.proof_steps {
                        visitor(step)?;
                    }
                }
            }
            Self::TryStmt(result) => {
                if let Some(proof) = &mut result.proof {
                    for step in &mut proof.proof_steps {
                        visitor(step)?;
                    }
                }
            }
        }
        Ok(())
    }
}

fn claim_child_results(verification: Option<SuccessVerifyClaimResult>) -> Vec<StmtResult> {
    match verification {
        Some(SuccessVerifyClaimResult::Forall(result)) => {
            let mut children = result.proof_steps;
            children.extend(result.conclusion_checks);
            children
        }
        Some(SuccessVerifyClaimResult::Fact(result)) => {
            let mut children = result.proof_steps;
            children.push(*result.conclusion_check);
            children
        }
        None => Vec::new(),
    }
}

impl SuccessVerifyClaimResult {
    fn visit_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        match self {
            Self::Forall(result) => {
                for step in &result.proof_steps {
                    visitor(step);
                }
                for check in &result.conclusion_checks {
                    visitor(check);
                }
            }
            Self::Fact(result) => {
                for step in &result.proof_steps {
                    visitor(step);
                }
                visitor(&result.conclusion_check);
            }
        }
    }

    fn try_visit_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::Forall(result) => {
                for step in &mut result.proof_steps {
                    visitor(step)?;
                }
                for check in &mut result.conclusion_checks {
                    visitor(check)?;
                }
            }
            Self::Fact(result) => {
                for step in &mut result.proof_steps {
                    visitor(step)?;
                }
                visitor(&mut result.conclusion_check)?;
            }
        }
        Ok(())
    }
}

impl SuccessDefObjStmtResult {
    fn visit_named_child_results(&self, visitor: &mut impl FnMut(&StmtResult)) {
        match self {
            Self::HaveObjByExistFactsStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.source_result);
                }
            }
            Self::ObtainObjFromExistFact(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.source_result);
                }
            }
            Self::ObtainObjFromAtomicFact(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.source_result);
                }
            }
            Self::ObtainObjFromThm(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.source_result);
                }
            }
            Self::HaveObjInNonemptySetStmt(result) => {
                if let Some(verification) = &result.verification {
                    for group in &verification.groups {
                        if let Some(check) = &group.nonempty_check {
                            visitor(check);
                        }
                    }
                }
            }
            Self::HaveObjEqualStmt(result) => {
                if let Some(verification) = &result.verification {
                    for check in &verification.type_checks {
                        visitor(check);
                    }
                }
            }
            Self::HaveByPreimageStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.source_membership_check);
                }
            }
            Self::HaveFnEqualStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.return_check);
                }
            }
            Self::HaveFnEqualCaseByCaseStmt(result) => {
                if let Some(verification) = &result.verification {
                    visitor(&verification.coverage_check);
                    for check in &verification.return_checks {
                        visitor(check);
                    }
                }
            }
            Self::HaveFnByForallExistUniqueStmt(result) => {
                if let Some(verification) = &result.verification {
                    if let Some(check) = &verification.source_forall_check {
                        visitor(check);
                    }
                    for step in &verification.proof_steps {
                        visitor(step);
                    }
                    for check in &verification.conclusion_checks {
                        visitor(check);
                    }
                }
            }
            Self::HaveTupleStmt(result) => {
                visit_tuple_or_cart_children(result.verification.as_ref(), visitor)
            }
            Self::HaveCartStmt(result) => {
                visit_tuple_or_cart_children(result.verification.as_ref(), visitor)
            }
            Self::HaveSeqStmt(result) => {
                visit_indexed_function_children(result.verification.as_ref(), visitor)
            }
            Self::HaveFiniteSeqStmt(result) => {
                visit_indexed_function_children(result.verification.as_ref(), visitor)
            }
            Self::HaveMatrixStmt(result) => {
                visit_indexed_function_children(result.verification.as_ref(), visitor)
            }
            _ => {}
        }
    }

    fn try_visit_named_child_results_mut<E>(
        &mut self,
        visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
    ) -> Result<(), E> {
        match self {
            Self::HaveObjByExistFactsStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.source_result)?;
                }
            }
            Self::ObtainObjFromExistFact(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.source_result)?;
                }
            }
            Self::ObtainObjFromAtomicFact(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.source_result)?;
                }
            }
            Self::ObtainObjFromThm(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.source_result)?;
                }
            }
            Self::HaveObjInNonemptySetStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for group in &mut verification.groups {
                        if let Some(check) = &mut group.nonempty_check {
                            visitor(check)?;
                        }
                    }
                }
            }
            Self::HaveObjEqualStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    for check in &mut verification.type_checks {
                        visitor(check)?;
                    }
                }
            }
            Self::HaveByPreimageStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.source_membership_check)?;
                }
            }
            Self::HaveFnEqualStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.return_check)?;
                }
            }
            Self::HaveFnEqualCaseByCaseStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    visitor(&mut verification.coverage_check)?;
                    for check in &mut verification.return_checks {
                        visitor(check)?;
                    }
                }
            }
            Self::HaveFnByForallExistUniqueStmt(result) => {
                if let Some(verification) = &mut result.verification {
                    if let Some(check) = &mut verification.source_forall_check {
                        visitor(check)?;
                    }
                    for step in &mut verification.proof_steps {
                        visitor(step)?;
                    }
                    for check in &mut verification.conclusion_checks {
                        visitor(check)?;
                    }
                }
            }
            Self::HaveTupleStmt(result) => {
                try_visit_tuple_or_cart_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::HaveCartStmt(result) => {
                try_visit_tuple_or_cart_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::HaveSeqStmt(result) => {
                try_visit_indexed_function_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::HaveFiniteSeqStmt(result) => {
                try_visit_indexed_function_children_mut(result.verification.as_mut(), visitor)?
            }
            Self::HaveMatrixStmt(result) => {
                try_visit_indexed_function_children_mut(result.verification.as_mut(), visitor)?
            }
            _ => {}
        }
        Ok(())
    }

    fn into_child_results(self) -> Vec<StmtResult> {
        match self {
            Self::HaveObjByExistFactsStmt(result) => result
                .verification
                .map(|verification| vec![*verification.source_result])
                .unwrap_or_default(),
            Self::ObtainObjFromExistFact(result) => result
                .verification
                .map(|verification| vec![*verification.source_result])
                .unwrap_or_default(),
            Self::ObtainObjFromAtomicFact(result) => result
                .verification
                .map(|verification| vec![*verification.source_result])
                .unwrap_or_default(),
            Self::ObtainObjFromThm(result) => result
                .verification
                .map(|verification| vec![*verification.source_result])
                .unwrap_or_default(),
            Self::HaveObjInNonemptySetStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.extend(
                        verification
                            .groups
                            .into_iter()
                            .filter_map(|group| group.nonempty_check.map(|check| *check)),
                    );
                }
                children
            }
            Self::HaveObjEqualStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.extend(verification.type_checks);
                }
                children
            }
            Self::HaveByPreimageStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.source_membership_check);
                }
                children
            }
            Self::HaveFnEqualStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.return_check);
                }
                children
            }
            Self::HaveFnEqualCaseByCaseStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    children.push(*verification.coverage_check);
                    children.extend(verification.return_checks);
                }
                children
            }
            Self::HaveFnByForallExistUniqueStmt(result) => {
                let mut children = Vec::new();
                if let Some(verification) = result.verification {
                    if let Some(check) = verification.source_forall_check {
                        children.push(*check);
                    }
                    children.extend(verification.proof_steps);
                    children.extend(verification.conclusion_checks);
                }
                children
            }
            Self::HaveTupleStmt(result) => {
                into_tuple_or_cart_children(result.common, result.verification)
            }
            Self::HaveCartStmt(result) => {
                into_tuple_or_cart_children(result.common, result.verification)
            }
            Self::HaveSeqStmt(result) => {
                into_indexed_function_children(result.common, result.verification)
            }
            Self::HaveFiniteSeqStmt(result) => {
                into_indexed_function_children(result.common, result.verification)
            }
            Self::HaveMatrixStmt(result) => {
                into_indexed_function_children(result.common, result.verification)
            }
            _other => Vec::new(),
        }
    }
}

fn visit_tuple_or_cart_children(
    verification: Option<&SuccessVerifyTupleOrCartDefinitionResult>,
    visitor: &mut impl FnMut(&StmtResult),
) {
    if let Some(verification) = verification {
        visitor(&verification.dimension.positive_check);
        visitor(&verification.dimension.at_least_two_check);
    }
}

fn try_visit_tuple_or_cart_children_mut<E>(
    verification: Option<&mut SuccessVerifyTupleOrCartDefinitionResult>,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    if let Some(verification) = verification {
        visitor(&mut verification.dimension.positive_check)?;
        visitor(&mut verification.dimension.at_least_two_check)?;
    }
    Ok(())
}

fn into_tuple_or_cart_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyTupleOrCartDefinitionResult>,
) -> Vec<StmtResult> {
    let mut children = Vec::new();
    if let Some(verification) = verification {
        children.push(*verification.dimension.positive_check);
        children.push(*verification.dimension.at_least_two_check);
    }
    children
}

fn visit_indexed_function_children(
    verification: Option<&SuccessVerifyIndexedFunctionDefinitionResult>,
    visitor: &mut impl FnMut(&StmtResult),
) {
    if let Some(verification) = verification {
        for check in &verification.bound_checks {
            visitor(check);
        }
        visitor(&verification.return_check);
    }
}

fn try_visit_indexed_function_children_mut<E>(
    verification: Option<&mut SuccessVerifyIndexedFunctionDefinitionResult>,
    visitor: &mut impl FnMut(&mut StmtResult) -> Result<(), E>,
) -> Result<(), E> {
    if let Some(verification) = verification {
        for check in &mut verification.bound_checks {
            visitor(check)?;
        }
        visitor(&mut verification.return_check)?;
    }
    Ok(())
}

fn into_indexed_function_children(
    _common: SuccessStmtCommonResult,
    verification: Option<SuccessVerifyIndexedFunctionDefinitionResult>,
) -> Vec<StmtResult> {
    let mut children = Vec::new();
    if let Some(verification) = verification {
        children.extend(verification.bound_checks);
        children.push(*verification.return_check);
    }
    children
}

impl SuccessUnsafeStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::TrustStmt(result) => result.common,
            Self::TrustHaveStmt(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::TrustStmt(result) => result.statement.clone().into(),
            Self::TrustHaveStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::TrustStmt(result) => &result.common,
            Self::TrustHaveStmt(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::TrustStmt(result) => &mut result.common,
            Self::TrustHaveStmt(result) => &mut result.common,
        }
    }
}

impl SuccessDefObjStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::LetObjStmt(result) => result.common,
            Self::HaveObjInNonemptySetStmt(result) => result.common,
            Self::HaveObjEqualStmt(result) => result.common,
            Self::HaveObjByExistFactsStmt(result) => result.common,
            Self::ObtainObjFromExistFact(result) => result.common,
            Self::ObtainObjFromAtomicFact(result) => result.common,
            Self::ObtainObjFromThm(result) => result.common,
            Self::HaveByPreimageStmt(result) => result.common,
            Self::HaveFnEqualStmt(result) => result.common,
            Self::HaveFnEqualCaseByCaseStmt(result) => result.common,
            Self::HaveFnByInducStmt(result) => result.common,
            Self::HaveFnByForallExistUniqueStmt(result) => result.common,
            Self::HaveTupleStmt(result) => result.common,
            Self::HaveCartStmt(result) => result.common,
            Self::HaveSeqStmt(result) => result.common,
            Self::HaveFiniteSeqStmt(result) => result.common,
            Self::HaveMatrixStmt(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::LetObjStmt(result) => result.statement.clone().into(),
            Self::HaveObjInNonemptySetStmt(result) => result.statement.clone().into(),
            Self::HaveObjEqualStmt(result) => result.statement.clone().into(),
            Self::HaveObjByExistFactsStmt(result) => result.statement.clone().into(),
            Self::ObtainObjFromExistFact(result) => result.statement.clone().into(),
            Self::ObtainObjFromAtomicFact(result) => result.statement.clone().into(),
            Self::ObtainObjFromThm(result) => result.statement.clone().into(),
            Self::HaveByPreimageStmt(result) => result.statement.clone().into(),
            Self::HaveFnEqualStmt(result) => result.statement.clone().into(),
            Self::HaveFnEqualCaseByCaseStmt(result) => result.statement.clone().into(),
            Self::HaveFnByInducStmt(result) => result.statement.clone().into(),
            Self::HaveFnByForallExistUniqueStmt(result) => result.statement.clone().into(),
            Self::HaveTupleStmt(result) => result.statement.clone().into(),
            Self::HaveCartStmt(result) => result.statement.clone().into(),
            Self::HaveSeqStmt(result) => result.statement.clone().into(),
            Self::HaveFiniteSeqStmt(result) => result.statement.clone().into(),
            Self::HaveMatrixStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::LetObjStmt(result) => &result.common,
            Self::HaveObjInNonemptySetStmt(result) => &result.common,
            Self::HaveObjEqualStmt(result) => &result.common,
            Self::HaveObjByExistFactsStmt(result) => &result.common,
            Self::ObtainObjFromExistFact(result) => &result.common,
            Self::ObtainObjFromAtomicFact(result) => &result.common,
            Self::ObtainObjFromThm(result) => &result.common,
            Self::HaveByPreimageStmt(result) => &result.common,
            Self::HaveFnEqualStmt(result) => &result.common,
            Self::HaveFnEqualCaseByCaseStmt(result) => &result.common,
            Self::HaveFnByInducStmt(result) => &result.common,
            Self::HaveFnByForallExistUniqueStmt(result) => &result.common,
            Self::HaveTupleStmt(result) => &result.common,
            Self::HaveCartStmt(result) => &result.common,
            Self::HaveSeqStmt(result) => &result.common,
            Self::HaveFiniteSeqStmt(result) => &result.common,
            Self::HaveMatrixStmt(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::LetObjStmt(result) => &mut result.common,
            Self::HaveObjInNonemptySetStmt(result) => &mut result.common,
            Self::HaveObjEqualStmt(result) => &mut result.common,
            Self::HaveObjByExistFactsStmt(result) => &mut result.common,
            Self::ObtainObjFromExistFact(result) => &mut result.common,
            Self::ObtainObjFromAtomicFact(result) => &mut result.common,
            Self::ObtainObjFromThm(result) => &mut result.common,
            Self::HaveByPreimageStmt(result) => &mut result.common,
            Self::HaveFnEqualStmt(result) => &mut result.common,
            Self::HaveFnEqualCaseByCaseStmt(result) => &mut result.common,
            Self::HaveFnByInducStmt(result) => &mut result.common,
            Self::HaveFnByForallExistUniqueStmt(result) => &mut result.common,
            Self::HaveTupleStmt(result) => &mut result.common,
            Self::HaveCartStmt(result) => &mut result.common,
            Self::HaveSeqStmt(result) => &mut result.common,
            Self::HaveFiniteSeqStmt(result) => &mut result.common,
            Self::HaveMatrixStmt(result) => &mut result.common,
        }
    }
}

impl SuccessDefPredicateStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::DefPropStmt(result) => result.common,
            Self::DefAbstractPropStmt(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::DefPropStmt(result) => result.statement.clone().into(),
            Self::DefAbstractPropStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::DefPropStmt(result) => &result.common,
            Self::DefAbstractPropStmt(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::DefPropStmt(result) => &mut result.common,
            Self::DefAbstractPropStmt(result) => &mut result.common,
        }
    }
}

impl SuccessDefInterfaceStmtResult {
    fn into_common(self) -> Option<SuccessStmtCommonResult> {
        match self {
            Self::DefSettingStmt(result) => Some(result.common),
            Self::DefTemplateStmt(_) => None,
            Self::DefStructStmt(result) => Some(result.common),
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::DefSettingStmt(result) => result.statement.clone().into(),
            Self::DefTemplateStmt(result) => result.statement.clone().into(),
            Self::DefStructStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> Option<&SuccessStmtCommonResult> {
        match self {
            Self::DefSettingStmt(result) => Some(&result.common),
            Self::DefTemplateStmt(_) => None,
            Self::DefStructStmt(result) => Some(&result.common),
        }
    }

    fn common_mut(&mut self) -> Option<&mut SuccessStmtCommonResult> {
        match self {
            Self::DefSettingStmt(result) => Some(&mut result.common),
            Self::DefTemplateStmt(_) => None,
            Self::DefStructStmt(result) => Some(&mut result.common),
        }
    }
}

impl SuccessByStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::ByCasesStmt(result) => result.common,
            Self::ByContraStmt(result) => result.common,
            Self::ByEnumerateFiniteSetStmt(result) => result.common,
            Self::ByFiniteSetInducStmt(result) => result.common,
            Self::ByInducStmt(result) => result.common,
            Self::ByForStmt(result) => result.common,
            Self::ByExtensionStmt(result) => result.common,
            Self::ByEnumerateRangeStmt(result) => result.common,
            Self::ByClosedRangeAsCasesStmt(result) => result.common,
            Self::ByTransitivePropStmt(result) => result.common,
            Self::BySymmetricPropStmt(result) => result.common,
            Self::ByReflexivePropStmt(result) => result.common,
            Self::ByAntisymmetricPropStmt(result) => result.common,
            Self::ByZornLemmaStmt(result) => result.common,
            Self::ByAxiomOfChoiceStmt(result) => result.common,
            Self::ByRegularityAxiomStmt(result) => result.common,
            Self::ByDefStmt(result) => result.common,
            Self::ByStructDefStmt(result) => result.common,
            Self::ByThmStmt(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::ByCasesStmt(result) => result.statement.clone().into(),
            Self::ByContraStmt(result) => result.statement.clone().into(),
            Self::ByEnumerateFiniteSetStmt(result) => result.statement.clone().into(),
            Self::ByFiniteSetInducStmt(result) => result.statement.clone().into(),
            Self::ByInducStmt(result) => result.statement.clone().into(),
            Self::ByForStmt(result) => result.statement.clone().into(),
            Self::ByExtensionStmt(result) => result.statement.clone().into(),
            Self::ByEnumerateRangeStmt(result) => result.statement.clone().into(),
            Self::ByClosedRangeAsCasesStmt(result) => result.statement.clone().into(),
            Self::ByTransitivePropStmt(result) => result.statement.clone().into(),
            Self::BySymmetricPropStmt(result) => result.statement.clone().into(),
            Self::ByReflexivePropStmt(result) => result.statement.clone().into(),
            Self::ByAntisymmetricPropStmt(result) => result.statement.clone().into(),
            Self::ByZornLemmaStmt(result) => result.statement.clone().into(),
            Self::ByAxiomOfChoiceStmt(result) => result.statement.clone().into(),
            Self::ByRegularityAxiomStmt(result) => result.statement.clone().into(),
            Self::ByDefStmt(result) => result.statement.clone().into(),
            Self::ByStructDefStmt(result) => result.statement.clone().into(),
            Self::ByThmStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::ByCasesStmt(result) => &result.common,
            Self::ByContraStmt(result) => &result.common,
            Self::ByEnumerateFiniteSetStmt(result) => &result.common,
            Self::ByFiniteSetInducStmt(result) => &result.common,
            Self::ByInducStmt(result) => &result.common,
            Self::ByForStmt(result) => &result.common,
            Self::ByExtensionStmt(result) => &result.common,
            Self::ByEnumerateRangeStmt(result) => &result.common,
            Self::ByClosedRangeAsCasesStmt(result) => &result.common,
            Self::ByTransitivePropStmt(result) => &result.common,
            Self::BySymmetricPropStmt(result) => &result.common,
            Self::ByReflexivePropStmt(result) => &result.common,
            Self::ByAntisymmetricPropStmt(result) => &result.common,
            Self::ByZornLemmaStmt(result) => &result.common,
            Self::ByAxiomOfChoiceStmt(result) => &result.common,
            Self::ByRegularityAxiomStmt(result) => &result.common,
            Self::ByDefStmt(result) => &result.common,
            Self::ByStructDefStmt(result) => &result.common,
            Self::ByThmStmt(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::ByCasesStmt(result) => &mut result.common,
            Self::ByContraStmt(result) => &mut result.common,
            Self::ByEnumerateFiniteSetStmt(result) => &mut result.common,
            Self::ByFiniteSetInducStmt(result) => &mut result.common,
            Self::ByInducStmt(result) => &mut result.common,
            Self::ByForStmt(result) => &mut result.common,
            Self::ByExtensionStmt(result) => &mut result.common,
            Self::ByEnumerateRangeStmt(result) => &mut result.common,
            Self::ByClosedRangeAsCasesStmt(result) => &mut result.common,
            Self::ByTransitivePropStmt(result) => &mut result.common,
            Self::BySymmetricPropStmt(result) => &mut result.common,
            Self::ByReflexivePropStmt(result) => &mut result.common,
            Self::ByAntisymmetricPropStmt(result) => &mut result.common,
            Self::ByZornLemmaStmt(result) => &mut result.common,
            Self::ByAxiomOfChoiceStmt(result) => &mut result.common,
            Self::ByRegularityAxiomStmt(result) => &mut result.common,
            Self::ByDefStmt(result) => &mut result.common,
            Self::ByStructDefStmt(result) => &mut result.common,
            Self::ByThmStmt(result) => &mut result.common,
        }
    }
}

impl SuccessWitnessStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::WitnessExistFact(result) => result.common,
            Self::WitnessAtomicFact(result) => result.common,
            Self::WitnessNonemptySet(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::WitnessExistFact(result) => result.statement.clone().into(),
            Self::WitnessAtomicFact(result) => result.statement.clone().into(),
            Self::WitnessNonemptySet(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::WitnessExistFact(result) => &result.common,
            Self::WitnessAtomicFact(result) => &result.common,
            Self::WitnessNonemptySet(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::WitnessExistFact(result) => &mut result.common,
            Self::WitnessAtomicFact(result) => &mut result.common,
            Self::WitnessNonemptySet(result) => &mut result.common,
        }
    }
}

impl SuccessProofBlockStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::ClaimStmt(result) => result.common,
            Self::ExampleStmt(result) => result.common,
            Self::SketchStmt(result) => result.common,
            Self::TryStmt(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::ClaimStmt(result) => result.statement.clone().into(),
            Self::ExampleStmt(result) => result.statement.clone().into(),
            Self::SketchStmt(result) => result.statement.clone().into(),
            Self::TryStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::ClaimStmt(result) => &result.common,
            Self::ExampleStmt(result) => &result.common,
            Self::SketchStmt(result) => &result.common,
            Self::TryStmt(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::ClaimStmt(result) => &mut result.common,
            Self::ExampleStmt(result) => &mut result.common,
            Self::SketchStmt(result) => &mut result.common,
            Self::TryStmt(result) => &mut result.common,
        }
    }
}

impl SuccessCommandStmtResult {
    fn into_common(self) -> SuccessStmtCommonResult {
        match self {
            Self::ImportStmt(result) => result.common,
            Self::DoNothingStmt(result) => result.common,
            Self::ClearStmt(result) => result.common,
            Self::EvalStmt(result) => result.common,
            Self::UseStrategyStmt(result) => result.common,
            Self::StopStrategyStmt(result) => result.common,
        }
    }

    fn statement(&self) -> Stmt {
        match self {
            Self::ImportStmt(result) => result.statement.clone().into(),
            Self::DoNothingStmt(result) => result.statement.clone().into(),
            Self::ClearStmt(result) => result.statement.clone().into(),
            Self::EvalStmt(result) => result.statement.clone().into(),
            Self::UseStrategyStmt(result) => result.statement.clone().into(),
            Self::StopStrategyStmt(result) => result.statement.clone().into(),
        }
    }

    fn common(&self) -> &SuccessStmtCommonResult {
        match self {
            Self::ImportStmt(result) => &result.common,
            Self::DoNothingStmt(result) => &result.common,
            Self::ClearStmt(result) => &result.common,
            Self::EvalStmt(result) => &result.common,
            Self::UseStrategyStmt(result) => &result.common,
            Self::StopStrategyStmt(result) => &result.common,
        }
    }

    fn common_mut(&mut self) -> &mut SuccessStmtCommonResult {
        match self {
            Self::ImportStmt(result) => &mut result.common,
            Self::DoNothingStmt(result) => &mut result.common,
            Self::ClearStmt(result) => &mut result.common,
            Self::EvalStmt(result) => &mut result.common,
            Self::UseStrategyStmt(result) => &mut result.common,
            Self::StopStrategyStmt(result) => &mut result.common,
        }
    }
}
