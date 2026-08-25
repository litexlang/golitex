//! Successful statement outcome variants and retained evidence fields.

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
    pub run_in_local_env: Option<SuccessVerifyDefAlgoLocalEnvResult>,
}

pub struct SuccessVerifyDefAlgoLocalEnvResult {
    pub definition_function_set: FnSetBody,
    pub parameter_retagging: Vec<SuccessVerifyDefAlgoParameterRetagResult>,
    pub requirement_facts: Vec<Fact>,
    pub parameter_definition: TypedParameterList,
    pub function_call: Obj,
    pub cases: Vec<SuccessVerifyDefAlgoCaseResult>,
    pub default_return: Option<SuccessVerifyDefAlgoDefaultResult>,
    pub coverage: Option<SuccessVerifyDefAlgoCoverageResult>,
}

pub struct SuccessVerifyDefAlgoParameterRetagResult {
    pub parameter_index: usize,
    pub source_binding: SymbolBinding,
    pub verification_object: Obj,
}

pub struct SuccessVerifyDefAlgoCaseResult {
    pub case_index: usize,
    pub verification_fact: Fact,
    pub verification: Box<StmtResult>,
}

pub struct SuccessVerifyDefAlgoDefaultResult {
    pub verification_fact: Fact,
    pub verification: Box<StmtResult>,
}

pub struct SuccessVerifyDefAlgoCoverageResult {
    pub verification_fact: Fact,
    pub verification: Box<StmtResult>,
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
    Definition(SuccessDefinitionStmtResult),
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
    pub verification: Option<SuccessVerifyHaveFnByInducResult>,
}

pub struct SuccessVerifyHaveFnByInducResult {
    pub well_definedness_run_in_local_env: SuccessVerifyHaveFnByInducWellDefinednessLocalEnvResult,
    pub verification_run_in_local_env: SuccessVerifyHaveFnByInducLocalEnvResult,
}

pub struct SuccessVerifyHaveFnByInducWellDefinednessLocalEnvResult {
    pub function_binding: SymbolBinding,
    pub function_set: FnSet,
    pub function_set_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub parameters_and_domain: SuccessVerifyHaveFnByInducParametersAndDomainResult,
    pub measure_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub lower_bound_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
}

pub struct SuccessVerifyHaveFnByInducParametersAndDomainResult {
    pub parameter_groups: Vec<SuccessVerifyHaveFnByInducParameterGroupResult>,
    pub domain_facts: Vec<SuccessVerifyHaveFnByInducDomainFactResult>,
}

pub struct SuccessVerifyHaveFnByInducParameterGroupResult {
    pub group_index: usize,
    pub definition: SetBoundParameterGroup,
    pub infers: SuccessInferResult,
}

pub struct SuccessVerifyHaveFnByInducDomainFactResult {
    pub domain_index: usize,
    pub store: SuccessStoreFactResult,
}

pub struct SuccessVerifyHaveFnByInducLocalEnvResult {
    pub parameters_and_domain: SuccessVerifyHaveFnByInducParametersAndDomainResult,
    pub measure: SuccessVerifyHaveFnByInducMeasureResult,
    pub recursive_function: SuccessVerifyHaveFnByInducRecursiveFunctionResult,
    pub cases: SuccessVerifyHaveFnByInducCaseListResult,
}

pub struct SuccessVerifyHaveFnByInducMeasureResult {
    pub measure_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub lower_bound_well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub measure_integer_check: Box<StmtResult>,
    pub lower_bound_integer_check: Box<StmtResult>,
    pub lower_bound_check: Box<StmtResult>,
}

pub struct SuccessVerifyHaveFnByInducRecursiveFunctionResult {
    pub function_set: FnSet,
    pub membership_store: SuccessStoreFactResult,
}

pub struct SuccessVerifyHaveFnByInducCaseListResult {
    pub coverage_fact: Fact,
    pub coverage_check: Box<StmtResult>,
    pub mutual_exclusions: Vec<SuccessVerifyCaseDisjointnessResult>,
    pub cases: Vec<SuccessVerifyHaveFnByInducCaseResult>,
}

pub struct SuccessVerifyHaveFnByInducCaseResult {
    pub case_index: usize,
    pub case_fact: Fact,
    pub assumption_store: SuccessStoreFactResult,
    pub body: SuccessVerifyHaveFnByInducCaseBodyResult,
}

pub enum SuccessVerifyHaveFnByInducCaseBodyResult {
    EqualTo(Box<SuccessVerifyHaveFnByInducEqualToResult>),
    NestedCases(Box<SuccessVerifyHaveFnByInducCaseListResult>),
}

pub struct SuccessVerifyHaveFnByInducEqualToResult {
    pub value: Obj,
    pub well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
    pub return_membership_fact: AtomicFact,
    pub return_membership_check: Box<StmtResult>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CaseDisjointnessOrientation {
    LeftImpliesNotRight,
    RightImpliesNotLeft,
}

/// The one successful orientation selected while checking that two case
/// conditions cannot hold together. Failed search attempts are not successful
/// proof evidence and are deliberately absent.
pub struct SuccessVerifyCaseDisjointnessResult {
    pub left_case_index: usize,
    pub right_case_index: usize,
    pub orientation: CaseDisjointnessOrientation,
    pub assumed_case: Fact,
    pub assumption_store: SuccessStoreFactResult,
    pub contradicted_atom: AtomicFact,
    pub negated_atom: AtomicFact,
    pub negated_atom_check: Box<StmtResult>,
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

pub enum SuccessDefinitionStmtResult {
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
    DefPropStmt(Box<SuccessDefPropStmtResult>),
    DefAbstractPropStmt(Box<SuccessDefAbstractPropStmtResult>),
    DefSettingStmt(Box<SuccessDefSettingStmtResult>),
    DefTemplateStmt(Box<SuccessDefTemplateStmtResult>),
    DefStructStmt(Box<SuccessDefStructStmtResult>),
    DefAlgoStmt(Box<SuccessDefAlgoStmtResult>),
    DefThmStmt(Box<SuccessDefThmStmtResult>),
    AxiomStmt(Box<SuccessAxiomStmtResult>),
    DefStrategyStmt(Box<SuccessDefStrategyStmtResult>),
}

pub struct SuccessDefPropStmtResult {
    pub statement: DefPropStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessDefAbstractPropStmtResult {
    pub statement: DefAbstractPropStmt,
    pub common: SuccessStmtCommonResult,
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
    /// The definition is checked in a temporary environment containing only
    /// its structure parameters and fields. Trusted materialization retains
    /// the definition but deliberately carries no invented verification.
    pub run_in_local_env: Option<SuccessVerifyDefStructLocalEnvResult>,
}

/// Typed output of `def_struct_stmt_check_well_defined_result` before its local
/// environment is popped. This is not a `StmtResult`: the local operation is
/// the verification process for the enclosing `def struct`, not another
/// source statement.
pub struct SuccessVerifyDefStructLocalEnvResult {
    /// Output of defining the structure parameters from the definition. These are
    /// structure parameters, not template parameters.
    pub structure_parameter_definition: Option<SuccessInferResult>,
    pub structure_domains: Vec<SuccessVerifyDefStructDomainResult>,
    pub field_types: Vec<SuccessVerifyDefStructFieldTypeResult>,
    pub field_scope_run_in_local_env: SuccessVerifyDefStructFieldScopeResult,
}

pub struct SuccessVerifyDefStructDomainResult {
    pub domain_index: usize,
    pub proposition: Fact,
    pub well_definedness: SuccessVerifyFactWellDefinedResult,
}

pub struct SuccessVerifyDefStructFieldTypeResult {
    pub field_index: usize,
    pub binding: SymbolBinding,
    pub field_type: Obj,
    pub well_definedness: Rc<SuccessVerifyObjWellDefinedResult>,
}

/// Typed output of the nested field environment. Field definitions and
/// equivalent facts are ordinary semantic operations owned by the enclosing
/// definition, so neither is wrapped in a synthetic statement Result.
pub struct SuccessVerifyDefStructFieldScopeResult {
    pub field_definitions: Vec<SuccessVerifyDefStructFieldDefinitionResult>,
    pub equivalent_facts: Vec<SuccessVerifyLocalFactWellDefinedResult>,
}

pub struct SuccessVerifyDefStructFieldDefinitionResult {
    pub field_index: usize,
    pub binding: SymbolBinding,
    pub field_type: Obj,
    pub infers: SuccessInferResult,
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
    pub execution: SuccessImportExecutionResult,
}

pub enum SuccessImportExecutionResult {
    Executed(Box<SuccessExecutedImportResult>),
    Reused(SuccessReusedImportResult),
}

pub struct SuccessExecutedImportResult {
    pub module_id: ModuleId,
    pub execution_mode: ExecutionMode,
    /// Ordered source statement Results produced while loading the module,
    /// including recursively executed configured imports.
    pub statement_results: Vec<StmtResult>,
}

pub struct SuccessReusedImportResult {
    pub module_id: ModuleId,
    pub execution_mode: ExecutionMode,
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
    ClearStmt(Box<SuccessClearStmtResult>),
    EvalStmt(Box<SuccessEvalStmtResult>),
    UseStrategyStmt(Box<SuccessUseStrategyStmtResult>),
    StopStrategyStmt(Box<SuccessStopStrategyStmtResult>),
}
