use super::*;
use crate::common::defaults::LineFile;

/// Compiler IR mirrors the source `Stmt` tree exactly. Unsupported source
/// payloads keep their source names and remain unconstructible.
macro_rules! unsupported_statement_irs {
    ($($name:ident),+ $(,)?) => {
        $(
            #[derive(Clone, Debug)]
            pub enum $name {}
        )+
    };
}

unsupported_statement_irs!(
    LitexToLeanDefAlgoStmtIr,
    LitexToLeanDefStrategyStmtIr,
    LitexToLeanTrustHaveStmtIr,
    LitexToLeanObtainObjFromThmIr,
    LitexToLeanHaveByPreimageStmtIr,
    LitexToLeanHaveFnEqualCaseByCaseStmtIr,
    LitexToLeanHaveFnByInducStmtIr,
    LitexToLeanHaveFnByForallExistUniqueStmtIr,
    LitexToLeanHaveCartStmtIr,
    LitexToLeanHaveSeqStmtIr,
    LitexToLeanHaveFiniteSeqStmtIr,
    LitexToLeanHaveMatrixStmtIr,
    LitexToLeanDefSettingStmtIr,
    LitexToLeanDefTemplateStmtIr,
    LitexToLeanDefStructStmtIr,
    LitexToLeanByEnumerateFiniteSetStmtIr,
    LitexToLeanByFiniteSetInducStmtIr,
    LitexToLeanByInducStmtIr,
    LitexToLeanByForStmtIr,
    LitexToLeanByExtensionStmtIr,
    LitexToLeanByEnumerateRangeStmtIr,
    LitexToLeanByClosedRangeAsCasesStmtIr,
    LitexToLeanByTransitivePropStmtIr,
    LitexToLeanBySymmetricPropStmtIr,
    LitexToLeanByReflexivePropStmtIr,
    LitexToLeanByAntisymmetricPropStmtIr,
    LitexToLeanByZornLemmaStmtIr,
    LitexToLeanByAxiomOfChoiceStmtIr,
    LitexToLeanByRegularityAxiomStmtIr,
    LitexToLeanByThmStmtIr,
    LitexToLeanWitnessNonemptySetIr,
    LitexToLeanTryStmtIr,
    LitexToLeanImportStmtIr,
    LitexToLeanClearStmtIr,
    LitexToLeanEvalStmtIr,
    LitexToLeanUseStrategyStmtIr,
    LitexToLeanStopStrategyStmtIr,
);

#[derive(Clone, Debug)]
pub enum LitexToLeanStatementIr {
    Fact(LitexToLeanFactStatementIr),
    UnsafeStmt(LitexToLeanUnsafeStmtIr),
    DefObjStmt(LitexToLeanDefObjStmtIr),
    DefPredicateStmt(LitexToLeanDefPredicateStmtIr),
    DefInterfaceStmt(LitexToLeanDefInterfaceStmtIr),
    DefAlgoStmt(LitexToLeanDefAlgoStmtIr),
    DefThmStmt(LitexToLeanDefThmStmtIr),
    DefStrategyStmt(LitexToLeanDefStrategyStmtIr),
    By(LitexToLeanByStmtIr),
    Witness(LitexToLeanWitnessStmtIr),
    ProofBlock(LitexToLeanProofBlockStmtIr),
    Command(LitexToLeanCommandStmtIr),
}

#[derive(Clone, Debug)]
pub enum LitexToLeanUnsafeStmtIr {
    TrustStmt(LitexToLeanTrustStmtIr),
    TrustHaveStmt(LitexToLeanTrustHaveStmtIr),
}

#[derive(Clone, Debug)]
pub enum LitexToLeanDefObjStmtIr {
    LetObjStmt(LitexToLeanLetObjStmtIr),
    HaveObjInNonemptySetStmt(LitexToLeanHaveObjInNonemptySetOrParamTypeStmtIr),
    HaveObjEqualStmt(LitexToLeanHaveObjEqualStmtIr),
    HaveObjByExistFactsStmt(LitexToLeanHaveObjByExistFactsStmtIr),
    ObtainObjFromExistFact(LitexToLeanObtainObjFromExistFactIr),
    ObtainObjFromAtomicFact(LitexToLeanObtainObjFromAtomicFactIr),
    ObtainObjFromThm(LitexToLeanObtainObjFromThmIr),
    HaveByPreimageStmt(LitexToLeanHaveByPreimageStmtIr),
    HaveFnEqualStmt(LitexToLeanHaveFnEqualStmtIr),
    HaveFnEqualCaseByCaseStmt(LitexToLeanHaveFnEqualCaseByCaseStmtIr),
    HaveFnByInducStmt(LitexToLeanHaveFnByInducStmtIr),
    HaveFnByForallExistUniqueStmt(LitexToLeanHaveFnByForallExistUniqueStmtIr),
    HaveTupleStmt(LitexToLeanHaveTupleStmtIr),
    HaveCartStmt(LitexToLeanHaveCartStmtIr),
    HaveSeqStmt(LitexToLeanHaveSeqStmtIr),
    HaveFiniteSeqStmt(LitexToLeanHaveFiniteSeqStmtIr),
    HaveMatrixStmt(LitexToLeanHaveMatrixStmtIr),
}

#[derive(Clone, Debug)]
pub enum LitexToLeanDefPredicateStmtIr {
    DefPropStmt(LitexToLeanDefPropStmtIr),
    DefAbstractPropStmt(LitexToLeanDefAbstractPropStmtIr),
}

#[derive(Clone, Debug)]
pub enum LitexToLeanDefInterfaceStmtIr {
    DefSettingStmt(LitexToLeanDefSettingStmtIr),
    DefTemplateStmt(LitexToLeanDefTemplateStmtIr),
    DefStructStmt(LitexToLeanDefStructStmtIr),
}

#[derive(Clone, Debug)]
pub enum LitexToLeanByStmtIr {
    ByCasesStmt(LitexToLeanByCasesStmtIr),
    ByContraStmt(LitexToLeanByContraStmtIr),
    ByEnumerateFiniteSetStmt(LitexToLeanByEnumerateFiniteSetStmtIr),
    ByFiniteSetInducStmt(LitexToLeanByFiniteSetInducStmtIr),
    ByInducStmt(LitexToLeanByInducStmtIr),
    ByForStmt(LitexToLeanByForStmtIr),
    ByExtensionStmt(LitexToLeanByExtensionStmtIr),
    ByEnumerateRangeStmt(LitexToLeanByEnumerateRangeStmtIr),
    ByClosedRangeAsCasesStmt(LitexToLeanByClosedRangeAsCasesStmtIr),
    ByTransitivePropStmt(LitexToLeanByTransitivePropStmtIr),
    BySymmetricPropStmt(LitexToLeanBySymmetricPropStmtIr),
    ByReflexivePropStmt(LitexToLeanByReflexivePropStmtIr),
    ByAntisymmetricPropStmt(LitexToLeanByAntisymmetricPropStmtIr),
    ByZornLemmaStmt(LitexToLeanByZornLemmaStmtIr),
    ByAxiomOfChoiceStmt(LitexToLeanByAxiomOfChoiceStmtIr),
    ByRegularityAxiomStmt(LitexToLeanByRegularityAxiomStmtIr),
    ByDefStmt(LitexToLeanByDefStmtIr),
    ByThmStmt(LitexToLeanByThmStmtIr),
}

#[derive(Clone, Debug)]
pub enum LitexToLeanWitnessStmtIr {
    WitnessExistFact(LitexToLeanWitnessExistFactIr),
    WitnessAtomicFact(LitexToLeanWitnessAtomicFactIr),
    WitnessNonemptySet(LitexToLeanWitnessNonemptySetIr),
}

#[derive(Clone, Debug)]
pub enum LitexToLeanProofBlockStmtIr {
    ClaimStmt(LitexToLeanClaimStmtIr),
    ExampleStmt(LitexToLeanExampleStmtIr),
    SketchStmt(LitexToLeanSketchStmtIr),
    TryStmt(LitexToLeanTryStmtIr),
}

#[derive(Clone, Debug)]
pub enum LitexToLeanCommandStmtIr {
    ImportStmt(LitexToLeanImportStmtIr),
    DoNothingStmt(LitexToLeanDoNothingStmtIr),
    ClearStmt(LitexToLeanClearStmtIr),
    EvalStmt(LitexToLeanEvalStmtIr),
    UseStrategyStmt(LitexToLeanUseStrategyStmtIr),
    StopStrategyStmt(LitexToLeanStopStrategyStmtIr),
}

#[derive(Clone, Debug)]
pub struct LitexToLeanDefAbstractPropStmtIr {
    pub name: String,
    pub params: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanDefPropStmtIr {
    pub name: String,
    pub params: Vec<LitexToLeanParameterGroupIr>,
    pub iff_facts: Vec<Fact>,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanHaveObjEqualStmtIr {
    pub definitions: Vec<LitexToLeanObjectDefinitionIr>,
    pub facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanLetObjStmtIr {
    pub line_file: LineFile,
    pub symbol_id: SymbolId,
    pub name: String,
    pub value: LitexToLeanObjectIr,
    pub defining_equality: LitexToLeanFactIr,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

impl LitexToLeanLetObjStmtIr {
    pub fn new(
        line_file: LineFile,
        symbol_id: SymbolId,
        name: String,
        value: LitexToLeanObjectIr,
        defining_equality: LitexToLeanFactIr,
        inferred_facts: Vec<LitexToLeanFactIr>,
        well_definedness: LitexToLeanWellDefinednessCertificateIr,
    ) -> Self {
        Self {
            line_file,
            symbol_id,
            name,
            value,
            defining_equality,
            inferred_facts,
            well_definedness,
        }
    }
}

#[derive(Clone, Debug)]
pub struct LitexToLeanHaveObjInNonemptySetOrParamTypeStmtIr {
    pub choices: Vec<LitexToLeanObjectChoiceIr>,
}

/// Checked IR for the source `have fn f(...) ... = body` statement.
#[derive(Clone)]
pub struct LitexToLeanHaveFnEqualStmtIr {
    pub symbol_id: SymbolId,
    pub name: String,
    pub function: LitexToLeanFunctionTypeIr,
    pub body: LitexToLeanObjectIr,
    pub parameter_premises: Vec<LitexToLeanLocalPremiseIr>,
    pub domain_premises: Vec<LitexToLeanLocalPremiseIr>,
    pub inferred_premises: Vec<LitexToLeanFactIr>,
    pub return_check: LitexToLeanFactIr,
    pub membership: LitexToLeanStoredFunctionFactIr,
    pub defining_equality: LitexToLeanStoredFunctionFactIr,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

impl fmt::Debug for LitexToLeanHaveFnEqualStmtIr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("LitexToLeanHaveFnEqualStmtIr")
            .field("symbol_id", &self.symbol_id)
            .field("name", &self.name)
            .field("function", &self.function)
            .field("body", &self.body)
            .field("parameter_premises", &self.parameter_premises)
            .field("domain_premises", &self.domain_premises)
            .field("inferred_premises", &self.inferred_premises)
            .field("return_check", &self.return_check)
            .field("membership", &self.membership)
            .field("defining_equality", &self.defining_equality)
            .field("well_definedness", &self.well_definedness)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct LitexToLeanHaveTupleStmtIr {
    pub symbol_id: SymbolId,
    pub name: String,
    pub index_symbol_id: SymbolId,
    pub index_name: String,
    pub dimension: LitexToLeanObjectIr,
    pub value: LitexToLeanObjectIr,
    pub dimension_checks: Vec<LitexToLeanFactIr>,
    pub stored_facts: Vec<LitexToLeanStoredTupleFactIr>,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanObtainObjFromExistFactIr {
    pub source: LitexToLeanFactIr,
    pub witnesses: Vec<LitexToLeanExistentialWitnessIr>,
    pub projections: Vec<LitexToLeanFactIr>,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanObtainObjFromAtomicFactIr {
    pub source: LitexToLeanFactIr,
    pub witnesses: Vec<LitexToLeanExistentialWitnessIr>,
    pub projections: Vec<LitexToLeanFactIr>,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanHaveObjByExistFactsStmtIr {
    pub source: LitexToLeanFactIr,
    pub witnesses: Vec<LitexToLeanExistentialWitnessIr>,
    pub projections: Vec<LitexToLeanFactIr>,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanWitnessExistFactIr {
    pub facts: Vec<LitexToLeanFactIr>,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanWitnessAtomicFactIr {
    pub facts: Vec<LitexToLeanFactIr>,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanLocalFactAliasIr {
    pub local_fact_id: FactId,
    pub parent_fact_id: FactId,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanLocalProofBlockIr {
    pub premise_aliases: Vec<LitexToLeanLocalFactAliasIr>,
    pub assumption_inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
    pub steps: Vec<LitexToLeanStatementIr>,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanClaimStmtIr {
    pub line_file: LineFile,
    pub target: LitexToLeanFactIr,
    pub block: LitexToLeanLocalProofBlockIr,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

impl LitexToLeanClaimStmtIr {
    pub fn new(
        line_file: LineFile,
        target: LitexToLeanFactIr,
        block: LitexToLeanLocalProofBlockIr,
        inferred_facts: Vec<LitexToLeanFactIr>,
        well_definedness: LitexToLeanWellDefinednessCertificateIr,
    ) -> Self {
        Self {
            line_file,
            target,
            block,
            inferred_facts,
            well_definedness,
        }
    }
}

#[derive(Clone, Debug)]
pub struct LitexToLeanExampleStmtIr {
    pub line_file: LineFile,
    pub target: LitexToLeanFactIr,
    pub block: LitexToLeanLocalProofBlockIr,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

impl LitexToLeanExampleStmtIr {
    pub fn new(
        line_file: LineFile,
        target: LitexToLeanFactIr,
        block: LitexToLeanLocalProofBlockIr,
        well_definedness: LitexToLeanWellDefinednessCertificateIr,
    ) -> Self {
        Self {
            line_file,
            target,
            block,
            well_definedness,
        }
    }
}

#[derive(Clone, Debug)]
pub struct LitexToLeanSketchStmtIr {
    pub line_file: LineFile,
    pub block: LitexToLeanLocalProofBlockIr,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

impl LitexToLeanSketchStmtIr {
    pub fn new(
        line_file: LineFile,
        block: LitexToLeanLocalProofBlockIr,
        well_definedness: LitexToLeanWellDefinednessCertificateIr,
    ) -> Self {
        Self {
            line_file,
            block,
            well_definedness,
        }
    }
}

#[derive(Clone, Debug)]
pub struct LitexToLeanDoNothingStmtIr {
    pub line_file: LineFile,
}

impl LitexToLeanDoNothingStmtIr {
    pub fn new(line_file: LineFile) -> Self {
        Self { line_file }
    }
}

#[derive(Clone, Debug)]
pub struct LitexToLeanByCasesStmtIr {
    pub facts: Vec<LitexToLeanFactIr>,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanByContraStmtIr {
    pub facts: Vec<LitexToLeanFactIr>,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanByDefStmtIr {
    pub facts: Vec<LitexToLeanFactIr>,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}

#[derive(Clone, Debug)]
pub struct LitexToLeanTrustStmtIr {
    pub facts: Vec<LitexToLeanFactIr>,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
}

/// One verified source `Fact` statement.  A complete stored fact keeps its
/// `FactId` on `source`; a covered `forall` without one complete `FactId`
/// retains its independently stored projections in source order.
#[derive(Clone, Debug)]
pub struct LitexToLeanFactStatementIr {
    pub source: LitexToLeanFactIr,
    pub stored_projections: Vec<LitexToLeanFactIr>,
    pub inferred_facts: Vec<LitexToLeanFactIr>,
    pub well_definedness: LitexToLeanWellDefinednessCertificateIr,
}
