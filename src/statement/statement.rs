//! Top-level statement enums and category types.

use crate::prelude::*;

#[derive(Clone)]
pub enum Stmt {
    Fact(Fact),
    UnsafeStmt(UnsafeStmt),
    Definition(DefinitionStmt),
    ReleaseThmStmt(ReleaseThmStmt),
    By(ByStmt),
    Witness(WitnessStmt),
    ProofBlock(ProofBlockStmt),
    Command(CommandStmt),
}

#[derive(Clone)]
pub enum UnsafeStmt {
    TrustStmt(TrustStmt),
    TrustHaveStmt(TrustHaveStmt),
}

#[derive(Clone)]
pub enum DefinitionStmt {
    LetObjStmt(LetObjStmt),
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveObjByExistFactsStmt(HaveObjByExistFactsStmt),
    ObtainObjFromExistFact(ObtainObjFromExistFact),
    ObtainObjFromAtomicFact(ObtainObjFromAtomicFact),
    ObtainObjFromThm(ObtainObjFromThm),
    HaveByPreimageStmt(HaveByPreimageStmt),
    HaveFnEqualStmt(HaveFnEqualStmt),
    HaveFnEqualCaseByCaseStmt(HaveFnEqualCaseByCaseStmt),
    HaveFnByInducStmt(HaveFnByInducStmt),
    HaveFnByForallExistUniqueStmt(HaveFnByForallExistUniqueStmt),
    HaveTupleStmt(HaveTupleStmt),
    HaveCartStmt(HaveCartStmt),
    HaveSeqStmt(HaveSeqStmt),
    HaveFiniteSeqStmt(HaveFiniteSeqStmt),
    HaveMatrixStmt(HaveMatrixStmt),
    DefPropStmt(DefPropStmt),
    DefAbstractPropStmt(DefAbstractPropStmt),
    DefSettingStmt(DefSettingStmt),
    DefTemplateStmt(DefTemplateStmt),
    DefStructStmt(DefStructStmt),
    DefAlgoStmt(DefAlgoStmt),
    DefThmStmt(DefThmStmt),
    AxiomStmt(AxiomStmt),
    DefStrategyStmt(DefStrategyStmt),
}

#[derive(Clone)]
pub enum ByStmt {
    ByCasesStmt(ByCasesStmt),
    ByContraStmt(ByContraStmt),
    ByEnumerateFiniteSetStmt(ByEnumerateFiniteSetStmt),
    ByFiniteSetInducStmt(ByFiniteSetInducStmt),
    ByInducStmt(ByInducStmt),
    ByForStmt(ByForStmt),
    ByExtensionStmt(ByExtensionStmt),
    ByEnumerateRangeStmt(ByEnumerateRangeStmt),
    ByClosedRangeAsCasesStmt(ByClosedRangeAsCasesStmt),
    ByTransitivePropStmt(ByTransitivePropStmt),
    BySymmetricPropStmt(BySymmetricPropStmt),
    ByReflexivePropStmt(ByReflexivePropStmt),
    ByZornLemmaStmt(ByZornLemmaStmt),
    ByAxiomOfChoiceStmt(ByAxiomOfChoiceStmt),
    ByRegularityAxiomStmt(ByRegularityAxiomStmt),
    ByDefStmt(ByDefStmt),
    ByStructDefStmt(ByStructDefStmt),
    ByThmStmt(ByThmStmt),
}

#[derive(Clone)]
pub enum WitnessStmt {
    WitnessExistFact(WitnessExistFact),
    WitnessAtomicFact(WitnessAtomicFact),
    WitnessNonemptySet(WitnessNonemptySet),
}

#[derive(Clone)]
pub enum ProofBlockStmt {
    ClaimStmt(ClaimStmt),
    ExampleStmt(ExampleStmt),
    SketchStmt(SketchStmt),
    TryStmt(TryStmt),
}

#[derive(Clone)]
pub enum CommandStmt {
    EvalStmt(EvalStmt),
}
