use crate::prelude::*;

#[derive(Clone)]
pub enum Stmt {
    Fact(Fact),
    UnsafeStmt(UnsafeStmt),
    DefObjStmt(DefObjStmt),
    DefPredicateStmt(DefPredicateStmt),
    DefAliasStmt(DefAliasStmt),
    DefInterfaceStmt(DefInterfaceStmt),
    DefAlgoStmt(DefAlgoStmt),
    DefThmStmt(DefThmStmt),
    DefStrategyStmt(DefStrategyStmt),
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
pub enum DefObjStmt {
    HaveObjInNonemptySetStmt(HaveObjInNonemptySetOrParamTypeStmt),
    HaveObjEqualStmt(HaveObjEqualStmt),
    HaveObjByExistFactsStmt(HaveObjByExistFactsStmt),
    HaveByExistStmt(HaveByExistStmt),
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
}

#[derive(Clone)]
pub enum DefPredicateStmt {
    DefPropStmt(DefPropStmt),
    DefAbstractPropStmt(DefAbstractPropStmt),
}

#[derive(Clone)]
pub enum DefAliasStmt {
    AliasPropStmt(AliasPropStmt),
    AliasThmStmt(AliasThmStmt),
}

#[derive(Clone)]
pub enum DefInterfaceStmt {
    DefTemplateStmt(DefTemplateStmt),
    DefStructStmt(DefStructStmt),
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
    ByAntisymmetricPropStmt(ByAntisymmetricPropStmt),
    ByZornLemmaStmt(ByZornLemmaStmt),
    ByAxiomOfChoiceStmt(ByAxiomOfChoiceStmt),
    ByRegularityAxiomStmt(ByRegularityAxiomStmt),
    ByThmStmt(ByThmStmt),
}

#[derive(Clone)]
pub enum WitnessStmt {
    WitnessExistFact(WitnessExistFact),
    WitnessNonemptySet(WitnessNonemptySet),
}

#[derive(Clone)]
pub enum ProofBlockStmt {
    ClaimStmt(ClaimStmt),
    SketchStmt(SketchStmt),
    TryStmt(TryStmt),
}

#[derive(Clone)]
pub enum CommandStmt {
    ImportStmt(ImportStmt),
    DoNothingStmt(DoNothingStmt),
    ClearStmt(ClearStmt),
    EvalStmt(EvalStmt),
    UseStrategyStmt(UseStrategyStmt),
    StopStrategyStmt(StopStrategyStmt),
}
