use crate::prelude::*;

#[derive(Clone)]
pub enum Stmt {
    Fact(Fact),
    UnsafeStmt(UnsafeStmt),
    DefObjStmt(DefObjStmt),
    DefInterfaceStmt(DefInterfaceStmt),
    By(ByStmt),
    Witness(WitnessStmt),
    ProofBlock(ProofBlockStmt),
    Command(CommandStmt),
}

#[derive(Clone)]
pub enum UnsafeStmt {
    KnowStmt(KnowStmt),
    DefLetStmt(DefLetStmt),
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
}

#[derive(Clone)]
pub enum DefInterfaceStmt {
    DefPropStmt(DefPropStmt),
    DefAbstractPropStmt(DefAbstractPropStmt),
    AliasPropStmt(AliasPropStmt),
    AliasThmStmt(AliasThmStmt),
    DefTemplateStmt(DefTemplateStmt),
    DefAlgoStmt(DefAlgoStmt),
    DefThmStmt(DefThmStmt),
    DefStrategyStmt(DefStrategyStmt),
    DefStructStmt(DefStructStmt),
}

#[derive(Clone)]
pub enum ByStmt {
    ByCasesStmt(ByCasesStmt),
    ByContraStmt(ByContraStmt),
    ByEnumerateFiniteSetStmt(ByEnumerateFiniteSetStmt),
    ByInducStmt(ByInducStmt),
    ByForStmt(ByForStmt),
    ByExtensionStmt(ByExtensionStmt),
    ByFnAsSetStmt(ByFnAsSetStmt),
    ByTupleAsSetStmt(ByTupleAsSetStmt),
    ByFnSetAsSetStmt(ByFnSetAsSetStmt),
    ByEnumerateRangeStmt(ByEnumerateRangeStmt),
    ByClosedRangeAsCasesStmt(ByClosedRangeAsCasesStmt),
    ByTransitivePropStmt(ByTransitivePropStmt),
    BySymmetricPropStmt(BySymmetricPropStmt),
    ByReflexivePropStmt(ByReflexivePropStmt),
    ByAntisymmetricPropStmt(ByAntisymmetricPropStmt),
    ByZornLemmaStmt(ByZornLemmaStmt),
    ByAxiomOfChoiceStmt(ByAxiomOfChoiceStmt),
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
}

#[derive(Clone)]
pub enum CommandStmt {
    ImportStmt(ImportStmt),
    DoNothingStmt(DoNothingStmt),
    ClearStmt(ClearStmt),
    StopImportStmt(StopImportStmt),
    RunFileStmt(RunFileStmt),
    EvalStmt(EvalStmt),
    EvalByStmt(EvalByStmt),
    UseStrategyStmt(UseStrategyStmt),
    StopStrategyStmt(StopStrategyStmt),
}
