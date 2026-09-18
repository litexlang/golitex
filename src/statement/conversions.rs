//! Conversions among concrete and top-level statement forms.

use crate::prelude::*;

impl From<Fact> for Stmt {
    fn from(v: Fact) -> Self {
        Stmt::Fact(v)
    }
}

impl From<TrustHaveStmt> for Stmt {
    fn from(v: TrustHaveStmt) -> Self {
        UnsafeStmt::TrustHaveStmt(v).into()
    }
}

impl From<DefPropStmt> for Stmt {
    fn from(v: DefPropStmt) -> Self {
        DefinitionStmt::DefPropStmt(v).into()
    }
}

impl From<DefAbstractPropStmt> for Stmt {
    fn from(v: DefAbstractPropStmt) -> Self {
        DefinitionStmt::DefAbstractPropStmt(v).into()
    }
}

impl From<HaveObjInNonemptySetOrParamTypeStmt> for Stmt {
    fn from(v: HaveObjInNonemptySetOrParamTypeStmt) -> Self {
        DefinitionStmt::HaveObjInNonemptySetStmt(v).into()
    }
}

impl From<LetObjStmt> for Stmt {
    fn from(v: LetObjStmt) -> Self {
        DefinitionStmt::LetObjStmt(v).into()
    }
}

impl From<HaveObjEqualStmt> for Stmt {
    fn from(v: HaveObjEqualStmt) -> Self {
        DefinitionStmt::HaveObjEqualStmt(v).into()
    }
}

impl From<HaveObjByExistFactsStmt> for Stmt {
    fn from(v: HaveObjByExistFactsStmt) -> Self {
        DefinitionStmt::HaveObjByExistFactsStmt(v).into()
    }
}

impl From<ObtainObjFromExistFact> for Stmt {
    fn from(v: ObtainObjFromExistFact) -> Self {
        DefinitionStmt::ObtainObjFromExistFact(v).into()
    }
}

impl From<ObtainObjFromAtomicFact> for Stmt {
    fn from(v: ObtainObjFromAtomicFact) -> Self {
        DefinitionStmt::ObtainObjFromAtomicFact(v).into()
    }
}

impl From<ObtainObjFromThm> for Stmt {
    fn from(v: ObtainObjFromThm) -> Self {
        DefinitionStmt::ObtainObjFromThm(v).into()
    }
}

impl From<HaveByPreimageStmt> for Stmt {
    fn from(v: HaveByPreimageStmt) -> Self {
        DefinitionStmt::HaveByPreimageStmt(v).into()
    }
}

impl From<HaveFnEqualStmt> for Stmt {
    fn from(v: HaveFnEqualStmt) -> Self {
        DefinitionStmt::HaveFnEqualStmt(v).into()
    }
}

impl From<HaveFnEqualCaseByCaseStmt> for Stmt {
    fn from(v: HaveFnEqualCaseByCaseStmt) -> Self {
        DefinitionStmt::HaveFnEqualCaseByCaseStmt(v).into()
    }
}

impl From<HaveFnByInducStmt> for Stmt {
    fn from(v: HaveFnByInducStmt) -> Self {
        DefinitionStmt::HaveFnByInducStmt(v).into()
    }
}

impl From<HaveFnByForallExistUniqueStmt> for Stmt {
    fn from(v: HaveFnByForallExistUniqueStmt) -> Self {
        DefinitionStmt::HaveFnByForallExistUniqueStmt(v).into()
    }
}

impl From<HaveTupleStmt> for Stmt {
    fn from(v: HaveTupleStmt) -> Self {
        DefinitionStmt::HaveTupleStmt(v).into()
    }
}

impl From<HaveCartStmt> for Stmt {
    fn from(v: HaveCartStmt) -> Self {
        DefinitionStmt::HaveCartStmt(v).into()
    }
}

impl From<HaveSeqStmt> for Stmt {
    fn from(v: HaveSeqStmt) -> Self {
        DefinitionStmt::HaveSeqStmt(v).into()
    }
}

impl From<HaveFiniteSeqStmt> for Stmt {
    fn from(v: HaveFiniteSeqStmt) -> Self {
        DefinitionStmt::HaveFiniteSeqStmt(v).into()
    }
}

impl From<HaveMatrixStmt> for Stmt {
    fn from(v: HaveMatrixStmt) -> Self {
        DefinitionStmt::HaveMatrixStmt(v).into()
    }
}

impl From<DefTemplateStmt> for Stmt {
    fn from(v: DefTemplateStmt) -> Self {
        DefinitionStmt::DefTemplateStmt(v).into()
    }
}

impl From<DefSettingStmt> for Stmt {
    fn from(v: DefSettingStmt) -> Self {
        DefinitionStmt::DefSettingStmt(v).into()
    }
}

impl From<DefAlgoStmt> for Stmt {
    fn from(v: DefAlgoStmt) -> Self {
        DefinitionStmt::DefAlgoStmt(v).into()
    }
}

impl From<ClaimStmt> for Stmt {
    fn from(v: ClaimStmt) -> Self {
        ProofBlockStmt::ClaimStmt(v).into()
    }
}

impl From<ExampleStmt> for Stmt {
    fn from(v: ExampleStmt) -> Self {
        ProofBlockStmt::ExampleStmt(v).into()
    }
}

impl From<TrustStmt> for Stmt {
    fn from(v: TrustStmt) -> Self {
        UnsafeStmt::TrustStmt(v).into()
    }
}

impl From<SketchStmt> for Stmt {
    fn from(v: SketchStmt) -> Self {
        ProofBlockStmt::SketchStmt(v).into()
    }
}

impl From<TryStmt> for Stmt {
    fn from(v: TryStmt) -> Self {
        ProofBlockStmt::TryStmt(v).into()
    }
}

impl From<EvalStmt> for Stmt {
    fn from(v: EvalStmt) -> Self {
        CommandStmt::EvalStmt(v).into()
    }
}

impl From<WitnessExistFact> for Stmt {
    fn from(v: WitnessExistFact) -> Self {
        WitnessStmt::WitnessExistFact(v).into()
    }
}

impl From<WitnessAtomicFact> for Stmt {
    fn from(v: WitnessAtomicFact) -> Self {
        WitnessStmt::WitnessAtomicFact(v).into()
    }
}

impl From<WitnessNonemptySet> for Stmt {
    fn from(v: WitnessNonemptySet) -> Self {
        WitnessStmt::WitnessNonemptySet(v).into()
    }
}

impl From<ByCasesStmt> for Stmt {
    fn from(v: ByCasesStmt) -> Self {
        ByStmt::ByCasesStmt(v).into()
    }
}

impl From<ByContraStmt> for Stmt {
    fn from(v: ByContraStmt) -> Self {
        ByStmt::ByContraStmt(v).into()
    }
}

impl From<ByEnumerateFiniteSetStmt> for Stmt {
    fn from(v: ByEnumerateFiniteSetStmt) -> Self {
        ByStmt::ByEnumerateFiniteSetStmt(v).into()
    }
}

impl From<ByFiniteSetInducStmt> for Stmt {
    fn from(v: ByFiniteSetInducStmt) -> Self {
        ByStmt::ByFiniteSetInducStmt(v).into()
    }
}

impl From<ByInducStmt> for Stmt {
    fn from(v: ByInducStmt) -> Self {
        ByStmt::ByInducStmt(v).into()
    }
}

impl From<ByForStmt> for Stmt {
    fn from(v: ByForStmt) -> Self {
        ByStmt::ByForStmt(v).into()
    }
}

impl From<ByExtensionStmt> for Stmt {
    fn from(v: ByExtensionStmt) -> Self {
        ByStmt::ByExtensionStmt(v).into()
    }
}

impl From<ByEnumerateRangeStmt> for Stmt {
    fn from(v: ByEnumerateRangeStmt) -> Self {
        ByStmt::ByEnumerateRangeStmt(v).into()
    }
}

impl From<ByClosedRangeAsCasesStmt> for Stmt {
    fn from(v: ByClosedRangeAsCasesStmt) -> Self {
        ByStmt::ByClosedRangeAsCasesStmt(v).into()
    }
}

impl From<ByTransitivePropStmt> for Stmt {
    fn from(v: ByTransitivePropStmt) -> Self {
        ByStmt::ByTransitivePropStmt(v).into()
    }
}

impl From<BySymmetricPropStmt> for Stmt {
    fn from(v: BySymmetricPropStmt) -> Self {
        ByStmt::BySymmetricPropStmt(v).into()
    }
}

impl From<ByReflexivePropStmt> for Stmt {
    fn from(v: ByReflexivePropStmt) -> Self {
        ByStmt::ByReflexivePropStmt(v).into()
    }
}


impl From<ByZornLemmaStmt> for Stmt {
    fn from(v: ByZornLemmaStmt) -> Self {
        ByStmt::ByZornLemmaStmt(v).into()
    }
}

impl From<ByAxiomOfChoiceStmt> for Stmt {
    fn from(v: ByAxiomOfChoiceStmt) -> Self {
        ByStmt::ByAxiomOfChoiceStmt(v).into()
    }
}

impl From<ByRegularityAxiomStmt> for Stmt {
    fn from(v: ByRegularityAxiomStmt) -> Self {
        ByStmt::ByRegularityAxiomStmt(v).into()
    }
}

impl From<ByThmStmt> for Stmt {
    fn from(v: ByThmStmt) -> Self {
        ByStmt::ByThmStmt(v).into()
    }
}

impl From<ReleaseThmStmt> for Stmt {
    fn from(v: ReleaseThmStmt) -> Self {
        Stmt::ReleaseThmStmt(v)
    }
}

impl From<ByDefStmt> for Stmt {
    fn from(v: ByDefStmt) -> Self {
        ByStmt::ByDefStmt(v).into()
    }
}

impl From<ByStructDefStmt> for Stmt {
    fn from(v: ByStructDefStmt) -> Self {
        ByStmt::ByStructDefStmt(v).into()
    }
}

impl From<DefThmStmt> for Stmt {
    fn from(v: DefThmStmt) -> Self {
        DefinitionStmt::DefThmStmt(v).into()
    }
}

impl From<AxiomStmt> for Stmt {
    fn from(v: AxiomStmt) -> Self {
        DefinitionStmt::AxiomStmt(v).into()
    }
}

impl From<DefStrategyStmt> for Stmt {
    fn from(v: DefStrategyStmt) -> Self {
        DefinitionStmt::DefStrategyStmt(v).into()
    }
}

impl From<DefStructStmt> for Stmt {
    fn from(v: DefStructStmt) -> Self {
        DefinitionStmt::DefStructStmt(v).into()
    }
}

impl From<DefinitionStmt> for Stmt {
    fn from(v: DefinitionStmt) -> Self {
        Stmt::Definition(v)
    }
}

impl From<ByStmt> for Stmt {
    fn from(v: ByStmt) -> Self {
        Stmt::By(v)
    }
}

impl From<WitnessStmt> for Stmt {
    fn from(v: WitnessStmt) -> Self {
        Stmt::Witness(v)
    }
}

impl From<ProofBlockStmt> for Stmt {
    fn from(v: ProofBlockStmt) -> Self {
        Stmt::ProofBlock(v)
    }
}

impl From<CommandStmt> for Stmt {
    fn from(v: CommandStmt) -> Self {
        Stmt::Command(v)
    }
}

impl From<UnsafeStmt> for Stmt {
    fn from(v: UnsafeStmt) -> Self {
        Stmt::UnsafeStmt(v)
    }
}
