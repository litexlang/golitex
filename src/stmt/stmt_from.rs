use crate::prelude::*;

impl From<Fact> for Stmt {
    fn from(v: Fact) -> Self {
        Stmt::Fact(v)
    }
}

impl From<DefLetStmt> for Stmt {
    fn from(v: DefLetStmt) -> Self {
        UnsafeStmt::DefLetStmt(v).into()
    }
}

impl From<DefPropStmt> for Stmt {
    fn from(v: DefPropStmt) -> Self {
        DefPredicateStmt::DefPropStmt(v).into()
    }
}

impl From<DefAbstractPropStmt> for Stmt {
    fn from(v: DefAbstractPropStmt) -> Self {
        DefPredicateStmt::DefAbstractPropStmt(v).into()
    }
}

impl From<AliasPropStmt> for Stmt {
    fn from(v: AliasPropStmt) -> Self {
        DefAliasStmt::AliasPropStmt(v).into()
    }
}

impl From<AliasThmStmt> for Stmt {
    fn from(v: AliasThmStmt) -> Self {
        DefAliasStmt::AliasThmStmt(v).into()
    }
}

impl From<HaveObjInNonemptySetOrParamTypeStmt> for Stmt {
    fn from(v: HaveObjInNonemptySetOrParamTypeStmt) -> Self {
        DefObjStmt::HaveObjInNonemptySetStmt(v).into()
    }
}

impl From<HaveObjEqualStmt> for Stmt {
    fn from(v: HaveObjEqualStmt) -> Self {
        DefObjStmt::HaveObjEqualStmt(v).into()
    }
}

impl From<HaveObjByExistFactsStmt> for Stmt {
    fn from(v: HaveObjByExistFactsStmt) -> Self {
        DefObjStmt::HaveObjByExistFactsStmt(v).into()
    }
}

impl From<HaveByExistStmt> for Stmt {
    fn from(v: HaveByExistStmt) -> Self {
        DefObjStmt::HaveByExistStmt(v).into()
    }
}

impl From<HaveByPreimageStmt> for Stmt {
    fn from(v: HaveByPreimageStmt) -> Self {
        DefObjStmt::HaveByPreimageStmt(v).into()
    }
}

impl From<HaveFnEqualStmt> for Stmt {
    fn from(v: HaveFnEqualStmt) -> Self {
        DefObjStmt::HaveFnEqualStmt(v).into()
    }
}

impl From<HaveFnEqualCaseByCaseStmt> for Stmt {
    fn from(v: HaveFnEqualCaseByCaseStmt) -> Self {
        DefObjStmt::HaveFnEqualCaseByCaseStmt(v).into()
    }
}

impl From<HaveFnByInducStmt> for Stmt {
    fn from(v: HaveFnByInducStmt) -> Self {
        DefObjStmt::HaveFnByInducStmt(v).into()
    }
}

impl From<HaveFnByForallExistUniqueStmt> for Stmt {
    fn from(v: HaveFnByForallExistUniqueStmt) -> Self {
        DefObjStmt::HaveFnByForallExistUniqueStmt(v).into()
    }
}

impl From<DefTemplateStmt> for Stmt {
    fn from(v: DefTemplateStmt) -> Self {
        DefInterfaceStmt::DefTemplateStmt(v).into()
    }
}

impl From<DefAlgoStmt> for Stmt {
    fn from(v: DefAlgoStmt) -> Self {
        Stmt::DefAlgoStmt(v)
    }
}

impl From<ClaimStmt> for Stmt {
    fn from(v: ClaimStmt) -> Self {
        ProofBlockStmt::ClaimStmt(v).into()
    }
}

impl From<KnowStmt> for Stmt {
    fn from(v: KnowStmt) -> Self {
        UnsafeStmt::KnowStmt(v).into()
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

impl From<ImportStmt> for Stmt {
    fn from(v: ImportStmt) -> Self {
        CommandStmt::ImportStmt(v).into()
    }
}

impl From<DoNothingStmt> for Stmt {
    fn from(v: DoNothingStmt) -> Self {
        CommandStmt::DoNothingStmt(v).into()
    }
}

impl From<ClearStmt> for Stmt {
    fn from(v: ClearStmt) -> Self {
        CommandStmt::ClearStmt(v).into()
    }
}

impl From<StopImportStmt> for Stmt {
    fn from(v: StopImportStmt) -> Self {
        CommandStmt::StopImportStmt(v).into()
    }
}

impl From<RunFileStmt> for Stmt {
    fn from(v: RunFileStmt) -> Self {
        CommandStmt::RunFileStmt(v).into()
    }
}

impl From<EvalStmt> for Stmt {
    fn from(v: EvalStmt) -> Self {
        CommandStmt::EvalStmt(v).into()
    }
}

impl From<EvalByStmt> for Stmt {
    fn from(v: EvalByStmt) -> Self {
        CommandStmt::EvalByStmt(v).into()
    }
}

impl From<WitnessExistFact> for Stmt {
    fn from(v: WitnessExistFact) -> Self {
        WitnessStmt::WitnessExistFact(v).into()
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

impl From<ByAntisymmetricPropStmt> for Stmt {
    fn from(v: ByAntisymmetricPropStmt) -> Self {
        ByStmt::ByAntisymmetricPropStmt(v).into()
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

impl From<ByThmStmt> for Stmt {
    fn from(v: ByThmStmt) -> Self {
        ByStmt::ByThmStmt(v).into()
    }
}

impl From<DefThmStmt> for Stmt {
    fn from(v: DefThmStmt) -> Self {
        Stmt::DefThmStmt(v)
    }
}

impl From<UseStrategyStmt> for Stmt {
    fn from(v: UseStrategyStmt) -> Self {
        CommandStmt::UseStrategyStmt(v).into()
    }
}

impl From<StopStrategyStmt> for Stmt {
    fn from(v: StopStrategyStmt) -> Self {
        CommandStmt::StopStrategyStmt(v).into()
    }
}

impl From<DefStrategyStmt> for Stmt {
    fn from(v: DefStrategyStmt) -> Self {
        Stmt::DefStrategyStmt(v)
    }
}

impl From<DefStructStmt> for Stmt {
    fn from(v: DefStructStmt) -> Self {
        DefInterfaceStmt::DefStructStmt(v).into()
    }
}

impl From<DefObjStmt> for Stmt {
    fn from(v: DefObjStmt) -> Self {
        Stmt::DefObjStmt(v)
    }
}

impl From<DefPredicateStmt> for Stmt {
    fn from(v: DefPredicateStmt) -> Self {
        Stmt::DefPredicateStmt(v)
    }
}

impl From<DefAliasStmt> for Stmt {
    fn from(v: DefAliasStmt) -> Self {
        Stmt::DefAliasStmt(v)
    }
}

impl From<DefInterfaceStmt> for Stmt {
    fn from(v: DefInterfaceStmt) -> Self {
        Stmt::DefInterfaceStmt(v)
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
