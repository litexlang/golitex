use crate::prelude::*;

impl Stmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            Stmt::Fact(fact) => fact.line_file(),
            Stmt::UnsafeStmt(stmt) => stmt.line_file(),
            Stmt::DefObjStmt(stmt) => stmt.line_file(),
            Stmt::DefPredicateStmt(stmt) => stmt.line_file(),
            Stmt::DefAliasStmt(stmt) => stmt.line_file(),
            Stmt::DefInterfaceStmt(stmt) => stmt.line_file(),
            Stmt::DefAlgoStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefThmStmt(stmt) => stmt.line_file.clone(),
            Stmt::DefStrategyStmt(stmt) => stmt.line_file.clone(),
            Stmt::By(stmt) => stmt.line_file(),
            Stmt::Witness(stmt) => stmt.line_file(),
            Stmt::ProofBlock(stmt) => stmt.line_file(),
            Stmt::Command(stmt) => stmt.line_file(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            Stmt::Fact(fact) => fact.fact_type_string(),
            Stmt::UnsafeStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefObjStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefPredicateStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefAliasStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefInterfaceStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefAlgoStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefThmStmt(stmt) => stmt.stmt_type_name(),
            Stmt::DefStrategyStmt(stmt) => stmt.stmt_type_name(),
            Stmt::By(stmt) => stmt.stmt_type_name(),
            Stmt::Witness(stmt) => stmt.stmt_type_name(),
            Stmt::ProofBlock(stmt) => stmt.stmt_type_name(),
            Stmt::Command(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            Stmt::Fact(fact) => fact.output_type_string(),
            Stmt::UnsafeStmt(stmt) => stmt.output_type_string(),
            Stmt::DefObjStmt(stmt) => stmt.output_type_string(),
            Stmt::DefPredicateStmt(stmt) => stmt.output_type_string(),
            Stmt::DefAliasStmt(stmt) => stmt.output_type_string(),
            Stmt::DefInterfaceStmt(stmt) => stmt.output_type_string(),
            Stmt::DefAlgoStmt(_) => DefAlgoStmt::output_type_string(),
            Stmt::DefThmStmt(stmt) => stmt.output_type_string_for_stmt(),
            Stmt::DefStrategyStmt(_) => DefStrategyStmt::output_type_string(),
            Stmt::By(stmt) => stmt.output_type_string(),
            Stmt::Witness(stmt) => stmt.output_type_string(),
            Stmt::ProofBlock(stmt) => stmt.output_type_string(),
            Stmt::Command(stmt) => stmt.output_type_string(),
        }
    }
}

impl UnsafeStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            UnsafeStmt::TrustStmt(stmt) => stmt.line_file.clone(),
            UnsafeStmt::TrustHaveStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            UnsafeStmt::TrustStmt(stmt) => stmt.stmt_type_name(),
            UnsafeStmt::TrustHaveStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            UnsafeStmt::TrustStmt(_) => TrustStmt::output_type_string(),
            UnsafeStmt::TrustHaveStmt(_) => TrustHaveStmt::output_type_string(),
        }
    }
}

impl DefObjStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            DefObjStmt::HaveObjInNonemptySetStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveObjEqualStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveObjByExistFactsStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveByExistStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveByPreimageStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveFnEqualStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveFnByInducStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveFnByForallExistUniqueStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveTupleStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveCartStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveSeqStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveFiniteSeqStmt(stmt) => stmt.line_file.clone(),
            DefObjStmt::HaveMatrixStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            DefObjStmt::HaveObjInNonemptySetStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveObjEqualStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveObjByExistFactsStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveByExistStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveByPreimageStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveFnEqualStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveFnByInducStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveFnByForallExistUniqueStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveTupleStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveCartStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveSeqStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveFiniteSeqStmt(stmt) => stmt.stmt_type_name(),
            DefObjStmt::HaveMatrixStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            DefObjStmt::HaveObjInNonemptySetStmt(_) => {
                HaveObjInNonemptySetOrParamTypeStmt::output_type_string()
            }
            DefObjStmt::HaveObjEqualStmt(_) => HaveObjEqualStmt::output_type_string(),
            DefObjStmt::HaveObjByExistFactsStmt(_) => HaveObjByExistFactsStmt::output_type_string(),
            DefObjStmt::HaveByExistStmt(_) => HaveByExistStmt::output_type_string(),
            DefObjStmt::HaveByPreimageStmt(_) => HaveByPreimageStmt::output_type_string(),
            DefObjStmt::HaveFnEqualStmt(_) => HaveFnEqualStmt::output_type_string(),
            DefObjStmt::HaveFnEqualCaseByCaseStmt(_) => {
                HaveFnEqualCaseByCaseStmt::output_type_string()
            }
            DefObjStmt::HaveFnByInducStmt(_) => HaveFnByInducStmt::output_type_string(),
            DefObjStmt::HaveFnByForallExistUniqueStmt(_) => {
                HaveFnByForallExistUniqueStmt::output_type_string()
            }
            DefObjStmt::HaveTupleStmt(_) => HaveTupleStmt::output_type_string(),
            DefObjStmt::HaveCartStmt(_) => HaveCartStmt::output_type_string(),
            DefObjStmt::HaveSeqStmt(_) => HaveSeqStmt::output_type_string(),
            DefObjStmt::HaveFiniteSeqStmt(_) => HaveFiniteSeqStmt::output_type_string(),
            DefObjStmt::HaveMatrixStmt(_) => HaveMatrixStmt::output_type_string(),
        }
    }
}

impl DefPredicateStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            DefPredicateStmt::DefPropStmt(stmt) => stmt.line_file.clone(),
            DefPredicateStmt::DefAbstractPropStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            DefPredicateStmt::DefPropStmt(stmt) => stmt.stmt_type_name(),
            DefPredicateStmt::DefAbstractPropStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            DefPredicateStmt::DefPropStmt(_) => DefPropStmt::output_type_string(),
            DefPredicateStmt::DefAbstractPropStmt(_) => DefAbstractPropStmt::output_type_string(),
        }
    }
}

impl DefAliasStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            DefAliasStmt::AliasPropStmt(stmt) => stmt.line_file.clone(),
            DefAliasStmt::AliasThmStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            DefAliasStmt::AliasPropStmt(stmt) => stmt.stmt_type_name(),
            DefAliasStmt::AliasThmStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            DefAliasStmt::AliasPropStmt(_) => AliasPropStmt::output_type_string(),
            DefAliasStmt::AliasThmStmt(_) => AliasThmStmt::output_type_string(),
        }
    }
}

impl DefInterfaceStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            DefInterfaceStmt::DefTemplateStmt(stmt) => stmt.line_file.clone(),
            DefInterfaceStmt::DefStructStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            DefInterfaceStmt::DefTemplateStmt(stmt) => stmt.stmt_type_name(),
            DefInterfaceStmt::DefStructStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            DefInterfaceStmt::DefTemplateStmt(_) => DefTemplateStmt::output_type_string(),
            DefInterfaceStmt::DefStructStmt(_) => DefStructStmt::output_type_string(),
        }
    }
}

impl ByStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            ByStmt::ByCasesStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByContraStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByEnumerateFiniteSetStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByInducStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByForStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByExtensionStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByEnumerateRangeStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByClosedRangeAsCasesStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByTransitivePropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::BySymmetricPropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByReflexivePropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByAntisymmetricPropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByZornLemmaStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByAxiomOfChoiceStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByRegularityAxiomStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByThmStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            ByStmt::ByCasesStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByContraStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByEnumerateFiniteSetStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByInducStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByForStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByExtensionStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByEnumerateRangeStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByClosedRangeAsCasesStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByTransitivePropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::BySymmetricPropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByReflexivePropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByAntisymmetricPropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByZornLemmaStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByAxiomOfChoiceStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByRegularityAxiomStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByThmStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            ByStmt::ByCasesStmt(_) => ByCasesStmt::output_type_string(),
            ByStmt::ByContraStmt(_) => ByContraStmt::output_type_string(),
            ByStmt::ByEnumerateFiniteSetStmt(_) => ByEnumerateFiniteSetStmt::output_type_string(),
            ByStmt::ByInducStmt(_) => ByInducStmt::output_type_string(),
            ByStmt::ByForStmt(_) => ByForStmt::output_type_string(),
            ByStmt::ByExtensionStmt(_) => ByExtensionStmt::output_type_string(),
            ByStmt::ByEnumerateRangeStmt(_) => ByEnumerateRangeStmt::output_type_string(),
            ByStmt::ByClosedRangeAsCasesStmt(_) => ByClosedRangeAsCasesStmt::output_type_string(),
            ByStmt::ByTransitivePropStmt(_) => ByTransitivePropStmt::output_type_string(),
            ByStmt::BySymmetricPropStmt(_) => BySymmetricPropStmt::output_type_string(),
            ByStmt::ByReflexivePropStmt(_) => ByReflexivePropStmt::output_type_string(),
            ByStmt::ByAntisymmetricPropStmt(_) => ByAntisymmetricPropStmt::output_type_string(),
            ByStmt::ByZornLemmaStmt(_) => ByZornLemmaStmt::output_type_string(),
            ByStmt::ByAxiomOfChoiceStmt(_) => ByAxiomOfChoiceStmt::output_type_string(),
            ByStmt::ByRegularityAxiomStmt(_) => ByRegularityAxiomStmt::output_type_string(),
            ByStmt::ByThmStmt(_) => ByThmStmt::output_type_string(),
        }
    }
}

impl WitnessStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            WitnessStmt::WitnessExistFact(stmt) => stmt.line_file.clone(),
            WitnessStmt::WitnessNonemptySet(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            WitnessStmt::WitnessExistFact(stmt) => stmt.stmt_type_name(),
            WitnessStmt::WitnessNonemptySet(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            WitnessStmt::WitnessExistFact(_) => WitnessExistFact::output_type_string(),
            WitnessStmt::WitnessNonemptySet(_) => WitnessNonemptySet::output_type_string(),
        }
    }
}

impl ProofBlockStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            ProofBlockStmt::ClaimStmt(stmt) => stmt.line_file.clone(),
            ProofBlockStmt::SketchStmt(stmt) => stmt.line_file.clone(),
            ProofBlockStmt::TryStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            ProofBlockStmt::ClaimStmt(stmt) => stmt.stmt_type_name(),
            ProofBlockStmt::SketchStmt(stmt) => stmt.stmt_type_name(),
            ProofBlockStmt::TryStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            ProofBlockStmt::ClaimStmt(_) => ClaimStmt::output_type_string(),
            ProofBlockStmt::SketchStmt(_) => SketchStmt::output_type_string(),
            ProofBlockStmt::TryStmt(_) => TryStmt::output_type_string(),
        }
    }
}

impl CommandStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            CommandStmt::ImportStmt(stmt) => stmt.line_file(),
            CommandStmt::TrustImportStmt(stmt) => stmt.line_file(),
            CommandStmt::LocalImportStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::TrustLocalImportStmt(stmt) => stmt.line_file(),
            CommandStmt::DoNothingStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::ClearStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::EvalStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::EvalByStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::UseStrategyStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::StopStrategyStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            CommandStmt::ImportStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::TrustImportStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::LocalImportStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::TrustLocalImportStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::DoNothingStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::ClearStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::EvalStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::EvalByStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::UseStrategyStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::StopStrategyStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            CommandStmt::ImportStmt(stmt) => stmt.output_type_string(),
            CommandStmt::TrustImportStmt(_) => TrustImportStmt::output_type_string(),
            CommandStmt::LocalImportStmt(_) => LocalImportStmt::output_type_string(),
            CommandStmt::TrustLocalImportStmt(_) => TrustLocalImportStmt::output_type_string(),
            CommandStmt::DoNothingStmt(_) => DoNothingStmt::output_type_string(),
            CommandStmt::ClearStmt(_) => ClearStmt::output_type_string(),
            CommandStmt::EvalStmt(_) => EvalStmt::output_type_string(),
            CommandStmt::EvalByStmt(_) => EvalByStmt::output_type_string(),
            CommandStmt::UseStrategyStmt(_) => UseStrategyStmt::output_type_string(),
            CommandStmt::StopStrategyStmt(_) => StopStrategyStmt::output_type_string(),
        }
    }
}
