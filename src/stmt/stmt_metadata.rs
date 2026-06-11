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
}

impl UnsafeStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            UnsafeStmt::KnowStmt(stmt) => stmt.line_file.clone(),
            UnsafeStmt::DefLetStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            UnsafeStmt::KnowStmt(stmt) => stmt.stmt_type_name(),
            UnsafeStmt::DefLetStmt(stmt) => stmt.stmt_type_name(),
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
            ByStmt::ByFnAsSetStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByTupleAsSetStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByFnSetAsSetStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByEnumerateRangeStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByClosedRangeAsCasesStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByTransitivePropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::BySymmetricPropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByReflexivePropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByAntisymmetricPropStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByZornLemmaStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByAxiomOfChoiceStmt(stmt) => stmt.line_file.clone(),
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
            ByStmt::ByFnAsSetStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByTupleAsSetStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByFnSetAsSetStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByEnumerateRangeStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByClosedRangeAsCasesStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByTransitivePropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::BySymmetricPropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByReflexivePropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByAntisymmetricPropStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByZornLemmaStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByAxiomOfChoiceStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByThmStmt(stmt) => stmt.stmt_type_name(),
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
}

impl ProofBlockStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            ProofBlockStmt::ClaimStmt(stmt) => stmt.line_file.clone(),
            ProofBlockStmt::SketchStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            ProofBlockStmt::ClaimStmt(stmt) => stmt.stmt_type_name(),
            ProofBlockStmt::SketchStmt(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl CommandStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            CommandStmt::ImportStmt(stmt) => stmt.line_file(),
            CommandStmt::DoNothingStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::ClearStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::StopImportStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::RunFileStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::EvalStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::EvalByStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::UseStrategyStmt(stmt) => stmt.line_file.clone(),
            CommandStmt::StopStrategyStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            CommandStmt::ImportStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::DoNothingStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::ClearStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::StopImportStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::RunFileStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::EvalStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::EvalByStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::UseStrategyStmt(stmt) => stmt.stmt_type_name(),
            CommandStmt::StopStrategyStmt(stmt) => stmt.stmt_type_name(),
        }
    }
}
