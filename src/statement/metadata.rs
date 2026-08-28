//! Source metadata access for statements.

use crate::prelude::*;

impl Stmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            Stmt::Fact(fact) => fact.line_file(),
            Stmt::UnsafeStmt(stmt) => stmt.line_file(),
            Stmt::Definition(stmt) => stmt.line_file(),
            Stmt::ReleaseThmStmt(stmt) => stmt.line_file.clone(),
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
            Stmt::Definition(stmt) => stmt.stmt_type_name(),
            Stmt::ReleaseThmStmt(stmt) => stmt.stmt_type_name(),
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
            Stmt::Definition(stmt) => stmt.output_type_string(),
            Stmt::ReleaseThmStmt(_) => ReleaseThmStmt::output_type_string(),
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

impl DefinitionStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            DefinitionStmt::LetObjStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveObjInNonemptySetStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveObjEqualStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveObjByExistFactsStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::ObtainObjFromExistFact(stmt) => stmt.line_file.clone(),
            DefinitionStmt::ObtainObjFromAtomicFact(stmt) => stmt.line_file.clone(),
            DefinitionStmt::ObtainObjFromThm(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveByPreimageStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveFnEqualStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveFnByInducStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveFnByForallExistUniqueStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveTupleStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveCartStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveSeqStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveFiniteSeqStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::HaveMatrixStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::DefPropStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::DefAbstractPropStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::DefSettingStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::DefTemplateStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::DefStructStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::DefAlgoStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::DefThmStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::AxiomStmt(stmt) => stmt.line_file.clone(),
            DefinitionStmt::DefStrategyStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            DefinitionStmt::LetObjStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveObjInNonemptySetStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveObjEqualStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveObjByExistFactsStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::ObtainObjFromExistFact(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::ObtainObjFromAtomicFact(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::ObtainObjFromThm(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveByPreimageStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveFnEqualStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveFnEqualCaseByCaseStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveFnByInducStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveFnByForallExistUniqueStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveTupleStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveCartStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveSeqStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveFiniteSeqStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::HaveMatrixStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::DefPropStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::DefAbstractPropStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::DefSettingStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::DefTemplateStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::DefStructStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::DefAlgoStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::DefThmStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::AxiomStmt(stmt) => stmt.stmt_type_name(),
            DefinitionStmt::DefStrategyStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            DefinitionStmt::LetObjStmt(_) => LetObjStmt::output_type_string(),
            DefinitionStmt::HaveObjInNonemptySetStmt(_) => {
                HaveObjInNonemptySetOrParamTypeStmt::output_type_string()
            }
            DefinitionStmt::HaveObjEqualStmt(_) => HaveObjEqualStmt::output_type_string(),
            DefinitionStmt::HaveObjByExistFactsStmt(_) => {
                HaveObjByExistFactsStmt::output_type_string()
            }
            DefinitionStmt::ObtainObjFromExistFact(_) => {
                ObtainObjFromExistFact::output_type_string()
            }
            DefinitionStmt::ObtainObjFromAtomicFact(_) => {
                ObtainObjFromAtomicFact::output_type_string()
            }
            DefinitionStmt::ObtainObjFromThm(_) => ObtainObjFromThm::output_type_string(),
            DefinitionStmt::HaveByPreimageStmt(_) => HaveByPreimageStmt::output_type_string(),
            DefinitionStmt::HaveFnEqualStmt(_) => HaveFnEqualStmt::output_type_string(),
            DefinitionStmt::HaveFnEqualCaseByCaseStmt(_) => {
                HaveFnEqualCaseByCaseStmt::output_type_string()
            }
            DefinitionStmt::HaveFnByInducStmt(_) => HaveFnByInducStmt::output_type_string(),
            DefinitionStmt::HaveFnByForallExistUniqueStmt(_) => {
                HaveFnByForallExistUniqueStmt::output_type_string()
            }
            DefinitionStmt::HaveTupleStmt(_) => HaveTupleStmt::output_type_string(),
            DefinitionStmt::HaveCartStmt(_) => HaveCartStmt::output_type_string(),
            DefinitionStmt::HaveSeqStmt(_) => HaveSeqStmt::output_type_string(),
            DefinitionStmt::HaveFiniteSeqStmt(_) => HaveFiniteSeqStmt::output_type_string(),
            DefinitionStmt::HaveMatrixStmt(_) => HaveMatrixStmt::output_type_string(),
            DefinitionStmt::DefPropStmt(_) => DefPropStmt::output_type_string(),
            DefinitionStmt::DefAbstractPropStmt(_) => DefAbstractPropStmt::output_type_string(),
            DefinitionStmt::DefSettingStmt(_) => DefSettingStmt::output_type_string(),
            DefinitionStmt::DefTemplateStmt(_) => DefTemplateStmt::output_type_string(),
            DefinitionStmt::DefStructStmt(_) => DefStructStmt::output_type_string(),
            DefinitionStmt::DefAlgoStmt(_) => DefAlgoStmt::output_type_string(),
            DefinitionStmt::DefThmStmt(_) => DefThmStmt::output_type_string(),
            DefinitionStmt::AxiomStmt(_) => AxiomStmt::output_type_string(),
            DefinitionStmt::DefStrategyStmt(_) => DefStrategyStmt::output_type_string(),
        }
    }
}

impl ByStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            ByStmt::ByCasesStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByContraStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByEnumerateFiniteSetStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByFiniteSetInducStmt(stmt) => stmt.line_file.clone(),
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
            ByStmt::ByDefStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByStructDefStmt(stmt) => stmt.line_file.clone(),
            ByStmt::ByThmStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            ByStmt::ByCasesStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByContraStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByEnumerateFiniteSetStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByFiniteSetInducStmt(stmt) => stmt.stmt_type_name(),
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
            ByStmt::ByDefStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByStructDefStmt(stmt) => stmt.stmt_type_name(),
            ByStmt::ByThmStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            ByStmt::ByCasesStmt(_) => ByCasesStmt::output_type_string(),
            ByStmt::ByContraStmt(_) => ByContraStmt::output_type_string(),
            ByStmt::ByEnumerateFiniteSetStmt(_) => ByEnumerateFiniteSetStmt::output_type_string(),
            ByStmt::ByFiniteSetInducStmt(_) => ByFiniteSetInducStmt::output_type_string(),
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
            ByStmt::ByDefStmt(_) => ByDefStmt::output_type_string(),
            ByStmt::ByStructDefStmt(_) => ByStructDefStmt::output_type_string(),
            ByStmt::ByThmStmt(_) => ByThmStmt::output_type_string(),
        }
    }
}

impl WitnessStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            WitnessStmt::WitnessExistFact(stmt) => stmt.line_file.clone(),
            WitnessStmt::WitnessAtomicFact(stmt) => stmt.line_file.clone(),
            WitnessStmt::WitnessNonemptySet(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            WitnessStmt::WitnessExistFact(stmt) => stmt.stmt_type_name(),
            WitnessStmt::WitnessAtomicFact(stmt) => stmt.stmt_type_name(),
            WitnessStmt::WitnessNonemptySet(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            WitnessStmt::WitnessExistFact(_) => WitnessExistFact::output_type_string(),
            WitnessStmt::WitnessAtomicFact(_) => WitnessAtomicFact::output_type_string(),
            WitnessStmt::WitnessNonemptySet(_) => WitnessNonemptySet::output_type_string(),
        }
    }
}

impl ProofBlockStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            ProofBlockStmt::ClaimStmt(stmt) => stmt.line_file.clone(),
            ProofBlockStmt::ExampleStmt(stmt) => stmt.line_file.clone(),
            ProofBlockStmt::SketchStmt(stmt) => stmt.line_file.clone(),
            ProofBlockStmt::TryStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            ProofBlockStmt::ClaimStmt(stmt) => stmt.stmt_type_name(),
            ProofBlockStmt::ExampleStmt(stmt) => stmt.stmt_type_name(),
            ProofBlockStmt::SketchStmt(stmt) => stmt.stmt_type_name(),
            ProofBlockStmt::TryStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            ProofBlockStmt::ClaimStmt(_) => ClaimStmt::output_type_string(),
            ProofBlockStmt::ExampleStmt(_) => ExampleStmt::output_type_string(),
            ProofBlockStmt::SketchStmt(_) => SketchStmt::output_type_string(),
            ProofBlockStmt::TryStmt(_) => TryStmt::output_type_string(),
        }
    }
}

impl CommandStmt {
    pub fn line_file(&self) -> LineFile {
        match self {
            CommandStmt::EvalStmt(stmt) => stmt.line_file.clone(),
        }
    }

    pub fn stmt_type_name(&self) -> String {
        match self {
            CommandStmt::EvalStmt(stmt) => stmt.stmt_type_name(),
        }
    }

    pub fn output_type_string(&self) -> String {
        match self {
            CommandStmt::EvalStmt(_) => EvalStmt::output_type_string(),
        }
    }
}
