//! Canonical statement display implementations.

use crate::prelude::*;
use std::fmt;

impl fmt::Debug for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self)
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Stmt::Fact(x) => write!(f, "{}", x),
            Stmt::UnsafeStmt(x) => write!(f, "{}", x),
            Stmt::Definition(x) => write!(f, "{}", x),
            Stmt::ReleaseThmStmt(x) => write!(f, "{}", x),
            Stmt::By(x) => write!(f, "{}", x),
            Stmt::Witness(x) => write!(f, "{}", x),
            Stmt::ProofBlock(x) => write!(f, "{}", x),
            Stmt::Command(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for UnsafeStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            UnsafeStmt::TrustStmt(x) => write!(f, "{}", x),
            UnsafeStmt::TrustHaveStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for DefinitionStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            DefinitionStmt::LetObjStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveObjInNonemptySetStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveObjEqualStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveObjByExistFactsStmt(x) => write!(f, "{}", x),
            DefinitionStmt::ObtainObjFromExistFact(x) => write!(f, "{}", x),
            DefinitionStmt::ObtainObjFromAtomicFact(x) => write!(f, "{}", x),
            DefinitionStmt::ObtainObjFromThm(x) => write!(f, "{}", x),
            DefinitionStmt::HaveByPreimageStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveFnEqualStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveFnEqualCaseByCaseStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveFnByInducStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveFnByForallExistUniqueStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveTupleStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveCartStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveSeqStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveFiniteSeqStmt(x) => write!(f, "{}", x),
            DefinitionStmt::HaveMatrixStmt(x) => write!(f, "{}", x),
            DefinitionStmt::DefPropStmt(x) => write!(f, "{}", x),
            DefinitionStmt::DefAbstractPropStmt(x) => write!(f, "{}", x),
            DefinitionStmt::DefSettingStmt(x) => write!(f, "{}", x),
            DefinitionStmt::DefTemplateStmt(x) => write!(f, "{}", x),
            DefinitionStmt::DefStructStmt(x) => write!(f, "{}", x),
            DefinitionStmt::DefAlgoStmt(x) => write!(f, "{}", x),
            DefinitionStmt::DefThmStmt(x) => write!(f, "{}", x),
            DefinitionStmt::AxiomStmt(x) => write!(f, "{}", x),
            DefinitionStmt::DefStrategyStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for ByStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            ByStmt::ByCasesStmt(x) => write!(f, "{}", x),
            ByStmt::ByContraStmt(x) => write!(f, "{}", x),
            ByStmt::ByEnumerateFiniteSetStmt(x) => write!(f, "{}", x),
            ByStmt::ByFiniteSetInducStmt(x) => write!(f, "{}", x),
            ByStmt::ByInducStmt(x) => write!(f, "{}", x),
            ByStmt::ByForStmt(x) => write!(f, "{}", x),
            ByStmt::ByExtensionStmt(x) => write!(f, "{}", x),
            ByStmt::ByEnumerateRangeStmt(x) => write!(f, "{}", x),
            ByStmt::ByClosedRangeAsCasesStmt(x) => write!(f, "{}", x),
            ByStmt::ByTransitivePropStmt(x) => write!(f, "{}", x),
            ByStmt::BySymmetricPropStmt(x) => write!(f, "{}", x),
            ByStmt::ByReflexivePropStmt(x) => write!(f, "{}", x),
            ByStmt::ByAntisymmetricPropStmt(x) => write!(f, "{}", x),
            ByStmt::ByZornLemmaStmt(x) => write!(f, "{}", x),
            ByStmt::ByAxiomOfChoiceStmt(x) => write!(f, "{}", x),
            ByStmt::ByRegularityAxiomStmt(x) => write!(f, "{}", x),
            ByStmt::ByDefStmt(x) => write!(f, "{}", x),
            ByStmt::ByStructDefStmt(x) => write!(f, "{}", x),
            ByStmt::ByThmStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for WitnessStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            WitnessStmt::WitnessExistFact(x) => write!(f, "{}", x),
            WitnessStmt::WitnessAtomicFact(x) => write!(f, "{}", x),
            WitnessStmt::WitnessNonemptySet(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for ProofBlockStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            ProofBlockStmt::ClaimStmt(x) => write!(f, "{}", x),
            ProofBlockStmt::ExampleStmt(x) => write!(f, "{}", x),
            ProofBlockStmt::SketchStmt(x) => write!(f, "{}", x),
            ProofBlockStmt::TryStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for CommandStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            CommandStmt::EvalStmt(x) => write!(f, "{}", x),
        }
    }
}
