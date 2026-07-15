use crate::prelude::*;
use std::fmt;

impl fmt::Debug for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Fact(x) => write!(f, "{}", x),
            Stmt::UnsafeStmt(x) => write!(f, "{}", x),
            Stmt::DefObjStmt(x) => write!(f, "{}", x),
            Stmt::DefPredicateStmt(x) => write!(f, "{}", x),
            Stmt::DefAliasStmt(x) => write!(f, "{}", x),
            Stmt::DefInterfaceStmt(x) => write!(f, "{}", x),
            Stmt::DefAlgoStmt(x) => write!(f, "{}", x),
            Stmt::DefThmStmt(x) => write!(f, "{}", x),
            Stmt::DefStrategyStmt(x) => write!(f, "{}", x),
            Stmt::By(x) => write!(f, "{}", x),
            Stmt::Witness(x) => write!(f, "{}", x),
            Stmt::ProofBlock(x) => write!(f, "{}", x),
            Stmt::Command(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for UnsafeStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnsafeStmt::TrustStmt(x) => write!(f, "{}", x),
            UnsafeStmt::TrustHaveStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for DefObjStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefObjStmt::HaveObjInNonemptySetStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveObjEqualStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveObjByExistFactsStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveByExistStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveByPreimageStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveFnEqualStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveFnEqualCaseByCaseStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveFnByInducStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveFnByForallExistUniqueStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveTupleStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveCartStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveSeqStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveFiniteSeqStmt(x) => write!(f, "{}", x),
            DefObjStmt::HaveMatrixStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for DefPredicateStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefPredicateStmt::DefPropStmt(x) => write!(f, "{}", x),
            DefPredicateStmt::DefAbstractPropStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for DefAliasStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefAliasStmt::AliasPropStmt(x) => write!(f, "{}", x),
            DefAliasStmt::AliasThmStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for DefInterfaceStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DefInterfaceStmt::DefTemplateStmt(x) => write!(f, "{}", x),
            DefInterfaceStmt::DefStructStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for ByStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
            ByStmt::ByThmStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for WitnessStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WitnessStmt::WitnessExistFact(x) => write!(f, "{}", x),
            WitnessStmt::WitnessNonemptySet(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for ProofBlockStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofBlockStmt::ClaimStmt(x) => write!(f, "{}", x),
            ProofBlockStmt::SketchStmt(x) => write!(f, "{}", x),
            ProofBlockStmt::TryStmt(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for CommandStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CommandStmt::ImportStmt(x) => write!(f, "{}", x),
            CommandStmt::TrustImportStmt(x) => write!(f, "{}", x),
            CommandStmt::LocalImportStmt(x) => write!(f, "{}", x),
            CommandStmt::TrustLocalImportStmt(x) => write!(f, "{}", x),
            CommandStmt::DoNothingStmt(x) => write!(f, "{}", x),
            CommandStmt::ClearStmt(x) => write!(f, "{}", x),
            CommandStmt::EvalStmt(x) => write!(f, "{}", x),
            CommandStmt::EvalByStmt(x) => write!(f, "{}", x),
            CommandStmt::UseStrategyStmt(x) => write!(f, "{}", x),
            CommandStmt::StopStrategyStmt(x) => write!(f, "{}", x),
        }
    }
}
