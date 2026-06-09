use crate::prelude::*;

#[derive(Debug)]
pub enum ByStmtResult {
    ByCasesStmt(NonFactualStmtSuccess),
    ByContraStmt(NonFactualStmtSuccess),
    ByEnumerateFiniteSetStmt(NonFactualStmtSuccess),
    ByInducStmt(NonFactualStmtSuccess),
    ByForStmt(NonFactualStmtSuccess),
    ByExtensionStmt(NonFactualStmtSuccess),
    ByFnAsSetStmt(NonFactualStmtSuccess),
    ByTupleAsSetStmt(NonFactualStmtSuccess),
    ByFnSetAsSetStmt(NonFactualStmtSuccess),
    ByEnumerateRangeStmt(NonFactualStmtSuccess),
    ByClosedRangeAsCasesStmt(NonFactualStmtSuccess),
    ByTransitivePropStmt(NonFactualStmtSuccess),
    BySymmetricPropStmt(NonFactualStmtSuccess),
    ByReflexivePropStmt(NonFactualStmtSuccess),
    ByAntisymmetricPropStmt(NonFactualStmtSuccess),
    ByZornLemmaStmt(NonFactualStmtSuccess),
    ByAxiomOfChoiceStmt(NonFactualStmtSuccess),
    ByThmStmt(NonFactualStmtSuccess),
}

impl ByStmtResult {
    pub fn new(success: NonFactualStmtSuccess) -> Self {
        match &success.stmt {
            Stmt::By(ByStmt::ByCasesStmt(_)) => ByStmtResult::ByCasesStmt(success),
            Stmt::By(ByStmt::ByContraStmt(_)) => ByStmtResult::ByContraStmt(success),
            Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(_)) => {
                ByStmtResult::ByEnumerateFiniteSetStmt(success)
            }
            Stmt::By(ByStmt::ByInducStmt(_)) => ByStmtResult::ByInducStmt(success),
            Stmt::By(ByStmt::ByForStmt(_)) => ByStmtResult::ByForStmt(success),
            Stmt::By(ByStmt::ByExtensionStmt(_)) => ByStmtResult::ByExtensionStmt(success),
            Stmt::By(ByStmt::ByFnAsSetStmt(_)) => ByStmtResult::ByFnAsSetStmt(success),
            Stmt::By(ByStmt::ByTupleAsSetStmt(_)) => ByStmtResult::ByTupleAsSetStmt(success),
            Stmt::By(ByStmt::ByFnSetAsSetStmt(_)) => ByStmtResult::ByFnSetAsSetStmt(success),
            Stmt::By(ByStmt::ByEnumerateRangeStmt(_)) => {
                ByStmtResult::ByEnumerateRangeStmt(success)
            }
            Stmt::By(ByStmt::ByClosedRangeAsCasesStmt(_)) => {
                ByStmtResult::ByClosedRangeAsCasesStmt(success)
            }
            Stmt::By(ByStmt::ByTransitivePropStmt(_)) => {
                ByStmtResult::ByTransitivePropStmt(success)
            }
            Stmt::By(ByStmt::BySymmetricPropStmt(_)) => ByStmtResult::BySymmetricPropStmt(success),
            Stmt::By(ByStmt::ByReflexivePropStmt(_)) => ByStmtResult::ByReflexivePropStmt(success),
            Stmt::By(ByStmt::ByAntisymmetricPropStmt(_)) => {
                ByStmtResult::ByAntisymmetricPropStmt(success)
            }
            Stmt::By(ByStmt::ByZornLemmaStmt(_)) => ByStmtResult::ByZornLemmaStmt(success),
            Stmt::By(ByStmt::ByAxiomOfChoiceStmt(_)) => ByStmtResult::ByAxiomOfChoiceStmt(success),
            Stmt::By(ByStmt::ByThmStmt(_)) => ByStmtResult::ByThmStmt(success),
            _ => panic!("expected by stmt result"),
        }
    }

    pub fn success(&self) -> &NonFactualStmtSuccess {
        match self {
            ByStmtResult::ByCasesStmt(success)
            | ByStmtResult::ByContraStmt(success)
            | ByStmtResult::ByEnumerateFiniteSetStmt(success)
            | ByStmtResult::ByInducStmt(success)
            | ByStmtResult::ByForStmt(success)
            | ByStmtResult::ByExtensionStmt(success)
            | ByStmtResult::ByFnAsSetStmt(success)
            | ByStmtResult::ByTupleAsSetStmt(success)
            | ByStmtResult::ByFnSetAsSetStmt(success)
            | ByStmtResult::ByEnumerateRangeStmt(success)
            | ByStmtResult::ByClosedRangeAsCasesStmt(success)
            | ByStmtResult::ByTransitivePropStmt(success)
            | ByStmtResult::BySymmetricPropStmt(success)
            | ByStmtResult::ByReflexivePropStmt(success)
            | ByStmtResult::ByAntisymmetricPropStmt(success)
            | ByStmtResult::ByZornLemmaStmt(success)
            | ByStmtResult::ByAxiomOfChoiceStmt(success)
            | ByStmtResult::ByThmStmt(success) => success,
        }
    }

    pub fn success_mut(&mut self) -> &mut NonFactualStmtSuccess {
        match self {
            ByStmtResult::ByCasesStmt(success)
            | ByStmtResult::ByContraStmt(success)
            | ByStmtResult::ByEnumerateFiniteSetStmt(success)
            | ByStmtResult::ByInducStmt(success)
            | ByStmtResult::ByForStmt(success)
            | ByStmtResult::ByExtensionStmt(success)
            | ByStmtResult::ByFnAsSetStmt(success)
            | ByStmtResult::ByTupleAsSetStmt(success)
            | ByStmtResult::ByFnSetAsSetStmt(success)
            | ByStmtResult::ByEnumerateRangeStmt(success)
            | ByStmtResult::ByClosedRangeAsCasesStmt(success)
            | ByStmtResult::ByTransitivePropStmt(success)
            | ByStmtResult::BySymmetricPropStmt(success)
            | ByStmtResult::ByReflexivePropStmt(success)
            | ByStmtResult::ByAntisymmetricPropStmt(success)
            | ByStmtResult::ByZornLemmaStmt(success)
            | ByStmtResult::ByAxiomOfChoiceStmt(success)
            | ByStmtResult::ByThmStmt(success) => success,
        }
    }

    pub fn into_success(self) -> NonFactualStmtSuccess {
        match self {
            ByStmtResult::ByCasesStmt(success)
            | ByStmtResult::ByContraStmt(success)
            | ByStmtResult::ByEnumerateFiniteSetStmt(success)
            | ByStmtResult::ByInducStmt(success)
            | ByStmtResult::ByForStmt(success)
            | ByStmtResult::ByExtensionStmt(success)
            | ByStmtResult::ByFnAsSetStmt(success)
            | ByStmtResult::ByTupleAsSetStmt(success)
            | ByStmtResult::ByFnSetAsSetStmt(success)
            | ByStmtResult::ByEnumerateRangeStmt(success)
            | ByStmtResult::ByClosedRangeAsCasesStmt(success)
            | ByStmtResult::ByTransitivePropStmt(success)
            | ByStmtResult::BySymmetricPropStmt(success)
            | ByStmtResult::ByReflexivePropStmt(success)
            | ByStmtResult::ByAntisymmetricPropStmt(success)
            | ByStmtResult::ByZornLemmaStmt(success)
            | ByStmtResult::ByAxiomOfChoiceStmt(success)
            | ByStmtResult::ByThmStmt(success) => success,
        }
    }
}
