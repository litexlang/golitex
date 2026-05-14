use crate::prelude::*;

impl ProveStmt {
    pub fn stmt_type_name(&self) -> String {
        "ProveStmt".to_string()
    }
}

impl ClaimStmt {
    pub fn stmt_type_name(&self) -> String {
        "ClaimStmt".to_string()
    }
}

impl KnowStmt {
    pub fn stmt_type_name(&self) -> String {
        "KnowStmt".to_string()
    }
}

impl EvalStmt {
    pub fn stmt_type_name(&self) -> String {
        "EvalStmt".to_string()
    }
}

impl EvalByStmt {
    pub fn stmt_type_name(&self) -> String {
        "EvalByStmt".to_string()
    }
}

impl DefAlgoStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefAlgoStmt".to_string()
    }
}

impl RunFileStmt {
    pub fn stmt_type_name(&self) -> String {
        "RunFileStmt".to_string()
    }
}

impl ImportRelativePathStmt {
    pub fn stmt_type_name(&self) -> String {
        "ImportRelativePathStmt".to_string()
    }
}

impl ImportGlobalModuleStmt {
    pub fn stmt_type_name(&self) -> String {
        "ImportGlobalModuleStmt".to_string()
    }
}

impl ImportStmt {
    pub fn stmt_type_name(&self) -> String {
        match self {
            ImportStmt::ImportRelativePath(stmt) => stmt.stmt_type_name(),
            ImportStmt::ImportGlobalModule(stmt) => stmt.stmt_type_name(),
        }
    }
}

impl DoNothingStmt {
    pub fn stmt_type_name(&self) -> String {
        "DoNothingStmt".to_string()
    }
}

impl ClearStmt {
    pub fn stmt_type_name(&self) -> String {
        "ClearStmt".to_string()
    }
}

impl WitnessExistFact {
    pub fn stmt_type_name(&self) -> String {
        "WitnessExistFact".to_string()
    }
}

impl WitnessNonemptySet {
    pub fn stmt_type_name(&self) -> String {
        "WitnessNonemptySet".to_string()
    }
}

impl ByEnumerateFiniteSetStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByEnumerateFiniteSetStmt".to_string()
    }
}

impl ByCasesStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByCasesStmt".to_string()
    }
}

impl ByContraStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByContraStmt".to_string()
    }
}

impl ByInducStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByInducStmt".to_string()
    }
}

impl ByForStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByForStmt".to_string()
    }
}

impl ByExtensionStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByExtensionStmt".to_string()
    }
}

impl ByFnAsSetStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByFnAsSetStmt".to_string()
    }
}

impl ByFnSetAsSetStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByFnSetAsSetStmt".to_string()
    }
}

impl ByFamilyAsSetStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByFamilyAsSetStmt".to_string()
    }
}

impl ByTupleAsSetStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByTupleAsSetStmt".to_string()
    }
}

impl ByClosedRangeAsCasesStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByClosedRangeAsCasesStmt".to_string()
    }
}

impl ByTransitivePropStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByTransitivePropStmt".to_string()
    }
}

impl ByCommutativePropStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByCommutativePropStmt".to_string()
    }
}

impl DefAbstractPropStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefAbstractPropStmt".to_string()
    }
}

impl DefPropStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefPropStmt".to_string()
    }
}

impl DefLetStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefLetStmt".to_string()
    }
}

impl HaveObjInNonemptySetOrParamTypeStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveObjInNonemptySetOrParamTypeStmt".to_string()
    }
}

impl HaveObjEqualStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveObjEqualStmt".to_string()
    }
}

impl HaveByExistStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveExistObjStmt".to_string()
    }
}

impl HaveFnEqualStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveFnEqualStmt".to_string()
    }
}

impl HaveFnEqualCaseByCaseStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveFnEqualCaseByCaseStmt".to_string()
    }
}

impl HaveFnByInducStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveFnByInducStmt".to_string()
    }
}

impl HaveFnByForallExistUniqueStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveFnByForallExistUniqueStmt".to_string()
    }
}

impl DefFamilyStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefFamilyStmt".to_string()
    }
}
