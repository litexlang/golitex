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

impl EnumerateAxiomStmt {
    pub fn stmt_type_name(&self) -> String {
        "EnumerateAxiomStmt".to_string()
    }
}

impl ByCasesAxiomStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByCasesAxiomStmt".to_string()
    }
}

impl ByContraAxiomStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByContraAxiomStmt".to_string()
    }
}

impl ByInducAxiomStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByInducAxiomStmt".to_string()
    }
}

impl ForAxiomStmt {
    pub fn stmt_type_name(&self) -> String {
        "ForAxiomStmt".to_string()
    }
}

impl ByExtensionAxiomStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByExtensionAxiomStmt".to_string()
    }
}

impl ByFnDefAxiomStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByFnDefAxiomStmt".to_string()
    }
}

impl ByCartDefAxiomStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByCartDefAxiomStmt".to_string()
    }
}

impl DefPropWithoutMeaningStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefPropWithoutMeaningStmt".to_string()
    }
}

impl DefPropWithMeaningStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefPropWithMeaningStmt".to_string()
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

impl HaveExistObjStmt {
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

impl DefStructWithNoFieldStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefStructWithNoFieldStmt".to_string()
    }
}

impl DefStructWithFieldsStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefStructWithFieldsStmt".to_string()
    }
}
