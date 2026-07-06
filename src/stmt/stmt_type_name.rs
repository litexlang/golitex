use crate::prelude::*;

impl SketchStmt {
    pub fn stmt_type_name(&self) -> String {
        "SketchStmt".to_string()
    }
}

impl TryStmt {
    pub fn stmt_type_name(&self) -> String {
        "TryStmt".to_string()
    }
}

impl ClaimStmt {
    pub fn stmt_type_name(&self) -> String {
        "ClaimStmt".to_string()
    }
}

impl ProofDebtStmt {
    pub fn stmt_type_name(&self) -> String {
        "ProofDebtStmt".to_string()
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

impl DefTemplateStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefTemplateStmt".to_string()
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

impl StopImportStmt {
    pub fn stmt_type_name(&self) -> String {
        "StopImportStmt".to_string()
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

impl ByEnumerateRangeStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByEnumerateRangeStmt".to_string()
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

impl BySymmetricPropStmt {
    pub fn stmt_type_name(&self) -> String {
        "BySymmetricPropStmt".to_string()
    }
}

impl ByReflexivePropStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByReflexivePropStmt".to_string()
    }
}

impl ByAntisymmetricPropStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByAntisymmetricPropStmt".to_string()
    }
}

impl ByZornLemmaStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByZornLemmaStmt".to_string()
    }
}

impl ByAxiomOfChoiceStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByAxiomOfChoiceStmt".to_string()
    }
}

impl ByRegularityAxiomStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByRegularityAxiomStmt".to_string()
    }
}

impl ByThmStmt {
    pub fn stmt_type_name(&self) -> String {
        "ByThmStmt".to_string()
    }
}

impl DefThmStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefThmStmt".to_string()
    }
}

impl UseStrategyStmt {
    pub fn stmt_type_name(&self) -> String {
        "UseStrategyStmt".to_string()
    }
}

impl StopStrategyStmt {
    pub fn stmt_type_name(&self) -> String {
        "StopStrategyStmt".to_string()
    }
}

impl DefStrategyStmt {
    pub fn stmt_type_name(&self) -> String {
        "DefStrategyStmt".to_string()
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

impl AliasPropStmt {
    pub fn stmt_type_name(&self) -> String {
        "AliasPropStmt".to_string()
    }
}

impl AliasThmStmt {
    pub fn stmt_type_name(&self) -> String {
        "AliasThmStmt".to_string()
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

impl HaveObjByExistFactsStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveObjByExistFactsStmt".to_string()
    }
}

impl HaveByExistStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveByExistStmt".to_string()
    }
}

impl HaveByPreimageStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveByPreimageStmt".to_string()
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

impl HaveTupleStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveTupleStmt".to_string()
    }
}

impl HaveCartStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveCartStmt".to_string()
    }
}

impl HaveSeqStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveSeqStmt".to_string()
    }
}

impl HaveFiniteSeqStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveFiniteSeqStmt".to_string()
    }
}

impl HaveMatrixStmt {
    pub fn stmt_type_name(&self) -> String {
        "HaveMatrixStmt".to_string()
    }
}

impl SketchStmt {
    pub fn output_type_string() -> String {
        "proof sketch".to_string()
    }
}

impl TryStmt {
    pub fn output_type_string() -> String {
        "try block".to_string()
    }
}

impl ClaimStmt {
    pub fn output_type_string() -> String {
        "proved claim".to_string()
    }
}

impl ProofDebtStmt {
    pub fn output_type_string() -> String {
        "unproved assumption".to_string()
    }
}

impl EvalStmt {
    pub fn output_type_string() -> String {
        "evaluation statement".to_string()
    }
}

impl EvalByStmt {
    pub fn output_type_string() -> String {
        "evaluation by statement".to_string()
    }
}

impl DefAlgoStmt {
    pub fn output_type_string() -> String {
        "algorithm definition".to_string()
    }
}

impl DefTemplateStmt {
    pub fn output_type_string() -> String {
        "template definition".to_string()
    }
}

impl RunFileStmt {
    pub fn output_type_string() -> String {
        "run file statement".to_string()
    }
}

impl ImportRelativePathStmt {
    pub fn output_type_string() -> String {
        "import statement".to_string()
    }
}

impl ImportGlobalModuleStmt {
    pub fn output_type_string() -> String {
        "import statement".to_string()
    }
}

impl ImportStmt {
    pub fn output_type_string(&self) -> String {
        match self {
            ImportStmt::ImportRelativePath(_) => ImportRelativePathStmt::output_type_string(),
            ImportStmt::ImportGlobalModule(_) => ImportGlobalModuleStmt::output_type_string(),
        }
    }
}

impl DoNothingStmt {
    pub fn output_type_string() -> String {
        "no-op statement".to_string()
    }
}

impl ClearStmt {
    pub fn output_type_string() -> String {
        "clear statement".to_string()
    }
}

impl StopImportStmt {
    pub fn output_type_string() -> String {
        "stop import statement".to_string()
    }
}

impl WitnessExistFact {
    pub fn output_type_string() -> String {
        "existence witness".to_string()
    }
}

impl WitnessNonemptySet {
    pub fn output_type_string() -> String {
        "nonempty set witness".to_string()
    }
}

impl ByEnumerateFiniteSetStmt {
    pub fn output_type_string() -> String {
        "proof by finite set enumeration".to_string()
    }
}

impl ByCasesStmt {
    pub fn output_type_string() -> String {
        "proof by cases".to_string()
    }
}

impl ByContraStmt {
    pub fn output_type_string() -> String {
        "proof by contradiction".to_string()
    }
}

impl ByInducStmt {
    pub fn output_type_string() -> String {
        "proof by induction".to_string()
    }
}

impl ByForStmt {
    pub fn output_type_string() -> String {
        "proof by universal introduction".to_string()
    }
}

impl ByExtensionStmt {
    pub fn output_type_string() -> String {
        "proof by extension".to_string()
    }
}

impl ByEnumerateRangeStmt {
    pub fn output_type_string() -> String {
        "proof by range enumeration".to_string()
    }
}

impl ByClosedRangeAsCasesStmt {
    pub fn output_type_string() -> String {
        "proof by closed range cases".to_string()
    }
}

impl ByTransitivePropStmt {
    pub fn output_type_string() -> String {
        "proof by transitivity".to_string()
    }
}

impl BySymmetricPropStmt {
    pub fn output_type_string() -> String {
        "proof by symmetry".to_string()
    }
}

impl ByReflexivePropStmt {
    pub fn output_type_string() -> String {
        "proof by reflexivity".to_string()
    }
}

impl ByAntisymmetricPropStmt {
    pub fn output_type_string() -> String {
        "proof by antisymmetry".to_string()
    }
}

impl ByZornLemmaStmt {
    pub fn output_type_string() -> String {
        "proof by Zorn lemma".to_string()
    }
}

impl ByAxiomOfChoiceStmt {
    pub fn output_type_string() -> String {
        "proof by axiom of choice".to_string()
    }
}

impl ByRegularityAxiomStmt {
    pub fn output_type_string() -> String {
        "proof by regularity axiom".to_string()
    }
}

impl ByThmStmt {
    pub fn output_type_string() -> String {
        "proof by theorem".to_string()
    }
}

impl DefThmStmt {
    pub fn output_type_string() -> String {
        "theorem".to_string()
    }
}

impl UseStrategyStmt {
    pub fn output_type_string() -> String {
        "use strategy statement".to_string()
    }
}

impl StopStrategyStmt {
    pub fn output_type_string() -> String {
        "stop strategy statement".to_string()
    }
}

impl DefStrategyStmt {
    pub fn output_type_string() -> String {
        "strategy definition".to_string()
    }
}

impl DefAbstractPropStmt {
    pub fn output_type_string() -> String {
        "abstract predicate interface definition".to_string()
    }
}

impl DefPropStmt {
    pub fn output_type_string() -> String {
        "predicate definition".to_string()
    }
}

impl AliasPropStmt {
    pub fn output_type_string() -> String {
        "predicate alias".to_string()
    }
}

impl AliasThmStmt {
    pub fn output_type_string() -> String {
        "theorem alias".to_string()
    }
}

impl DefLetStmt {
    pub fn output_type_string() -> String {
        "unproved object definition".to_string()
    }
}

impl HaveObjInNonemptySetOrParamTypeStmt {
    pub fn output_type_string() -> String {
        "object definition".to_string()
    }
}

impl HaveObjEqualStmt {
    pub fn output_type_string() -> String {
        "object definition".to_string()
    }
}

impl HaveObjByExistFactsStmt {
    pub fn output_type_string() -> String {
        "object definition by existence".to_string()
    }
}

impl HaveByExistStmt {
    pub fn output_type_string() -> String {
        "object definition by existence".to_string()
    }
}

impl HaveByPreimageStmt {
    pub fn output_type_string() -> String {
        "preimage object definition".to_string()
    }
}

impl HaveFnEqualStmt {
    pub fn output_type_string() -> String {
        "function definition".to_string()
    }
}

impl HaveFnEqualCaseByCaseStmt {
    pub fn output_type_string() -> String {
        "casewise function definition".to_string()
    }
}

impl HaveFnByInducStmt {
    pub fn output_type_string() -> String {
        "recursive function definition".to_string()
    }
}

impl HaveFnByForallExistUniqueStmt {
    pub fn output_type_string() -> String {
        "function definition by unique existence".to_string()
    }
}

impl HaveTupleStmt {
    pub fn output_type_string() -> String {
        "tuple definition".to_string()
    }
}

impl HaveCartStmt {
    pub fn output_type_string() -> String {
        "cart definition".to_string()
    }
}

impl HaveSeqStmt {
    pub fn output_type_string() -> String {
        "sequence definition".to_string()
    }
}

impl HaveFiniteSeqStmt {
    pub fn output_type_string() -> String {
        "finite sequence definition".to_string()
    }
}

impl HaveMatrixStmt {
    pub fn output_type_string() -> String {
        "matrix definition".to_string()
    }
}
