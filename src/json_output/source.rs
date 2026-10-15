use crate::prelude::*;

/// Existing parsed source identity; synthetic facts may have no source line.
pub(super) fn project_statement_source(stmt: &Stmt, runtime: &Runtime) -> JsonValue {
    let Some(source) = statement_source_line(stmt) else {
        return JsonValue::Null;
    };
    super::helper::object_for(
        runtime,
        vec![
            ("path", super::helper::string(source.origin.to_string())),
            ("line", JsonValue::Number(source.line as f64)),
        ],
    )
}

fn statement_source_line(stmt: &Stmt) -> Option<&crate::ast::line_file::SourceLine> {
    match stmt {
        Stmt::Fact(fact) => super::helper::fact_source_line(fact),
        Stmt::Trust(value) => match value {
            crate::ast::stmt::TrustBoundaryStmt::TrustStmt(value) => Some(&value.line_file),
            crate::ast::stmt::TrustBoundaryStmt::TrustHaveStmt(value) => Some(&value.line_file),
        },
        Stmt::Definition(value) => match value {
            crate::ast::stmt::DefinitionStmt::DefineObj(value) => match value {
                crate::ast::stmt::DefineObjStmt::LetObjStmt(value) => Some(&value.line_file),
                crate::ast::stmt::DefineObjStmt::HaveObjInNonemptySetStmt(value) => {
                    Some(&value.line_file)
                }
                crate::ast::stmt::DefineObjStmt::HaveObjEqualStmt(value) => Some(&value.line_file),
                crate::ast::stmt::DefineObjStmt::HaveObjByExistFactsStmt(value) => {
                    Some(&value.line_file)
                }
                crate::ast::stmt::DefineObjStmt::ObtainObjFromExistFact(value) => {
                    Some(&value.line_file)
                }
                crate::ast::stmt::DefineObjStmt::ObtainObjFromAtomicFact(value) => {
                    Some(&value.line_file)
                }
                crate::ast::stmt::DefineObjStmt::HaveByPreimageStmt(value) => {
                    Some(&value.line_file)
                }
                crate::ast::stmt::DefineObjStmt::HaveByReplacementAxiomStmt(value) => {
                    Some(&value.line_file)
                }
            },
            crate::ast::stmt::DefinitionStmt::HaveFnEqualStmt(value) => Some(&value.line_file),
            crate::ast::stmt::DefinitionStmt::HaveFnEqualCaseByCaseStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::DefinitionStmt::HaveFnByInducStmt(value) => Some(&value.line_file),
            crate::ast::stmt::DefinitionStmt::HaveFnByForallExistUniqueStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::DefinitionStmt::DefPropStmt(value) => Some(&value.line_file),
            crate::ast::stmt::DefinitionStmt::DefAbstractPropStmt(value) => Some(&value.line_file),
            crate::ast::stmt::DefinitionStmt::DefTemplateStmt(value) => Some(&value.line_file),
            crate::ast::stmt::DefinitionStmt::DefStructStmt(value) => Some(&value.line_file),
            crate::ast::stmt::DefinitionStmt::DefAlgoByCasesStmt(value) => Some(&value.line_file),
            crate::ast::stmt::DefinitionStmt::DefAlgoByInducStmt(value) => Some(&value.line_file),
            crate::ast::stmt::DefinitionStmt::DefThmStmt(value) => Some(&value.line_file),
            crate::ast::stmt::DefinitionStmt::AxiomStmt(value) => Some(&value.line_file),
            crate::ast::stmt::DefinitionStmt::DefStrategyStmt(value) => Some(&value.line_file),
        },
        Stmt::ReleaseAndExpand(value) => match value {
            crate::ast::stmt::ReleaseAndExpandStmt::ReleaseThmStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ReleaseAndExpandStmt::ReleaseStructDefStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::ReleaseAndExpandStmt::ReleaseObjDefStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::ReleaseAndExpandStmt::ReleaseCartDefStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::ReleaseAndExpandStmt::ReleaseTupleDefStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::ReleaseAndExpandStmt::ExpandRangeStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::ReleaseAndExpandStmt::ReleaseZornLemmaStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::ReleaseAndExpandStmt::ReleaseAxiomOfChoiceStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::ReleaseAndExpandStmt::ReleaseRegularityAxiomStmt(value) => {
                Some(&value.line_file)
            }
        },
        Stmt::By(value) => match value {
            crate::ast::stmt::ByStmt::ByCasesStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ByStmt::ByContraStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ByStmt::ByEnumerateFiniteSetStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ByStmt::ByInducStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ByStmt::ByStrongInducStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ByStmt::ByForStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ByStmt::ByExtensionStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ByStmt::ByFnExtensionStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ByStmt::ByDefStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ByStmt::ByThmStmt(value) => Some(&value.line_file),
        },
        Stmt::Register(value) => match value {
            crate::ast::stmt::RegisterStmt::RegisterTransitivePropStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::RegisterStmt::RegisterSymmetricPropStmt(value) => {
                Some(&value.line_file)
            }
            crate::ast::stmt::RegisterStmt::RegisterReflexivePropStmt(value) => {
                Some(&value.line_file)
            }
        },
        Stmt::Witness(value) => match value {
            crate::ast::stmt::WitnessStmt::WitnessExistFact(value) => Some(&value.line_file),
            crate::ast::stmt::WitnessStmt::WitnessAtomicFact(value) => Some(&value.line_file),
            crate::ast::stmt::WitnessStmt::WitnessNonemptySet(value) => Some(&value.line_file),
        },
        Stmt::ProofBlock(value) => match value {
            crate::ast::stmt::ProofBlockStmt::ClaimStmt(value) => Some(&value.line_file),
            crate::ast::stmt::ProofBlockStmt::SketchStmt(value) => Some(&value.line_file),
        },
        Stmt::Command(value) => match value {
            crate::ast::stmt::CommandStmt::EvalStmt(value) => Some(&value.line_file),
        },
    }
}
