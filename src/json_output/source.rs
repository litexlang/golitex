use crate::ast::SourceLine;
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

pub(crate) fn statement_source_line(stmt: &Stmt) -> Option<&crate::ast::line_file::SourceLine> {
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

/// Location of the checked proposition, following the failed child of a quantifier.
pub(super) fn failed_verification_line(result: &VerifyFactResult) -> Option<SourceLine> {
    use crate::execute::execute_fact_stmt::verify_forall_fact::*;
    if let VerifyFactResult::ForallFact(result) = result {
        match result.as_ref() {
            VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToSearchProof {
                failed_then,
                ..
            }) => {
                if let Some(line) = failed_verification_line(failed_then) {
                    return Some(line);
                }
            }
            VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToVerifyWellDefined(
                reason,
            )) => {
                if let Some(line) = failed_forall_wd_line(reason) {
                    return Some(line);
                }
            }
            VerifyForallFactResult::Success(_) => {}
        }
    }
    match result {
        VerifyFactResult::AndFact(result) => {
            use crate::execute::execute_fact_stmt::verify_and_fact::*;
            if let VerifyAndFactResult::Failed(
                VerifyAndFactFailed::FailToSearchProof {
                    failed_component, ..
                }
                | VerifyAndFactFailed::FailToVerifyWellDefined {
                    failed_component, ..
                },
            ) = result.as_ref()
            {
                return failed_verification_line(failed_component);
            }
        }
        VerifyFactResult::ChainFact(result) => {
            use crate::execute::execute_fact_stmt::verify_chain_fact::*;
            if let VerifyChainFactResult::Failed(
                VerifyChainFactFailed::FailToSearchProof {
                    failed_adjacent, ..
                }
                | VerifyChainFactFailed::FailToVerifyWellDefined {
                    failed_adjacent, ..
                },
            ) = result.as_ref()
            {
                return failed_verification_line(failed_adjacent);
            }
        }
        VerifyFactResult::ForallFactWithIff(result) => {
            use crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::*;
            match result.as_ref() {
                VerifyForallFactWithIffResult::Failed(
                    VerifyForallFactWithIffFailed::FailThenImpliesIff {
                        then_implies_iff, ..
                    },
                ) => return failed_verification_line(then_implies_iff),
                VerifyForallFactWithIffResult::Failed(
                    VerifyForallFactWithIffFailed::FailIffImpliesThen {
                        iff_implies_then, ..
                    },
                ) => return failed_verification_line(iff_implies_then),
                _ => {}
            }
        }
        _ => {}
    }
    super::helper::fact_source_line(&super::project_normal::verify_goal_fact(result)).cloned()
}

pub(super) fn failed_fact_wd_line(
    result: &FailToVerifyFactWellDefinedResult,
) -> Option<SourceLine> {
    if let FailToVerifyFactWellDefinedResult::ForallFact(reason) = result {
        if let Some(line) = failed_forall_wd_line(reason) {
            return Some(line);
        }
    }
    super::helper::fact_source_line(&result.fact()).cloned()
}

fn failed_forall_wd_line(
    reason: &crate::execute::execute_fact_stmt::verify_forall_fact::FailToVerifyForallFactWellDefinedResult,
) -> Option<SourceLine> {
    use crate::execute::execute_fact_stmt::verify_forall_fact::*;
    match reason {
        FailToVerifyForallFactWellDefinedResult::LocalIntroduction(local) => match &local.failure {
            ForallIntroductionFormationFailed::Premise { failed_dom, .. } => {
                failed_fact_wd_line(failed_dom)
            }
            ForallIntroductionFormationFailed::Parameters(_) => None,
        },
        FailToVerifyForallFactWellDefinedResult::LocalWellDefinedness(local) => {
            match &local.failure {
                ForallWellDefinedLocalFailed::Premise { failed_dom, .. } => {
                    failed_fact_wd_line(failed_dom)
                }
                ForallWellDefinedLocalFailed::Conclusion { failed_then, .. } => {
                    failed_fact_wd_line(failed_then)
                }
                ForallWellDefinedLocalFailed::Parameters(_)
                | ForallWellDefinedLocalFailed::AutoOpen { .. } => None,
            }
        }
        FailToVerifyForallFactWellDefinedResult::DomFact { failed_dom, .. } => {
            failed_fact_wd_line(failed_dom)
        }
        FailToVerifyForallFactWellDefinedResult::ThenFact { failed_then, .. } => {
            failed_fact_wd_line(failed_then)
        }
        FailToVerifyForallFactWellDefinedResult::ParamType { .. }
        | FailToVerifyForallFactWellDefinedResult::AutoOpenStructLayer { .. } => None,
    }
}

pub(super) fn failed_statement_line(result: &ExecStmtResult) -> Option<SourceLine> {
    use crate::execute::execute_by_stmt::*;
    use crate::execute::execute_def_thm_stmt::*;
    use crate::execute::execute_proof_block_stmt::*;
    use crate::execute::execute_witness_stmt::*;
    let body_line = |failed: &ProofBlockBodyFailed| {
        failed_statement_line(&failed.result)
            .or_else(|| statement_source_line(&failed.statement).cloned())
    };
    match result {
        ExecStmtResult::Fact(ExecFactStmtResult::Failed(result)) => {
            failed_verification_line(result)
        }
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(
            ExecClaimStmtResult::Failed(failed),
        )) => match failed {
            ExecClaimStmtFailed::GoalWd(VerifyFactWellDefinedResult::Failed(reason)) => {
                failed_fact_wd_line(reason)
            }
            ExecClaimStmtFailed::Local(failure) => match &failure.body {
                ExecClaimBodyFailed::NonForall(ExecClaimNonForallFailed::ProofBody(body)) => {
                    body_line(body)
                }
                ExecClaimBodyFailed::NonForall(ExecClaimNonForallFailed::Conclusion {
                    result,
                    ..
                }) => failed_verification_line(result),
                ExecClaimBodyFailed::Forall(ExecClaimForallFailed::Entered { failure, .. }) => {
                    match failure {
                        ExecClaimForallEnteredFailed::ProofBody(body) => body_line(body),
                        ExecClaimForallEnteredFailed::Conclusion { result, .. } => {
                            failed_verification_line(result)
                        }
                        ExecClaimForallEnteredFailed::PremiseWd {
                            result: VerifyFactWellDefinedResult::Failed(reason),
                            ..
                        } => failed_fact_wd_line(reason),
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        },
        ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Sketch(
            ExecSketchStmtResult::Failed(ExecSketchStmtFailed::ProofBody(body)),
        )) => body_line(body),
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Failed(failed),
        )) => match failed {
            ExecDefThmStmtFailed::GoalWd(VerifyFactWellDefinedResult::Failed(reason)) => {
                failed_fact_wd_line(reason)
            }
            ExecDefThmStmtFailed::Local(failure) => match &failure.body {
                ExecDefThmBodyFailed::NonForall(ExecDefThmNonForallFailed::ProofBody(body)) => {
                    body_line(body)
                }
                ExecDefThmBodyFailed::NonForall(ExecDefThmNonForallFailed::Conclusion {
                    result,
                    ..
                }) => failed_verification_line(result),
                ExecDefThmBodyFailed::Forall(ExecDefThmForallFailed::Entered {
                    failure, ..
                }) => match failure {
                    ExecDefThmForallEnteredFailed::ProofBody(body) => body_line(body),
                    ExecDefThmForallEnteredFailed::Conclusion { result, .. } => {
                        failed_verification_line(result)
                    }
                    ExecDefThmForallEnteredFailed::PremiseWd {
                        result: VerifyFactWellDefinedResult::Failed(reason),
                        ..
                    } => failed_fact_wd_line(reason),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        },
        ExecStmtResult::By(ExecByStmtResult::Cases(ExecByCasesStmtResult::Failed(
            ExecByCasesStmtFailed::Branch {
                failed: ByCasesBranchFailed::AfterAssumption(failed),
                ..
            },
        ))) => match &failed.failure {
            ByCasesEnteredBranchFailed::ProofBody(body) => body_line(body),
            ByCasesEnteredBranchFailed::ClosingThen { result, .. } => {
                failed_verification_line(result)
            }
            ByCasesEnteredBranchFailed::ClosingImpossible { failed, .. } => {
                failed_contradiction_line(failed)
            }
        },
        ExecStmtResult::By(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
            ExecByContraStmtFailed::Local(failed),
        ))) => match &failed.failure {
            ExecByContraEnteredFailed::ProofBody { failure, .. } => body_line(failure),
            ExecByContraEnteredFailed::Closing { failure, .. } => {
                failed_contradiction_line(failure)
            }
            ExecByContraEnteredFailed::AssumptionWd(_) => None,
        },
        ExecStmtResult::Witness(ExecWitnessStmtResult::WitnessExistFact(
            ExecWitnessExistFactStmtResult::Failed(failed),
        )) => match failed {
            ExecWitnessExistFactStmtFailed::ProofBody(body) => body_line(body),
            ExecWitnessExistFactStmtFailed::WitnessType(proof)
            | ExecWitnessExistFactStmtFailed::BodyCheck(proof)
            | ExecWitnessExistFactStmtFailed::Uniqueness(proof) => failed_verification_line(proof),
            ExecWitnessExistFactStmtFailed::ExistFactWellDefined(failure) => {
                failed_fact_wd_line(failure)
            }
            _ => None,
        },
        _ => None,
    }
}

fn failed_contradiction_line(
    failure: &crate::execute::execute_by_stmt::ByContradictionClosingFailed,
) -> Option<SourceLine> {
    use crate::execute::execute_by_stmt::ByContradictionClosingFailed;
    match failure {
        ByContradictionClosingFailed::Impossible(proof)
        | ByContradictionClosingFailed::NegatedImpossible(proof) => failed_verification_line(proof),
        _ => None,
    }
}
