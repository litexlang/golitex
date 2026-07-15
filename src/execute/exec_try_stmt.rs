use crate::prelude::*;

impl Runtime {
    pub fn exec_try_stmt(&mut self, stmt: &TryStmt) -> Result<StmtResult, RuntimeError> {
        if let Some((control_stmt, control_name)) = first_disallowed_control_stmt_in_try(stmt) {
            return Err(try_control_stmt_error(control_stmt, control_name));
        }

        let committed_results =
            self.run_in_local_env_and_commit(|rt| rt.exec_try_proof_steps(stmt))?;

        Ok(
            NonFactualStmtSuccess::new(stmt.clone().into(), InferResult::new(), committed_results)
                .into(),
        )
    }

    fn exec_try_proof_steps(&mut self, stmt: &TryStmt) -> Result<Vec<StmtResult>, RuntimeError> {
        let mut results = Vec::new();
        let proof_len = stmt.proof.len();
        for (proof_index, proof_stmt) in stmt.proof.iter().enumerate() {
            match self.exec_stmt(proof_stmt) {
                Ok(result) => {
                    if result.is_unknown() {
                        return Err(UnknownRuntimeError(RuntimeErrorStruct::new_with_output(
                            Some(proof_stmt.clone()),
                            "try failed: proof step is unknown".to_string(),
                            proof_stmt.line_file(),
                            None,
                            vec![],
                            RuntimeErrorOutput::proof_step_unknown(
                                proof_stmt.clone(),
                                proof_index + 1,
                                proof_len,
                                &result,
                            ),
                        ))
                        .into());
                    }
                    results.push(result);
                }
                Err(statement_error) => {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        proof_stmt.to_string(),
                        Some(statement_error),
                        vec![],
                    ));
                }
            }
        }
        Ok(results)
    }
}

fn first_disallowed_control_stmt_in_try(stmt: &TryStmt) -> Option<(Stmt, &'static str)> {
    first_disallowed_control_stmt_in_stmts(&stmt.proof)
}

fn first_disallowed_control_stmt_in_stmts(stmts: &[Stmt]) -> Option<(Stmt, &'static str)> {
    for stmt in stmts {
        if let Some(found) = first_disallowed_control_stmt(stmt) {
            return Some(found);
        }
    }
    None
}

fn first_disallowed_control_stmt(stmt: &Stmt) -> Option<(Stmt, &'static str)> {
    if let Some(control_name) = disallowed_control_stmt_name(stmt) {
        return Some((stmt.clone(), control_name));
    }

    match stmt {
        Stmt::DefObjStmt(DefObjStmt::HaveFnByForallExistUniqueStmt(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.prove_process)
        }
        Stmt::DefInterfaceStmt(DefInterfaceStmt::DefTemplateStmt(s)) => {
            first_disallowed_control_stmt_in_template_def(&s.template_def_stmt)
        }
        Stmt::DefThmStmt(s) => first_disallowed_control_stmt_in_stmts(&s.prove_process),
        Stmt::DefStrategyStmt(s) => first_disallowed_control_stmt_in_stmts(&s.prove_process),
        Stmt::By(ByStmt::ByCasesStmt(s)) => {
            for proof in s.proofs.iter() {
                if let Some(found) = first_disallowed_control_stmt_in_stmts(proof) {
                    return Some(found);
                }
            }
            None
        }
        Stmt::By(ByStmt::ByContraStmt(s)) => first_disallowed_control_stmt_in_stmts(&s.proof),
        Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        Stmt::By(ByStmt::ByFiniteSetInducStmt(s)) => {
            if let Some(found) = first_disallowed_control_stmt_in_stmts(&s.base_proof) {
                return Some(found);
            }
            first_disallowed_control_stmt_in_stmts(&s.step_proof)
        }
        Stmt::By(ByStmt::ByInducStmt(s)) => {
            if let Some(found) = first_disallowed_control_stmt_in_stmts(&s.proof) {
                return Some(found);
            }
            if let Some(base_proof) = s.base_proof.as_ref() {
                if let Some(found) = first_disallowed_control_stmt_in_stmts(base_proof) {
                    return Some(found);
                }
            }
            if let Some(step_proof) = s.step_proof.as_ref() {
                if let Some(found) = first_disallowed_control_stmt_in_stmts(step_proof) {
                    return Some(found);
                }
            }
            None
        }
        Stmt::By(ByStmt::ByForStmt(s)) => first_disallowed_control_stmt_in_stmts(&s.proof),
        Stmt::By(ByStmt::ByExtensionStmt(s)) => first_disallowed_control_stmt_in_stmts(&s.proof),
        Stmt::By(ByStmt::ByTransitivePropStmt(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        Stmt::By(ByStmt::BySymmetricPropStmt(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        Stmt::By(ByStmt::ByReflexivePropStmt(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        Stmt::By(ByStmt::ByAntisymmetricPropStmt(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        Stmt::By(ByStmt::ByZornLemmaStmt(s)) => first_disallowed_control_stmt_in_stmts(&s.proof),
        Stmt::By(ByStmt::ByAxiomOfChoiceStmt(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        Stmt::By(ByStmt::ByRegularityAxiomStmt(_)) => None,
        Stmt::Witness(WitnessStmt::WitnessExistFact(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        Stmt::Witness(WitnessStmt::WitnessNonemptySet(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        Stmt::ProofBlock(ProofBlockStmt::SketchStmt(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        Stmt::ProofBlock(ProofBlockStmt::TryStmt(s)) => {
            first_disallowed_control_stmt_in_stmts(&s.proof)
        }
        _ => None,
    }
}

fn first_disallowed_control_stmt_in_template_def(
    template_def: &TemplateDefEnum,
) -> Option<(Stmt, &'static str)> {
    match template_def {
        TemplateDefEnum::HaveFnByForallExistUniqueStmt(s) => {
            first_disallowed_control_stmt_in_stmts(&s.prove_process)
        }
        _ => None,
    }
}

fn disallowed_control_stmt_name(stmt: &Stmt) -> Option<&'static str> {
    match stmt {
        Stmt::Command(CommandStmt::ClearStmt(_)) => Some("clear"),
        Stmt::Command(CommandStmt::ImportStmt(_)) => Some("import"),
        Stmt::Command(CommandStmt::TrustImportStmt(_)) => Some("trust import"),
        Stmt::Command(CommandStmt::LocalImportStmt(_)) => Some("local import"),
        Stmt::Command(CommandStmt::TrustLocalImportStmt(_)) => Some("trust local import"),
        _ => None,
    }
}

fn try_control_stmt_error(control_stmt: Stmt, control_name: &str) -> RuntimeError {
    RuntimeError::ExecStmtError(RuntimeErrorStruct::new(
        Some(control_stmt.clone()),
        format!(
            "try cannot contain control statement `{}` because try commits by merging a child environment; run it outside try",
            control_name
        ),
        control_stmt.line_file(),
        None,
        vec![],
    ))
}
