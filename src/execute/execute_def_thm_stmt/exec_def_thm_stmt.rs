use crate::ast::fact::{Fact, ForallFact};
use crate::ast::stmt::{
    ByStmt, ClaimStmt, DefThmStmt, DefineObjStmt, DefinitionStmt, ProofBlockStmt, SketchStmt, Stmt,
};
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ExecStmtResult;
use crate::execute::execute_by_stmt::{
    proof_verify_state, store_goal_fact, verify_goal_fact,
};
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::execute::execute_proof_block_stmt::{
    run_proof_body_stmts, ProofBlockBodyFailed,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

// `local_env`: FactId/WdId resolution table for the theorem proof scope (same
// role as documented in execute_by_stmt/result.rs).

pub enum ExecDefThmStmtResult {
    Success(ExecDefThmStmtSuccess),
    Failed(ExecDefThmStmtFailed),
}

pub struct ExecDefThmStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub proof_steps: Vec<ExecStmtResult>,
    pub conclusion_proofs: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecDefThmStmtFailed {
    NameClash(String),
    GoalWd(VerifyFactWellDefinedResult),
    Introduce(String),
    ProofBody(ProofBlockBodyFailed),
    Conclusion {
        index: usize,
        result: VerifyFactResult,
    },
    Store(String),
}

impl ExecDefThmStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub fn exec_def_thm_stmt(
    runtime: &mut Runtime,
    stmt: &DefThmStmt,
) -> RuntimeResult<ExecDefThmStmtResult> {
    if runtime.def_thm_visible_in_stack(&stmt.name).is_some()
        || runtime.axiom_visible_in_stack(&stmt.name).is_some()
        || runtime.def_strategy_visible_in_stack(&stmt.name).is_some()
    {
        return Ok(ExecDefThmStmtResult::Failed(ExecDefThmStmtFailed::NameClash(
            format!("thm `{}` is already defined", stmt.name),
        )));
    }

    let goal_wd =
        runtime.verify_fact_well_definedness(&stmt.fact, proof_verify_state())?;
    if goal_wd.is_failed() {
        runtime.release_obtain_parse_bindings_in_stmts(&stmt.prove_process);
        return Ok(ExecDefThmStmtResult::Failed(ExecDefThmStmtFailed::GoalWd(
            goal_wd,
        )));
    }

    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        match &stmt.fact {
            Fact::ForallFact(forall) => {
                exec_def_thm_forall_body(rt, forall, &stmt.prove_process)
            }
            _ => {
                let proof_steps = match run_proof_body_stmts(rt, &stmt.prove_process)? {
                    Ok(steps) => steps,
                    Err(failed) => return Ok(Err(ExecDefThmStmtFailed::ProofBody(failed))),
                };
                let proof = verify_goal_fact(rt, &stmt.fact)?;
                if proof.is_failed() {
                    return Ok(Err(ExecDefThmStmtFailed::Conclusion {
                        index: 0,
                        result: proof,
                    }));
                }
                Ok(Ok((proof_steps, vec![proof])))
            }
        }
    })?;

    runtime.release_obtain_parse_bindings_in_stmts(&stmt.prove_process);

    let (proof_steps, conclusion_proofs) = match local_outcome {
        Ok(v) => v,
        Err(failed) => return Ok(ExecDefThmStmtResult::Failed(failed)),
    };

    runtime.top_exec_env_mut().store_def_thm(stmt.clone());

    let stored = match store_goal_fact(runtime, &stmt.fact)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecDefThmStmtResult::Failed(ExecDefThmStmtFailed::Store(
                msg,
            )));
        }
    };

    Ok(ExecDefThmStmtResult::Success(ExecDefThmStmtSuccess {
        goal_wd,
        proof_steps,
        conclusion_proofs,
        local_env,
        stored,
    }))
}

fn exec_def_thm_forall_body(
    runtime: &mut Runtime,
    forall: &ForallFact,
    proof: &[Stmt],
) -> RuntimeResult<Result<(Vec<ExecStmtResult>, Vec<VerifyFactResult>), ExecDefThmStmtFailed>>
{
    if runtime
        .introduce_typed_parameters(&forall.typed_parameters, proof_verify_state())?
        .is_err()
    {
        return Ok(Err(ExecDefThmStmtFailed::Introduce(
            "thm: failed to introduce forall parameters".to_string(),
        )));
    }

    for dom in &forall.dom_facts {
        let wd = runtime.verify_fact_well_definedness(dom, proof_verify_state())?;
        if wd.is_failed() {
            return Ok(Err(ExecDefThmStmtFailed::Introduce(
                "thm: forall domain fact is not well-defined".to_string(),
            )));
        }
        let _ = runtime.store_fact_and_infer(dom)?;
    }

    let proof_steps = match run_proof_body_stmts(runtime, proof)? {
        Ok(steps) => steps,
        Err(failed) => return Ok(Err(ExecDefThmStmtFailed::ProofBody(failed))),
    };

    let mut conclusion_proofs = Vec::with_capacity(forall.then_facts.len());
    for (index, then) in forall.then_facts.iter().enumerate() {
        let then_fact: Fact = then.clone().into();
        let proof = verify_goal_fact(runtime, &then_fact)?;
        if proof.is_failed() {
            return Ok(Err(ExecDefThmStmtFailed::Conclusion { index, result: proof }));
        }
        conclusion_proofs.push(proof);
    }

    Ok(Ok((proof_steps, conclusion_proofs)))
}

impl Runtime {
    // Nested obtain binds witnesses at file-root parse scope so ids survive
    // temporary forall/by scopes; drop them after the enclosing proof finishes.
    pub(crate) fn release_obtain_parse_bindings_in_stmts(&mut self, stmts: &[Stmt]) {
        for name in collect_obtain_equal_tos(stmts) {
            self.remove_plain_atom_from_file_root_scope(&name);
        }
    }
}

fn collect_obtain_equal_tos(stmts: &[Stmt]) -> Vec<String> {
    let mut out = Vec::new();
    for stmt in stmts {
        collect_obtain_equal_tos_in_stmt(stmt, &mut out);
    }
    out
}

fn collect_obtain_equal_tos_in_stmt(stmt: &Stmt, out: &mut Vec<String>) {
    match stmt {
        Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::ObtainObjFromExistFact(s))) => {
            out.extend(s.equal_tos.iter().cloned());
        }
        Stmt::Definition(DefinitionStmt::DefineObj(DefineObjStmt::ObtainObjFromAtomicFact(s))) => {
            out.extend(s.equal_tos.iter().cloned());
        }
        Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(ClaimStmt { proof, .. })) => {
            for child in proof {
                collect_obtain_equal_tos_in_stmt(child, out);
            }
        }
        Stmt::ProofBlock(ProofBlockStmt::SketchStmt(SketchStmt { proof, .. })) => {
            for child in proof {
                collect_obtain_equal_tos_in_stmt(child, out);
            }
        }
        Stmt::By(ByStmt::ByContraStmt(s)) => {
            for child in &s.proof {
                collect_obtain_equal_tos_in_stmt(child, out);
            }
        }
        Stmt::By(ByStmt::ByCasesStmt(s)) => {
            for proof in &s.proofs {
                for child in proof {
                    collect_obtain_equal_tos_in_stmt(child, out);
                }
            }
        }
        Stmt::By(ByStmt::ByInducStmt(s)) => {
            for child in &s.proof {
                collect_obtain_equal_tos_in_stmt(child, out);
            }
            if let Some(base) = &s.base_proof {
                for child in base {
                    collect_obtain_equal_tos_in_stmt(child, out);
                }
            }
            if let Some(step) = &s.step_proof {
                for child in step {
                    collect_obtain_equal_tos_in_stmt(child, out);
                }
            }
        }
        Stmt::By(ByStmt::ByStrongInducStmt(s)) => {
            for child in &s.proof {
                collect_obtain_equal_tos_in_stmt(child, out);
            }
            if let Some(base) = &s.base_proof {
                for child in base {
                    collect_obtain_equal_tos_in_stmt(child, out);
                }
            }
            if let Some(step) = &s.step_proof {
                for child in step {
                    collect_obtain_equal_tos_in_stmt(child, out);
                }
            }
        }
        Stmt::By(ByStmt::ByEnumerateFiniteSetStmt(s)) => {
            for child in &s.proof {
                collect_obtain_equal_tos_in_stmt(child, out);
            }
        }
        Stmt::By(ByStmt::ByForStmt(s)) => {
            for child in &s.proof {
                collect_obtain_equal_tos_in_stmt(child, out);
            }
        }
        Stmt::By(ByStmt::ByExtensionStmt(s)) => {
            for child in &s.proof {
                collect_obtain_equal_tos_in_stmt(child, out);
            }
        }
        Stmt::By(ByStmt::ByFnExtensionStmt(s)) => {
            for child in &s.proof {
                collect_obtain_equal_tos_in_stmt(child, out);
            }
        }
        Stmt::By(ByStmt::ByDefStmt(_)) | Stmt::By(ByStmt::ByThmStmt(_)) => {}
        Stmt::Fact(_)
        | Stmt::Trust(_)
        | Stmt::Definition(_)
        | Stmt::ReleaseAndExpand(_)
        | Stmt::Register(_)
        | Stmt::Witness(_)
        | Stmt::Command(_) => {}
    }
}
