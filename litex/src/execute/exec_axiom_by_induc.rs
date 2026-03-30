use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_by_induc_axiom_stmt(
        &mut self,
        stmt: &ByInducAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        let all_inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for fact in stmt.to_prove.iter() {
            self.push_env();
            let one_fact_infer_result = self.exec_by_induc_axiom_stmt_for_one_fact(stmt, fact);
            self.pop_env();

            match one_fact_infer_result {
                Ok(one_fact_infer_result) => {
                    infer_result.new_infer_result_inside(one_fact_infer_result);
                }
                Err(exec_stmt_error) => {
                    return Err(RuntimeError::ExecStmtError(
                        ExecStmtError::with_message_and_cause(
                            Stmt::ByInducAxiomStmt(stmt.clone()),
                            format!("by_induc: failed to prove `{}`", fact),
                            Some(exec_stmt_error.into()),
                            vec![],
                        ),
                    ));
                }
            }
        }

        let corresponding_forall_fact = stmt.to_corresponding_forall_fact().map_err(|msg| {
            RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                Stmt::ByInducAxiomStmt(stmt.clone()),
                msg,
                None,
                vec![],
            ))
        })?;
        self.store_fact_without_well_defined_verified_and_infer(&corresponding_forall_fact)?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ByInducAxiomStmt(stmt.clone()),
                infer_result,
                all_inside_results,
            ),
        ))
    }
}

impl Runtime {
    fn exec_by_induc_axiom_stmt_for_one_fact(
        &mut self,
        stmt: &ByInducAxiomStmt,
        fact: &ExistOrAndChainAtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();

        let mut base_case_param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        base_case_param_to_arg_map.insert(stmt.param.clone(), stmt.induc_from.clone());
        let base_case_fact = fact
            .clone()
            .instantiate(&base_case_param_to_arg_map)
            .to_fact();
        self.verify_fact_return_err_if_not_true(&base_case_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByInducAxiomStmt(stmt.clone()),
                    format!("by_induc: base case is not proved `{}`", base_case_fact),
                    Some(verify_error.into()),
                    vec![],
                ))
            })?;

        let induc_from_in_z_fact = AtomicFact::InFact(InFact::new(
            stmt.induc_from.clone(),
            Obj::StandardSet(StandardSet::Z),
            stmt.line_file,
        ));
        let verify_induc_from_in_z_result = self
            .verify_atomic_fact(&induc_from_in_z_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByInducAxiomStmt(stmt.clone()),
                    format!("by_induc: failed to verify `{}`", induc_from_in_z_fact),
                    Some(verify_error.into()),
                    vec![],
                ))
            })?;
        if verify_induc_from_in_z_result.is_unknown() {
            return Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    Stmt::ByInducAxiomStmt(stmt.clone()),
                    format!("by_induc: failed to verify `{}`", induc_from_in_z_fact),
                    None,
                    vec![],
                ),
            ));
        }

        let param_as_identifier = Obj::Identifier(Identifier::new(stmt.param.clone()));
        let param_plus_one_obj = Obj::Add(Add::new(
            param_as_identifier.clone(),
            Obj::Number(Number::new("1".to_string())),
        ));
        let mut induction_step_param_to_obj_map: HashMap<String, Obj> = HashMap::new();
        induction_step_param_to_obj_map.insert(stmt.param.clone(), param_plus_one_obj);
        let next_fact_of_induction_step = fact.instantiate(&induction_step_param_to_obj_map);

        let corresponding_forall_fact = Fact::ForallFact(ForallFact::new(
            vec![ParamDefWithParamType(
                vec![stmt.param.clone()],
                ParamType::Obj(Obj::StandardSet(StandardSet::Z)),
            )],
            vec![
                ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::GreaterEqualFact(
                    GreaterEqualFact::new(
                        param_as_identifier,
                        stmt.induc_from.clone(),
                        stmt.line_file,
                    ),
                )),
                fact.clone(),
            ],
            vec![next_fact_of_induction_step],
            stmt.line_file,
        ));

        self.verify_fact_return_err_if_not_true(
            &corresponding_forall_fact,
            &VerifyState::new(0, false),
        )
        .map_err(|well_defined_error| {
            RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                Stmt::ByInducAxiomStmt(stmt.clone()),
                format!(
                    "by_induc: generated step forall is not well-defined `{}`",
                    corresponding_forall_fact
                ),
                Some(well_defined_error.into()),
                vec![],
            ))
        })?;

        infer_result.new_fact(&corresponding_forall_fact);
        Ok(infer_result)
    }
}
