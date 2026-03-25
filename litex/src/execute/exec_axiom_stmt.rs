use super::Runtime;
use crate::common::helper::is_number_string_literally_integer_without_dot;
use crate::error::{ExecStmtError, RuntimeError, UnknownError};
use crate::fact::{
    AtomicFact, EqualFact, ExistOrAndChainAtomicFact, Fact, ForallFact, GreaterEqualFact, InFact,
    OrFact,
};
use crate::infer::InferResult;
use crate::obj::{Add, Identifier, Number, Obj, ZObj};
use crate::result::{NonErrStmtExecResult, NonFactualStmtSuccess};
use crate::stmt::Stmt;
use crate::stmt::axiom_stmt::{
    ByCartDefAxiomStmt, ByCasesAxiomStmt, ByContraAxiomStmt, ByExtensionAxiomStmt,
    ByFnDefAxiomStmt, ByInducAxiomStmt, EnumerateAxiomStmt, ForAxiomStmt,
};
use crate::stmt::parameter_def::{ParamDefWithParamType, ParamType};
use crate::verify::VerifyState;
use std::collections::HashMap;

impl<'a> Runtime<'a> {
    pub fn exec_by_cases_axiom_stmt(
        &mut self,
        stmt: &ByCasesAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        // 证明 well-defined
        for fact in stmt.then_facts.iter() {
            self.verify_fact_well_defined(fact, &VerifyState::new(0, false))
                .map_err(|e| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    format!("by_cases: failed to prove `{}`", fact),
                        Some(e.into()),
                        vec![],
                    ))
                })?;
        }

        self.exec_by_cases_axiom_stmt_verify_cases_cover_all_situations(stmt)
            .map_err(RuntimeError::from)?;

        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for case_index in 0..stmt.cases.len() {
            self.runtime_context.push_env();
            let one_case_result = self.exec_by_cases_axiom_stmt_for_one_case(stmt, case_index);
            self.runtime_context.pop_env();

            match one_case_result {
                Ok(mut one_case_inside_results) => {
                    inside_results.append(&mut one_case_inside_results);
                }
                Err(exec_stmt_error) => {
                    return Err(RuntimeError::ExecStmtError(exec_stmt_error));
                }
            }
        }

        let mut infer_result = InferResult::new();
        for then_fact in stmt.then_facts.iter() {
            let one_then_fact_infer_result = self
                .store_fact_without_well_defined_verified_and_infer(then_fact)
                .map_err(|store_fact_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    format!("by_cases: failed to release `{}`", then_fact),
                        Some(store_fact_error.into()),
                        vec![],
                    ))
                })?;
            infer_result.new_infer_result_inside(one_then_fact_infer_result);
        }

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ByCasesAxiomStmt(stmt.clone()),
                infer_result,
                inside_results,
            ),
        ))
    }

    pub fn exec_by_contra_axiom_stmt(
        &mut self,
        stmt: &ByContraAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let to_prove_fact = Fact::AtomicFact(stmt.to_prove.clone());
        self.verify_fact_well_defined(&to_prove_fact, &VerifyState::new(0, false))
            .map_err(|e| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByContraAxiomStmt(stmt.clone()),
                    format!("by_contra: failed to prove `{}`", to_prove_fact),
                    Some(e.into()),
                    vec![],
                ))
            })?;

        let mut last_error: Option<RuntimeError> = None;
        let exec_proof_inside_results = {
            let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();

            self.runtime_context.push_env();

            // know reverse of to_prove
            let reverse_to_prove_fact = stmt.to_prove.make_reversed();
            self.store_atomic_fact_without_well_defined_verified_and_infer(&reverse_to_prove_fact)
                .map_err(|store_fact_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByContraAxiomStmt(stmt.clone()),
                    format!("by_contra: failed to know reverse of `{}`", to_prove_fact),
                        Some(store_fact_error.into()),
                        vec![],
                    ))
                })?;

            for proof_stmt in stmt.proof.iter() {
                let exec_stmt_result = self.exec_stmt(proof_stmt);
                match exec_stmt_result {
                    Ok(result) => inside_results.push(result),
                    Err(statement_error) => {
                        last_error = Some(statement_error);
                        break;
                    }
                }
            }

            // 这里要证明 impossible 的 正面和反面都是对的
            let verify_impossible_fact_result =
                self.verify_atomic_fact(&stmt.impossible_fact, &VerifyState::new(0, false))?;
            if verify_impossible_fact_result.is_unknown() {
                return Err(RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByContraAxiomStmt(stmt.clone()),
                    impossible_proof_error_message(&stmt.impossible_fact, None),
                    None,
                    inside_results,
                )));
            }

            let verify_reversed_impossible_fact_result = self.verify_atomic_fact(
                &stmt.impossible_fact.make_reversed(),
                &VerifyState::new(0, false),
            )?;
            if verify_reversed_impossible_fact_result.is_unknown() {
                return Err(RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByContraAxiomStmt(stmt.clone()),
                    impossible_proof_error_message(&stmt.impossible_fact, None),
                    None,
                    vec![],
                )));
            }

            self.runtime_context.pop_env();
            inside_results
        };

        if let Some(last_error) = last_error {
            return Err(RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByContraAxiomStmt(stmt.clone()),
                    "by_contra: failed to execute proof".to_string(),
                Some(last_error),
                exec_proof_inside_results,
            )));
        }

        let infer_result = self
            .store_fact_without_well_defined_verified_and_infer(&to_prove_fact)
            .map_err(|store_fact_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByContraAxiomStmt(stmt.clone()),
                    format!("by_contra: failed to release `{}`", to_prove_fact),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ByContraAxiomStmt(stmt.clone()),
                infer_result,
                exec_proof_inside_results,
            ),
        ))
    }

    pub fn exec_enumerate_axiom_stmt(
        &mut self,
        stmt: &EnumerateAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let corresponding_forall_fact = stmt.to_corresponding_forall_fact().map_err(|msg| {
            RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::EnumerateAxiomStmt(stmt.clone()),
                    msg,
                None,
                vec![],
            ))
        })?;

        self.verify_fact_well_defined(&corresponding_forall_fact, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::EnumerateAxiomStmt(stmt.clone()),
                    format!(
                        "enumerate: corresponding forall `{}` is not well-defined",
                        corresponding_forall_fact
                    ),
                    Some(well_defined_error.into()),
                    vec![],
                ))
            })?;

        let enumerate_cartesian_product_is_empty = stmt
            .param_sets
            .iter()
            .any(|list_set_obj| list_set_obj.list.is_empty());

        if enumerate_cartesian_product_is_empty {
            let mut infer_result = InferResult::new();
            infer_result.new_fact(&corresponding_forall_fact);
            let infer_result_from_stored_forall_fact = self
                .store_fact_without_well_defined_verified_and_infer(&corresponding_forall_fact)
                .map_err(|store_fact_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::EnumerateAxiomStmt(stmt.clone()),
                    format!(
                            "enumerate: failed to store corresponding forall `{}`",
                            corresponding_forall_fact
                        ),
                        Some(store_fact_error.into()),
                        vec![],
                    ))
                })?;
            return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                NonFactualStmtSuccess::new(
                    Stmt::EnumerateAxiomStmt(stmt.clone()),
                    infer_result_from_stored_forall_fact,
                    vec![],
                ),
            ));
        }

        let mut all_inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        let mut current_parameter_index_assignment = Self::enumerate_start_index_assignment(stmt);
        loop {
            let mut one_assignment_inside_results = self
                .exec_enumerate_axiom_stmt_for_one_assignment(
                    stmt,
                    &current_parameter_index_assignment,
                )?;
            all_inside_results.append(&mut one_assignment_inside_results);
            let next_parameter_index_assignment =
                Self::enumerate_next_index_assignment(stmt, &current_parameter_index_assignment);
            match next_parameter_index_assignment {
                Some(next_parameter_index_assignment) => {
                    current_parameter_index_assignment = next_parameter_index_assignment;
                }
                None => break,
            }
        }

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&corresponding_forall_fact);

        let infer_result_from_stored_forall_fact = self
            .store_fact_without_well_defined_verified_and_infer(&corresponding_forall_fact)
            .map_err(|store_fact_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::EnumerateAxiomStmt(stmt.clone()),
                    format!(
                        "enumerate: failed to store corresponding forall `{}`",
                        corresponding_forall_fact
                    ),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;
        infer_result.new_infer_result_inside(infer_result_from_stored_forall_fact);

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::EnumerateAxiomStmt(stmt.clone()),
                infer_result,
                all_inside_results,
            ),
        ))
    }

    pub fn exec_by_induc_axiom_stmt(
        &mut self,
        stmt: &ByInducAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        let all_inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for fact in stmt.to_prove.iter() {
            self.runtime_context.push_env();
            let one_fact_infer_result = self.exec_by_induc_axiom_stmt_for_one_fact(stmt, fact);
            self.runtime_context.pop_env();

            match one_fact_infer_result {
                Ok(one_fact_infer_result) => {
                    infer_result.new_infer_result_inside(one_fact_infer_result);
                }
                Err(exec_stmt_error) => {
                    return Err(RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByInducAxiomStmt(stmt.clone()),
                    format!("by_induc: failed to prove `{}`", fact),
                        Some(exec_stmt_error.into()),
                        vec![],
                    )));
                }
            }
        }

        // store 对应的forall
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
            Obj::ZObj(ZObj::new()),
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
            return Err(RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByInducAxiomStmt(stmt.clone()),
                    format!("by_induc: failed to verify `{}`", induc_from_in_z_fact),
                None,
                vec![],
            )));
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
                ParamType::Obj(Obj::ZObj(ZObj::new())),
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

    pub fn exec_for_axiom_stmt(
        &mut self,
        stmt: &ForAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        if stmt.params.len() != stmt.param_sets.len() {
            return Err(RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    "for: number of params does not match number of ranges".to_string(),
                None,
                vec![],
            )));
        }

        let corresponding_forall_fact = stmt.to_corresponding_forall_fact().map_err(|msg| {
            RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    msg,
                None,
                vec![],
            ))
        })?;
        self.verify_fact_well_defined(&corresponding_forall_fact, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    format!(
                        "for: corresponding forall `{}` is not well-defined",
                        corresponding_forall_fact
                    ),
                    Some(well_defined_error.into()),
                    vec![],
                ))
            })?;

        let param_value_strings_of_each_param = Self::for_param_value_strings_of_each_param(stmt)
            .map_err(|msg| {
            RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    msg,
                None,
                vec![],
            ))
        })?;
        let for_cartesian_product_is_empty = param_value_strings_of_each_param
            .iter()
            .any(|one_param_value_strings| one_param_value_strings.is_empty());
        if for_cartesian_product_is_empty {
            let infer_result_from_stored_forall_fact = self
                .store_fact_without_well_defined_verified_and_infer(&corresponding_forall_fact)
                .map_err(|store_fact_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    format!(
                            "for: failed to store corresponding forall `{}`",
                            corresponding_forall_fact
                        ),
                        Some(store_fact_error.into()),
                        vec![],
                    ))
                })?;
            return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                NonFactualStmtSuccess::new(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    infer_result_from_stored_forall_fact,
                    vec![],
                ),
            ));
        }

        let mut all_inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        let mut current_parameter_index_assignment = Self::for_start_index_assignment(stmt);
        loop {
            let mut one_assignment_inside_results = self.exec_for_axiom_stmt_for_one_assignment(
                stmt,
                &current_parameter_index_assignment,
                &param_value_strings_of_each_param,
            )?;
            all_inside_results.append(&mut one_assignment_inside_results);
            let next_parameter_index_assignment = Self::for_next_index_assignment(
                &current_parameter_index_assignment,
                &param_value_strings_of_each_param,
            );
            match next_parameter_index_assignment {
                Some(next_parameter_index_assignment) => {
                    current_parameter_index_assignment = next_parameter_index_assignment;
                }
                None => break,
            }
        }

        let infer_result_from_stored_forall_fact = self
            .store_fact_without_well_defined_verified_and_infer(&corresponding_forall_fact)
            .map_err(|store_fact_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    format!(
                        "for: failed to store corresponding forall `{}`",
                        corresponding_forall_fact
                    ),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ForAxiomStmt(stmt.clone()),
                infer_result_from_stored_forall_fact,
                all_inside_results,
            ),
        ))
    }

    pub fn exec_by_extension_axiom_stmt(
        &mut self,
        stmt: &ByExtensionAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&stmt.left, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByExtensionAxiomStmt(stmt.clone()),
                    format!("by_extension: left set `{}` is not well-defined", stmt.left),
                    Some(well_defined_error.into()),
                    vec![],
                ))
            })?;
        self.verify_obj_well_defined_and_store_cache(&stmt.right, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByExtensionAxiomStmt(stmt.clone()),
                    format!(
                        "by_extension: right set `{}` is not well-defined",
                        stmt.right
                    ),
                    Some(well_defined_error.into()),
                    vec![],
                ))
            })?;

        self.runtime_context.push_env();
        let local_proof_result =
            (|| -> Result<(Vec<NonErrStmtExecResult>, Fact, Fact), RuntimeError> {
                let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
                for proof_stmt in stmt.proof.iter() {
                    let one_proof_stmt_exec_result =
                        self.exec_stmt(proof_stmt).map_err(|stmt_error| {
                            RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByExtensionAxiomStmt(stmt.clone()),
                    format!(
                                    "by_extension: failed to execute proof stmt `{}`",
                                    proof_stmt
                                ),
                                Some(stmt_error),
                                vec![],
                            ))
                        })?;
                    inside_results.push(one_proof_stmt_exec_result);
                }

                let unused_name = self.generate_an_unused_name();

                let left_to_right_forall_fact = Fact::ForallFact(ForallFact::new(
                    vec![ParamDefWithParamType(
                        vec![unused_name.clone()],
                        ParamType::Obj(stmt.left.clone()),
                    )],
                    vec![],
                    vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                        InFact::new(
                            Obj::Identifier(Identifier::new(unused_name.clone())),
                            stmt.right.clone(),
                            stmt.line_file,
                        ),
                    ))],
                    stmt.line_file,
                ));
                self.verify_fact_return_err_if_not_true(
                    &left_to_right_forall_fact,
                    &VerifyState::new(0, false),
                )
                .map_err(|verify_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByExtensionAxiomStmt(stmt.clone()),
                    format!(
                            "by_extension: failed to prove left subset right `{}`",
                            left_to_right_forall_fact
                        ),
                        Some(verify_error.into()),
                        vec![],
                    ))
                })?;

                let right_to_left_forall_fact = Fact::ForallFact(ForallFact::new(
                    vec![ParamDefWithParamType(
                        vec![unused_name.clone()],
                        ParamType::Obj(stmt.right.clone()),
                    )],
                    vec![],
                    vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                        InFact::new(
                            Obj::Identifier(Identifier::new(unused_name.clone())),
                            stmt.left.clone(),
                            stmt.line_file,
                        ),
                    ))],
                    stmt.line_file,
                ));
                self.verify_fact_return_err_if_not_true(
                    &right_to_left_forall_fact,
                    &VerifyState::new(0, false),
                )
                .map_err(|verify_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByExtensionAxiomStmt(stmt.clone()),
                    format!(
                            "by_extension: failed to prove right subset left `{}`",
                            right_to_left_forall_fact
                        ),
                        Some(verify_error.into()),
                        vec![],
                    ))
                })?;
                Ok((
                    inside_results,
                    left_to_right_forall_fact,
                    right_to_left_forall_fact,
                ))
            })();
        self.runtime_context.pop_env();
        let (inside_results, _, _) = local_proof_result?;

        // left = right
        let left_equal_to_right_atomic_fact = AtomicFact::EqualFact(EqualFact::new(
            stmt.left.clone(),
            stmt.right.clone(),
            stmt.line_file,
        ));

        let mut infer_result = InferResult::new();
        infer_result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                &left_equal_to_right_atomic_fact,
            )?,
        );

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ByExtensionAxiomStmt(stmt.clone()),
                infer_result,
                inside_results,
            ),
        ))
    }

    pub fn exec_by_fn_def_axiom_stmt(
        &mut self,
        stmt: &ByFnDefAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::ByFnDefAxiomStmt(stmt.clone()))
    }

    pub fn exec_by_cart_def_axiom_stmt(
        &mut self,
        stmt: &ByCartDefAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::ByCartDefAxiomStmt(stmt.clone()))
    }
}

impl<'a> Runtime<'a> {
    fn integer_string_from_number_like_obj_for_for(
        number_like_obj: &Obj,
        line_file: (usize, usize),
    ) -> Result<String, RuntimeError> {
        let calculated_string = match number_like_obj.normalized_calculated_value() {
            Some(calculated_number) => calculated_number.normalized_value,
            None => {
                return Err(RuntimeError::UnknownError(UnknownError::new(
                    format!(
                        "for: range boundary `{}` must be a calculable number expression",
                        number_like_obj
                    ),
                    line_file,
                    None,
                )));
            }
        };

        if !is_number_string_literally_integer_without_dot(calculated_string.clone()) {
            return Err(RuntimeError::UnknownError(UnknownError::new(
                format!(
                    "for: range boundary `{}` is not an integer number",
                    number_like_obj
                ),
                line_file,
                None,
            )));
        }
        Ok(calculated_string)
    }

    fn for_param_value_strings_of_each_param(
        stmt: &ForAxiomStmt,
    ) -> Result<Vec<Vec<String>>, String> {
        let mut param_value_strings_of_each_param: Vec<Vec<String>> = Vec::new();
        for param_set in stmt.param_sets.iter() {
            let (start_obj, end_obj, is_closed_range) = match param_set {
                crate::stmt::axiom_stmt::ClosedRangeOrRange::ClosedRange(closed_range) => {
                    (closed_range.start.as_ref(), closed_range.end.as_ref(), true)
                }
                crate::stmt::axiom_stmt::ClosedRangeOrRange::Range(range) => {
                    (range.start.as_ref(), range.end.as_ref(), false)
                }
            };
            let start_integer_string =
                Self::integer_string_from_number_like_obj_for_for(start_obj, stmt.line_file)
                    .map_err(|e| e.to_string())?;
            let end_integer_string =
                Self::integer_string_from_number_like_obj_for_for(end_obj, stmt.line_file)
                    .map_err(|e| e.to_string())?;
            let start_integer_i128 = start_integer_string.parse::<i128>().map_err(|_| {
                format!(
                    "for: failed to parse start boundary `{}` as integer",
                    start_integer_string
                )
            })?;
            let end_integer_i128 = end_integer_string.parse::<i128>().map_err(|_| {
                format!(
                    "for: failed to parse end boundary `{}` as integer",
                    end_integer_string
                )
            })?;

            let mut one_param_value_strings: Vec<String> = Vec::new();
            if start_integer_i128 <= end_integer_i128 {
                let right_boundary = if is_closed_range {
                    end_integer_i128
                } else {
                    end_integer_i128 - 1
                };
                if start_integer_i128 <= right_boundary {
                    let mut current_value_i128 = start_integer_i128;
                    while current_value_i128 <= right_boundary {
                        one_param_value_strings.push(current_value_i128.to_string());
                        current_value_i128 += 1;
                    }
                }
            }
            param_value_strings_of_each_param.push(one_param_value_strings);
        }
        Ok(param_value_strings_of_each_param)
    }

    fn for_start_index_assignment(stmt: &ForAxiomStmt) -> Vec<usize> {
        let mut start_index_assignment: Vec<usize> = Vec::new();
        for _ in stmt.param_sets.iter() {
            start_index_assignment.push(0);
        }
        start_index_assignment
    }

    fn for_next_index_assignment(
        current_parameter_index_assignment: &Vec<usize>,
        param_value_strings_of_each_param: &Vec<Vec<String>>,
    ) -> Option<Vec<usize>> {
        let mut next_parameter_index_assignment = current_parameter_index_assignment.clone();
        for reversed_position in 0..next_parameter_index_assignment.len() {
            let position_from_right = next_parameter_index_assignment.len() - 1 - reversed_position;
            let current_index = next_parameter_index_assignment[position_from_right];
            let current_range_length = param_value_strings_of_each_param[position_from_right].len();
            if current_index + 1 < current_range_length {
                next_parameter_index_assignment[position_from_right] = current_index + 1;
                return Some(next_parameter_index_assignment);
            }
            next_parameter_index_assignment[position_from_right] = 0;
        }
        None
    }

    fn exec_for_axiom_stmt_for_one_assignment(
        &mut self,
        stmt: &ForAxiomStmt,
        parameter_index_assignment: &Vec<usize>,
        param_value_strings_of_each_param: &Vec<Vec<String>>,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        self.runtime_context.push_env();
        let execute_result = self.exec_for_axiom_stmt_for_one_assignment_body(
            stmt,
            parameter_index_assignment,
            param_value_strings_of_each_param,
        );
        self.runtime_context.pop_env();
        execute_result
    }

    fn exec_for_axiom_stmt_for_one_assignment_body(
        &mut self,
        stmt: &ForAxiomStmt,
        parameter_index_assignment: &Vec<usize>,
        param_value_strings_of_each_param: &Vec<Vec<String>>,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for (parameter_position, parameter_name) in stmt.params.iter().enumerate() {
            let assigned_integer_string = param_value_strings_of_each_param[parameter_position]
                [parameter_index_assignment[parameter_position]]
                .clone();
            self.store_identifier_obj(parameter_name)
                .map_err(RuntimeError::from)?;

            // it is in Z
            let parameter_in_z_atomic_fact = AtomicFact::InFact(InFact::new(
                Obj::Identifier(Identifier::new(parameter_name.clone())),
                Obj::ZObj(ZObj::new()),
                stmt.line_file,
            ));
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                &parameter_in_z_atomic_fact,
            )
            .map_err(RuntimeError::from)?;

            let parameter_equal_to_assigned_obj_atomic_fact =
                AtomicFact::EqualFact(EqualFact::new(
                    Obj::Identifier(Identifier::new(parameter_name.clone())),
                    Obj::Number(Number::new(assigned_integer_string)),
                    stmt.line_file,
                ));
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                &parameter_equal_to_assigned_obj_atomic_fact,
            )
            .map_err(RuntimeError::from)?;
        }

        let mut no_dom_fact_is_false = true;
        for dom_fact in stmt.dom_facts.iter() {
            let verify_dom_result =
                self.verify_atomic_fact(dom_fact, &VerifyState::new(0, false))?;
            if verify_dom_result.is_true() {
                self.store_atomic_fact_without_well_defined_verified_and_infer(dom_fact)
                    .map_err(RuntimeError::from)?;
                inside_results.push(verify_dom_result);
            } else {
                let reversed = dom_fact.make_reversed();
                let verify_reversed_dom_result =
                    self.verify_atomic_fact(&reversed, &VerifyState::new(0, false))?;
                if verify_reversed_dom_result.is_unknown() {
                    return Err(RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    format!("for: domain fact `{}` or its reversed `{}` must be verified to be true, but both are unknown", dom_fact, reversed),
                        None,
                        inside_results,
                    )));
                }
                if verify_reversed_dom_result.is_true() {
                    no_dom_fact_is_false = false;
                }
            }
        }

        if !no_dom_fact_is_false {
            return Ok(inside_results);
        }

        for proof_stmt in stmt.proof.iter() {
            let proof_result = self.exec_stmt(proof_stmt)?;
            inside_results.push(proof_result);
        }
        for fact_to_prove in stmt.then_facts.iter() {
            let verified_result = self.verify_exist_or_and_chain_atomic_fact(
                fact_to_prove,
                &VerifyState::new(0, false),
            )?;
            if verified_result.is_unknown() {
                return Err(RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    format!("for: failed to prove `{}`", fact_to_prove),
                    None,
                    inside_results,
                )));
            }
            inside_results.push(verified_result);
        }
        Ok(inside_results)
    }

    fn enumerate_start_index_assignment(stmt: &EnumerateAxiomStmt) -> Vec<usize> {
        let mut start_index_assignment: Vec<usize> = Vec::new();
        for _ in stmt.param_sets.iter() {
            start_index_assignment.push(0);
        }
        start_index_assignment
    }

    fn enumerate_next_index_assignment(
        stmt: &EnumerateAxiomStmt,
        current_parameter_index_assignment: &Vec<usize>,
    ) -> Option<Vec<usize>> {
        let mut next_parameter_index_assignment = current_parameter_index_assignment.clone();
        for reversed_position in 0..next_parameter_index_assignment.len() {
            let position_from_right = next_parameter_index_assignment.len() - 1 - reversed_position;
            let current_index = next_parameter_index_assignment[position_from_right];
            let current_list_set_length = stmt.param_sets[position_from_right].list.len();
            if current_index + 1 < current_list_set_length {
                next_parameter_index_assignment[position_from_right] = current_index + 1;
                return Some(next_parameter_index_assignment);
            }
            next_parameter_index_assignment[position_from_right] = 0;
        }
        None
    }

    fn exec_enumerate_axiom_stmt_for_one_assignment(
        &mut self,
        stmt: &EnumerateAxiomStmt,
        parameter_index_assignment: &Vec<usize>,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        self.runtime_context.push_env();
        let execute_result = self
            .exec_enumerate_axiom_stmt_for_one_assignment_body(stmt, parameter_index_assignment);
        self.runtime_context.pop_env();
        execute_result
    }

    fn exec_enumerate_axiom_stmt_for_one_assignment_body(
        &mut self,
        stmt: &EnumerateAxiomStmt,
        parameter_index_assignment: &Vec<usize>,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for (parameter_position, parameter_name) in stmt.params.iter().enumerate() {
            let assigned_obj = (*stmt.param_sets[parameter_position].list
                [parameter_index_assignment[parameter_position]])
                .clone();
            self.store_identifier_obj(parameter_name)
                .map_err(RuntimeError::from)?;
            let parameter_equal_to_assigned_obj_atomic_fact =
                AtomicFact::EqualFact(EqualFact::new(
                    Obj::Identifier(Identifier::new(parameter_name.clone())),
                    assigned_obj.clone(),
                    stmt.line_file,
                ));
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                &parameter_equal_to_assigned_obj_atomic_fact,
            )
            .map_err(RuntimeError::from)?;
        }
        for proof_stmt in stmt.proof.iter() {
            let proof_result = self.exec_stmt(proof_stmt)?;
            inside_results.push(proof_result);
        }
        for fact_to_prove in stmt.to_prove.iter() {
            let verified_result = self
                .verify_fact_return_err_if_not_true(fact_to_prove, &VerifyState::new(0, false))?;
            inside_results.push(verified_result);
        }
        Ok(inside_results)
    }

    fn exec_by_cases_axiom_stmt_verify_cases_cover_all_situations(
        &mut self,
        stmt: &ByCasesAxiomStmt,
    ) -> Result<(), ExecStmtError> {
        let all_cases_or_fact = Fact::OrFact(OrFact::new(stmt.cases.clone(), stmt.line_file));
        self.verify_fact_return_err_if_not_true(&all_cases_or_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                ExecStmtError::with_message_and_cause(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    "by_cases: cannot verify that all cases cover all situations".to_string(),
                    Some(verify_error.into()),
                    vec![],
                )
            })?;
        Ok(())
    }

    fn exec_by_cases_axiom_stmt_prove_then_facts_under_case(
        &mut self,
        stmt: &ByCasesAxiomStmt,
        case_index: usize,
        inside_results: &mut Vec<NonErrStmtExecResult>,
    ) -> Result<(), ExecStmtError> {
        for then_fact in stmt.then_facts.iter() {
            let exec_fact_result = self.exec_fact(then_fact).map_err(|statement_error| {
                ExecStmtError::with_message_and_cause(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    format!(
                        "by_cases: failed to prove `{}` under case `{}`",
                        then_fact, stmt.cases[case_index]
                    ),
                    Some(statement_error),
                    std::mem::take(inside_results),
                )
            })?;
            inside_results.push(exec_fact_result);
        }
        Ok(())
    }

    fn exec_by_cases_axiom_stmt_for_one_case(
        &mut self,
        stmt: &ByCasesAxiomStmt,
        case_index: usize,
    ) -> Result<Vec<NonErrStmtExecResult>, ExecStmtError> {
        let case_fact = &stmt.cases[case_index];
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();

        self.store_and_chain_atomic_fact_without_well_defined_verified_and_infer(case_fact)
            .map_err(|store_fact_error| {
                ExecStmtError::with_message_and_cause(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    format!("by_cases: failed to assume case `{}`", case_fact),
                    Some(store_fact_error.into()),
                    vec![],
                )
            })?;

        for proof_stmt in stmt.proofs[case_index].iter() {
            let exec_stmt_result = self.exec_stmt(proof_stmt);
            match exec_stmt_result {
                Ok(result) => inside_results.push(result),
                Err(statement_error) => {
                    return Err(ExecStmtError::with_message_and_cause(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    format!(
                            "by_cases: failed while executing proof under case `{}`",
                            case_fact
                        ),
                        Some(statement_error),
                        inside_results,
                    ));
                }
            }
        }

        if let Some(impossible_fact) = &stmt.impossible_facts[case_index] {
            let verify_state = VerifyState::new(0, false);
            let verify_impossible_fact_result = self
                .verify_atomic_fact(impossible_fact, &verify_state)
                .map_err(|verify_error| {
                    ExecStmtError::with_message_and_cause(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    impossible_proof_error_message(
                            impossible_fact,
                            Some(case_fact.to_string()),
                        ),
                        Some(verify_error.into()),
                        vec![],
                    )
                })?;

            if verify_impossible_fact_result.is_unknown() {
                return Err(ExecStmtError::with_message_and_cause(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    impossible_proof_error_message(impossible_fact, Some(case_fact.to_string())),
                    None,
                    vec![],
                ));
            }

            let verify_reversed_impossible_fact_result = self
                .verify_atomic_fact(&impossible_fact.make_reversed(), &verify_state)
                .map_err(|verify_error| {
                    ExecStmtError::with_message_and_cause(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    impossible_proof_error_message(
                            impossible_fact,
                            Some(case_fact.to_string()),
                        ),
                        Some(verify_error.into()),
                        vec![],
                    )
                })?;

            if verify_reversed_impossible_fact_result.is_unknown() {
                return Err(ExecStmtError::with_message_and_cause(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    impossible_proof_error_message(impossible_fact, Some(case_fact.to_string())),
                    None,
                    vec![],
                ));
            }

            inside_results.push(NonErrStmtExecResult::NonFactualStmtSuccess(
                NonFactualStmtSuccess::new(
                    Stmt::ByCasesAxiomStmt(stmt.clone()),
                    InferResult::new(),
                    vec![
                        verify_impossible_fact_result,
                        verify_reversed_impossible_fact_result,
                    ],
                ),
            ));

            return Ok(inside_results);
        }

        self.exec_by_cases_axiom_stmt_prove_then_facts_under_case(
            stmt,
            case_index,
            &mut inside_results,
        )?;
        Ok(inside_results)
    }
}

fn impossible_proof_error_message(
    impossible_fact: &AtomicFact,
    option_case_fact_string: Option<String>,
) -> String {
    match option_case_fact_string {
        Some(case_fact) => format!(
            "failed to prove impossible `{}` under case `{}`",
            impossible_fact, case_fact
        ),
        None => format!("failed to prove impossible `{}`", impossible_fact),
    }
}
