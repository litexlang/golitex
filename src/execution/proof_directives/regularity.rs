use crate::prelude::*;

impl Runtime {
    pub fn exec_by_regularity_axiom_stmt(
        &mut self,
        stmt: &ByRegularityAxiomStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_result(&stmt.set, &VerifyState::initial())
            .map_err(|well_defined_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by regularity_axiom: set `{}` is not well-defined",
                        stmt.set
                    ),
                    Some(well_defined_error),
                    vec![],
                )
            })?;

        let nonempty_fact: Fact =
            IsNonemptySetFact::new(stmt.set.clone(), stmt.line_file.clone()).into();
        let mut nonempty_result = self
            .verify_fact_or_error(&nonempty_fact, &VerifyState::initial())
            .map_err(|verify_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by regularity_axiom: failed to prove nonempty obligation `{}`",
                        nonempty_fact
                    ),
                    Some(verify_error),
                    vec![],
                )
            })?;
        self.attach_known_fact_ids_to_verify_fact_result(&mut nonempty_result)?;
        let nonempty_fact_id = self.require_known_fact_id_for_success_result(&nonempty_fact)?;

        // Trusted regularity/foundation step: every nonempty set A has a member
        // disjoint from A. Example: by regularity_axiom(A) stores
        // exist x A st {intersect(x, A) = {}}.
        let regularity_fact =
            regularity_axiom_exist_fact(self, stmt.set.clone(), stmt.line_file.clone())?;
        let infer_result = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                regularity_fact.clone(),
            )
            .map_err(|store_error| {
                short_exec_error(
                    stmt.clone().into(),
                    "by regularity_axiom: failed to store regularity conclusion".to_string(),
                    Some(store_error),
                    vec![],
                )
            })?;
        let regularity_fact_id = self.require_known_fact_id_for_success_result(&regularity_fact)?;

        let by_verification = SuccessVerifyByChoiceResult::new(
            SuccessVerifyByChoiceProofKind::RegularityAxiom,
            SuccessVerifyByChoiceTargetResult::RegularityAxiom {
                set: stmt.set.clone(),
            },
            Vec::new(),
            vec![SuccessVerifyByChoiceObligationResult {
                role: SuccessVerifyByChoiceObligationRole::RegularityNonempty,
                fact: nonempty_fact,
                fact_id: nonempty_fact_id,
                check: Some(Box::new(nonempty_result)),
            }],
            regularity_fact,
            regularity_fact_id,
        );
        Ok(SuccessByStmtResult::ByRegularityAxiomStmt(Box::new(
            SuccessByRegularityAxiomStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: Some(by_verification),
            },
        ))
        .into())
    }

    pub fn exec_by_regularity_axiom_stmt_affect_environment_only(
        &mut self,
        stmt: &ByRegularityAxiomStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let regularity_fact =
            regularity_axiom_exist_fact(self, stmt.set.clone(), stmt.line_file.clone())?;
        let infer_result = self.store_fact_with_trust_and_infer_with_reason(
            regularity_fact,
            InferReason::StatementWithVerification,
        )?;
        Ok(SuccessByStmtResult::ByRegularityAxiomStmt(Box::new(
            SuccessByRegularityAxiomStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: None,
            },
        ))
        .into())
    }
}

fn regularity_axiom_exist_fact(
    runtime: &Runtime,
    set: Obj,
    line_file: LineFile,
) -> Result<Fact, RuntimeError> {
    let x_name = runtime.generate_internal_binder_name();
    let x_group = runtime.fresh_param_group_with_type(vec![x_name], ParamType::Obj(set.clone()))?;
    let x = obj_for_bound_param_in_scope(&x_group.params[0]);
    let empty_set: Obj = ListSet::new(vec![]).into();
    let disjoint_fact = EqualFact::new(
        Intersect::new(x, set.clone()).into(),
        empty_set,
        line_file.clone(),
    );
    let body = PlainExistFact::new(
        TypedParameterList::new(vec![x_group]),
        vec![disjoint_fact.into()],
        line_file,
    )?;
    Ok(ExistFact::PlainExistFact(body).into())
}
