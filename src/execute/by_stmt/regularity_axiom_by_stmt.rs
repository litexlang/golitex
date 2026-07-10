use crate::prelude::*;

impl Runtime {
    pub fn exec_by_regularity_axiom_stmt(
        &mut self,
        stmt: &ByRegularityAxiomStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&stmt.set, &VerifyState::new(0, false))
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
        let nonempty_result = self
            .verify_fact_return_err_if_not_true(&nonempty_fact, &VerifyState::new(0, false))
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

        // Trusted regularity/foundation step: every nonempty set A has a member
        // disjoint from A. Example: by regularity_axiom(A) stores
        // exist x A st {intersect(x, A) = {}}.
        let regularity_fact =
            regularity_axiom_exist_fact(stmt.set.clone(), stmt.line_file.clone())?;
        let regularity_fact_string = regularity_fact.to_string();
        let infer_result = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(regularity_fact)
            .map_err(|store_error| {
                short_exec_error(
                    stmt.clone().into(),
                    "by regularity_axiom: failed to store regularity conclusion".to_string(),
                    Some(store_error),
                    vec![],
                )
            })?;

        let by_verification = ByChoiceVerificationResult::new(
            "by regularity_axiom proof".to_string(),
            stmt.set.to_string(),
            0,
            vec![("nonempty".to_string(), nonempty_fact.to_string(), true)],
            regularity_fact_string,
        );
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            vec![nonempty_result],
            ByVerificationResult::RegularityAxiom(by_verification),
        )
        .into())
    }
}

fn regularity_axiom_exist_fact(set: Obj, line_file: LineFile) -> Result<Fact, RuntimeError> {
    let x_name = "x".to_string();
    let x = obj_for_bound_param_in_scope(x_name.clone(), ParamObjType::Exist);
    let empty_set: Obj = ListSet::new(vec![]).into();
    let disjoint_fact = EqualFact::new(
        Intersect::new(x, set.clone()).into(),
        empty_set,
        line_file.clone(),
    );
    let body = ExistFactBody::new(
        ParamDefWithType::new(vec![ParamGroupWithParamType::new(
            vec![x_name],
            ParamType::Obj(set),
        )]),
        vec![disjoint_fact.into()],
        line_file,
    )?;
    Ok(ExistFactEnum::ExistFact(body).into())
}
