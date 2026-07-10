use super::helpers_by_stmt::{
    or_branches_closed_range_start_plus_offset_equalities,
    or_branches_integer_closed_range_equalities,
};
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_closed_range_as_cases_stmt(
        &mut self,
        stmt: &ByClosedRangeAsCasesStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let set_obj: Obj = stmt.closed_range.clone().into();
        let element = stmt.element.clone();
        let in_fact = InFact::new(element, set_obj, stmt.line_file.clone());
        let in_atomic: AtomicFact = in_fact.clone().into();
        let verify_state = VerifyState::new(0, false);
        let membership = self.verify_atomic_fact(&in_atomic, &verify_state)?;
        if membership.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by closed_range as cases: membership `{}` is not known",
                    in_fact
                ),
                None,
                vec![],
            ));
        }
        let mut inside_results = vec![membership];
        let mut endpoint_facts = Vec::new();

        let z_set: Obj = StandardSet::Z.into();
        let lf = stmt.line_file.clone();
        for (side, endpoint) in [
            ("left", stmt.closed_range.start.as_ref().clone()),
            ("right", stmt.closed_range.end.as_ref().clone()),
        ] {
            let in_z: AtomicFact = InFact::new(endpoint, z_set.clone(), lf.clone()).into();
            let in_z_ok = self.verify_atomic_fact(&in_z, &verify_state)?;
            if in_z_ok.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by closed_range as cases: range {} endpoint must be known in Z (`{}`)",
                        side, in_z
                    ),
                    None,
                    vec![],
                ));
            }
            endpoint_facts.push(in_z.to_string());
            inside_results.push(in_z_ok);
        }

        let branches = match or_branches_integer_closed_range_equalities(
            stmt.element.clone(),
            &stmt.closed_range,
            &stmt.line_file,
            "by closed_range as cases",
        ) {
            Ok(b) => {
                if b.is_empty() {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        "by closed_range as cases: integer range is empty (end < start)"
                            .to_string(),
                        None,
                        vec![],
                    ));
                }
                b
            }
            Err(literal_err) => match or_branches_closed_range_start_plus_offset_equalities(
                stmt.element.clone(),
                &stmt.closed_range,
                &stmt.line_file,
                "by closed_range as cases",
            ) {
                Ok(b) => b,
                Err(offset_err) => {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!("{} ({})", offset_err, literal_err),
                        None,
                        vec![],
                    ));
                }
            },
        };
        let generated_fact: Fact = if branches.len() == 1 {
            branches[0].clone().into()
        } else {
            OrFact::new(branches, stmt.line_file.clone()).into()
        };
        let generated_fact_string = generated_fact.to_string();
        let infer_after_store = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(
                generated_fact.clone(),
            )
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&generated_fact);
        infer_result.new_infer_result_inside(infer_after_store);

        let by_verification = ByEnumerateRangeVerificationResult::new(
            "by closed_range as cases proof".to_string(),
            stmt.element.to_string(),
            Obj::ClosedRange(stmt.closed_range.clone()).to_string(),
            in_fact.to_string(),
            endpoint_facts,
            generated_fact_string,
        );
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            inside_results,
            by_verification.into(),
        )
        .into())
    }
}
