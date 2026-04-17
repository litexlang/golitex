use crate::common::helper::is_number_string_literally_integer_without_dot;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_closed_range_stmt(
        &mut self,
        stmt: &ByClosedRangeStmt,
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
                format!("by closed_range: membership `{}` is not known", in_fact),
                None,
                vec![],
            ));
        }

        let branches = or_branches_integer_closed_range_equalities(
            stmt.element.clone(),
            &stmt.closed_range,
            &stmt.line_file,
        )
        .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;
        if branches.is_empty() {
            return Err(short_exec_error(
                stmt.clone().into(),
                "by closed_range: integer range is empty (end < start)".to_string(),
                None,
                vec![],
            ));
        }
        let disjunction = OrFact::new(branches, stmt.line_file.clone());
        let disjunction_fact: Fact = disjunction.into();
        let infer_after_store = self
            .store_fact_without_well_defined_verified_and_infer(disjunction_fact.clone())
            .map_err(|e| short_exec_error(stmt.clone().into(), "", Some(e), vec![]))?;

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&disjunction_fact);
        infer_result.new_infer_result_inside(infer_after_store);

        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}

fn closed_range_endpoint_integer_string(obj: &Obj) -> Result<String, String> {
    let Obj::Number(n) = obj else {
        return Err("by closed_range: range endpoints must be integer literals".to_string());
    };
    let s = n.normalized_value.clone();
    if !is_number_string_literally_integer_without_dot(s.clone()) {
        return Err(
            "by closed_range: range endpoints must be integers (no decimal point)".to_string(),
        );
    }
    Ok(s)
}

fn or_branches_integer_closed_range_equalities(
    element: Obj,
    closed: &ClosedRange,
    line_file: &LineFile,
) -> Result<Vec<AndChainAtomicFact>, String> {
    let start_s = closed_range_endpoint_integer_string(closed.start.as_ref())?;
    let end_s = closed_range_endpoint_integer_string(closed.end.as_ref())?;
    let start_i: i128 = start_s
        .parse()
        .map_err(|_| format!("by closed_range: invalid integer `{}`", start_s))?;
    let end_i: i128 = end_s
        .parse()
        .map_err(|_| format!("by closed_range: invalid integer `{}`", end_s))?;

    let mut branches: Vec<AndChainAtomicFact> = Vec::new();
    let mut v = start_i;
    while v <= end_i {
        let eq = EqualFact::new(
            element.clone(),
            Number::new(v.to_string()).into(),
            line_file.clone(),
        );
        branches.push(AndChainAtomicFact::AtomicFact(eq.into()));
        v += 1;
    }
    Ok(branches)
}
