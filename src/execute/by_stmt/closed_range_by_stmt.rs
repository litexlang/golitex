use crate::common::helper::is_number_string_literally_integer_without_dot;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_enumerate_closed_range_stmt(
        &mut self,
        stmt: &ByEnumerateClosedRangeStmt,
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
                    "by enumerate closed_range: membership `{}` is not known",
                    in_fact
                ),
                None,
                vec![],
            ));
        }

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
                        "by enumerate closed_range: range {} endpoint must be known in Z (`{}`)",
                        side, in_z
                    ),
                    None,
                    vec![],
                ));
            }
        }

        let branches = match or_branches_integer_closed_range_equalities(
            stmt.element.clone(),
            &stmt.closed_range,
            &stmt.line_file,
        ) {
            Ok(b) => {
                if b.is_empty() {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        "by enumerate closed_range: integer range is empty (end < start)".to_string(),
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
        let disjunction = OrFact::new(branches, stmt.line_file.clone());
        let disjunction_fact: Fact = disjunction.into();
        let infer_after_store = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(disjunction_fact.clone())
            .map_err(|e| short_exec_error(stmt.clone().into(), "", Some(e), vec![]))?;

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&disjunction_fact);
        infer_result.new_infer_result_inside(infer_after_store);

        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}

fn closed_range_endpoint_integer_string(obj: &Obj) -> Result<String, String> {
    let Obj::Number(n) = obj else {
        return Err("by enumerate closed_range: range endpoints must be integer literals".to_string());
    };
    let s = n.normalized_value.clone();
    if !is_number_string_literally_integer_without_dot(s.clone()) {
        return Err(
            "by enumerate closed_range: range endpoints must be integers (no decimal point)"
                .to_string(),
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
        .map_err(|_| format!("by enumerate closed_range: invalid integer `{}`", start_s))?;
    let end_i: i128 = end_s
        .parse()
        .map_err(|_| format!("by enumerate closed_range: invalid integer `{}`", end_s))?;

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

/// `closed_range(start, start + N)` with integer literal `N >= 0`; `start` may be any obj.
fn or_branches_closed_range_start_plus_offset_equalities(
    element: Obj,
    closed: &ClosedRange,
    line_file: &LineFile,
) -> Result<Vec<AndChainAtomicFact>, String> {
    let start = closed.start.as_ref();
    let end = closed.end.as_ref();
    let Obj::Add(add) = end else {
        return Err(
            "by enumerate closed_range: when start is not an integer literal, end must be start + N"
                .to_string(),
        );
    };
    if add.left.as_ref().to_string() != start.to_string() {
        return Err(
            "by enumerate closed_range: end must be start + N (left addend equals range start)"
                .to_string(),
        );
    }
    let Obj::Number(n) = add.right.as_ref() else {
        return Err(
            "by enumerate closed_range: N in start + N must be an integer literal".to_string(),
        );
    };
    let s = n.normalized_value.clone();
    if !is_number_string_literally_integer_without_dot(s.clone()) {
        return Err(
            "by enumerate closed_range: N in start + N must be an integer (no decimal point)"
                .to_string(),
        );
    }
    let k: i128 = s
        .parse()
        .map_err(|_| format!("by enumerate closed_range: invalid integer offset `{}`", s))?;
    if k < 0 {
        return Err(
            "by enumerate closed_range: offset N in start + N must be non-negative".to_string(),
        );
    }

    let mut branches: Vec<AndChainAtomicFact> = Vec::new();
    let mut i = 0_i128;
    while i <= k {
        let rhs = if i == 0 {
            start.clone()
        } else {
            Add::new(start.clone(), Number::new(i.to_string()).into()).into()
        };
        let eq = EqualFact::new(element.clone(), rhs, line_file.clone());
        branches.push(AndChainAtomicFact::AtomicFact(eq.into()));
        i += 1;
    }
    Ok(branches)
}
