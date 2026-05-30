use super::helpers_by_stmt::{
    or_branches_closed_range_start_plus_offset_equalities,
    or_branches_integer_closed_range_equalities, or_branches_integer_range_equalities,
    or_branches_range_start_plus_offset_equalities,
};
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_enumerate_range_stmt(
        &mut self,
        stmt: &ByEnumerateRangeStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let set_obj = enumerated_range_set_obj(&stmt.range);
        let element = stmt.element.clone();
        let in_fact = InFact::new(element, set_obj, stmt.line_file.clone());
        let in_atomic: AtomicFact = in_fact.clone().into();
        let verify_state = VerifyState::new(0, false);
        let membership = self.verify_atomic_fact(&in_atomic, &verify_state)?;
        let stmt_name = enumerate_range_stmt_name(&stmt.range);
        if membership.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!("{}: membership `{}` is not known", stmt_name, in_fact),
                None,
                vec![],
            ));
        }

        let z_set: Obj = StandardSet::Z.into();
        let lf = stmt.line_file.clone();
        let (start, end) = enumerated_range_endpoints(&stmt.range);
        for (side, endpoint) in [("left", start), ("right", end)] {
            let in_z: AtomicFact =
                InFact::new((*endpoint).clone(), z_set.clone(), lf.clone()).into();
            let in_z_ok = self.verify_atomic_fact(&in_z, &verify_state)?;
            if in_z_ok.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "{}: range {} endpoint must be known in Z (`{}`)",
                        stmt_name, side, in_z
                    ),
                    None,
                    vec![],
                ));
            }
        }

        let branches = match enumerate_range_equalities(stmt) {
            Ok(branches) => {
                if branches.is_empty() {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "{}: {}",
                            stmt_name,
                            enumerate_range_empty_error(&stmt.range)
                        ),
                        None,
                        vec![],
                    ));
                }
                branches
            }
            Err(msg) => {
                return Err(short_exec_error(stmt.clone().into(), msg, None, vec![]));
            }
        };

        let generated_fact: Fact = if branches.len() == 1 {
            branches[0].clone().into()
        } else {
            OrFact::new(branches, stmt.line_file.clone()).into()
        };
        let infer_after_store = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(
                generated_fact.clone(),
            )
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;

        let mut infer_result = InferResult::new();
        infer_result.new_fact(&generated_fact);
        infer_result.new_infer_result_inside(infer_after_store);

        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}

fn enumerated_range_set_obj(range: &ClosedRangeOrRange) -> Obj {
    match range {
        ClosedRangeOrRange::ClosedRange(closed_range) => closed_range.clone().into(),
        ClosedRangeOrRange::Range(range) => range.clone().into(),
    }
}

fn enumerated_range_endpoints(range: &ClosedRangeOrRange) -> (&Obj, &Obj) {
    match range {
        ClosedRangeOrRange::ClosedRange(closed_range) => {
            (closed_range.start.as_ref(), closed_range.end.as_ref())
        }
        ClosedRangeOrRange::Range(range) => (range.start.as_ref(), range.end.as_ref()),
    }
}

fn enumerate_range_stmt_name(range: &ClosedRangeOrRange) -> &'static str {
    match range {
        ClosedRangeOrRange::ClosedRange(_) => "by enumerate closed_range",
        ClosedRangeOrRange::Range(_) => "by enumerate range",
    }
}

fn enumerate_range_empty_error(range: &ClosedRangeOrRange) -> &'static str {
    match range {
        ClosedRangeOrRange::ClosedRange(_) => "integer range is empty (end < start)",
        ClosedRangeOrRange::Range(_) => "integer range is empty (end <= start)",
    }
}

fn enumerate_range_equalities(
    stmt: &ByEnumerateRangeStmt,
) -> Result<Vec<AndChainAtomicFact>, String> {
    let stmt_name = enumerate_range_stmt_name(&stmt.range);
    match &stmt.range {
        ClosedRangeOrRange::ClosedRange(closed_range) => {
            match or_branches_integer_closed_range_equalities(
                stmt.element.clone(),
                closed_range,
                &stmt.line_file,
                stmt_name,
            ) {
                Ok(branches) => Ok(branches),
                Err(literal_err) => match or_branches_closed_range_start_plus_offset_equalities(
                    stmt.element.clone(),
                    closed_range,
                    &stmt.line_file,
                    stmt_name,
                ) {
                    Ok(branches) => Ok(branches),
                    Err(offset_err) => Err(format!("{} ({})", offset_err, literal_err)),
                },
            }
        }
        ClosedRangeOrRange::Range(range) => {
            match or_branches_integer_range_equalities(
                stmt.element.clone(),
                range,
                &stmt.line_file,
                stmt_name,
            ) {
                Ok(branches) => Ok(branches),
                Err(literal_err) => match or_branches_range_start_plus_offset_equalities(
                    stmt.element.clone(),
                    range,
                    &stmt.line_file,
                    stmt_name,
                ) {
                    Ok(branches) => Ok(branches),
                    Err(offset_err) => Err(format!("{} ({})", offset_err, literal_err)),
                },
            }
        }
    }
}
