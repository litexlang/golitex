use super::enumerate_helpers::{
    expand_closed_range_values, membership_in_fact, membership_or_equalities_fact,
};
use super::helper::{store_goal_fact, verify_goal_fact};
use super::result::{
    ExecByClosedRangeAsCasesStmtFailed, ExecByClosedRangeAsCasesStmtResult,
    ExecByClosedRangeAsCasesStmtSuccess, ExecByStmtResult,
};
use crate::new_pipeline::ast::obj::{Obj, SetFormer};
use crate::new_pipeline::ast::stmt::ByClosedRangeAsCasesStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Legacy semantics: membership `element $in closed_range` must already be known;
// then store the expanded equality cases without re-proving them as a goal.
//
// Example:
//   have y Z
//   trust y $in 1...2
//   by closed_range as cases: y $in 1...2
// stores `y = 1 or y = 2`.
pub fn exec_by_closed_range_as_cases_stmt(
    runtime: &mut Runtime,
    stmt: &ByClosedRangeAsCasesStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let values = match expand_closed_range_values(&stmt.closed_range) {
        Ok(v) => v,
        Err(msg) => {
            return Ok(ExecByStmtResult::ClosedRangeAsCases(
                ExecByClosedRangeAsCasesStmtResult::Failed(
                    ExecByClosedRangeAsCasesStmtFailed::Domain(msg),
                ),
            ));
        }
    };
    if values.is_empty() {
        return Ok(ExecByStmtResult::ClosedRangeAsCases(
            ExecByClosedRangeAsCasesStmtResult::Failed(ExecByClosedRangeAsCasesStmtFailed::Domain(
                "closed_range as cases: expanded domain is empty".to_string(),
            )),
        ));
    }

    let set = Obj::SetFormer(SetFormer::ClosedRange(stmt.closed_range.clone()));
    let (outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let membership_fact = membership_in_fact(rt, &stmt.element, set, &stmt.line_file);
        let membership = verify_goal_fact(rt, &membership_fact)?;
        if membership.is_failed() {
            return Ok(Err(membership));
        }
        Ok(Ok(membership))
    })?;

    let membership = match outcome {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecByStmtResult::ClosedRangeAsCases(
                ExecByClosedRangeAsCasesStmtResult::Failed(
                    ExecByClosedRangeAsCasesStmtFailed::Membership(failed),
                ),
            ));
        }
    };

    let expanded_fact =
        membership_or_equalities_fact(runtime, &stmt.element, &values, &stmt.line_file);
    let stored = match store_goal_fact(runtime, &expanded_fact)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::ClosedRangeAsCases(
                ExecByClosedRangeAsCasesStmtResult::Failed(
                    ExecByClosedRangeAsCasesStmtFailed::Store(msg),
                ),
            ));
        }
    };

    Ok(ExecByStmtResult::ClosedRangeAsCases(
        ExecByClosedRangeAsCasesStmtResult::Success(ExecByClosedRangeAsCasesStmtSuccess {
            values,
            membership,
            local_env,
            stored,
        }),
    ))
}
