use super::enumerate_helpers::{
    closed_range_or_range_as_obj, expand_closed_range_or_range, membership_in_fact,
    membership_or_equalities_fact,
};
use super::helper::{store_goal_fact, verify_goal_fact};
use super::result::{
    ExecByEnumerateRangeStmtFailed, ExecByEnumerateRangeStmtResult,
    ExecByEnumerateRangeStmtSuccess, ExecByStmtResult,
};
use crate::new_pipeline::ast::stmt::ByEnumerateRangeStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Legacy semantics: membership `element $in range` must already be known; then
// store the expanded equality cases without re-proving them as a goal.
//
// Example:
//   have x Z
//   trust x $in range(1, 3)
//   by enumerate range: x $in range(1, 3)
// stores `x = 1 or x = 2`.
pub fn exec_by_enumerate_range_stmt(
    runtime: &mut Runtime,
    stmt: &ByEnumerateRangeStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let values = match expand_closed_range_or_range(&stmt.range) {
        Ok(v) => v,
        Err(msg) => {
            return Ok(ExecByStmtResult::EnumerateRange(
                ExecByEnumerateRangeStmtResult::Failed(ExecByEnumerateRangeStmtFailed::Domain(msg)),
            ));
        }
    };
    if values.is_empty() {
        return Ok(ExecByStmtResult::EnumerateRange(
            ExecByEnumerateRangeStmtResult::Failed(ExecByEnumerateRangeStmtFailed::Domain(
                "enumerate range: expanded domain is empty".to_string(),
            )),
        ));
    }

    let set = closed_range_or_range_as_obj(&stmt.range);
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
            return Ok(ExecByStmtResult::EnumerateRange(
                ExecByEnumerateRangeStmtResult::Failed(ExecByEnumerateRangeStmtFailed::Membership(
                    failed,
                )),
            ));
        }
    };

    let expanded_fact =
        membership_or_equalities_fact(runtime, &stmt.element, &values, &stmt.line_file);
    let stored = match store_goal_fact(runtime, &expanded_fact)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::EnumerateRange(
                ExecByEnumerateRangeStmtResult::Failed(ExecByEnumerateRangeStmtFailed::Store(msg)),
            ));
        }
    };

    Ok(ExecByStmtResult::EnumerateRange(
        ExecByEnumerateRangeStmtResult::Success(ExecByEnumerateRangeStmtSuccess {
            values,
            membership,
            local_env,
            stored,
        }),
    ))
}
