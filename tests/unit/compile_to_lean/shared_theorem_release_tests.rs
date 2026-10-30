use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;
const CASES: [(&str, usize); 3] = [
    (
        include_str!("../../../lean/examples/shared_quotient_theorem_results/statement.lit"),
        3,
    ),
    (
        include_str!("../../../lean/examples/shared_reciprocal_theorem_results/statement.lit"),
        2,
    ),
    (
        include_str!("../../../lean/examples/shared_square_theorem_packages/statement.lit"),
        1,
    ),
];
fn release(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut run.statement_results[index]
    else {
        panic!("release")
    };
    p
}
#[test]
fn shared_releases_preserve_guarded_objects_compounds_and_local_uses() {
    for (source, _) in CASES {
        let (run, c) = super::execute(source);
        let out = c.compile_run(&run, "shared_release").unwrap();
        assert!(
            out.len() < 150_000,
            "a pair of returned facts must not duplicate a complete invocation repeatedly"
        );
    }
}
#[test]
fn shared_releases_require_original_callee_and_caller_stages() {
    for (source, index) in CASES {
        for mutation in 0..4 {
            let (mut run, c) = super::execute(source);
            let p = release(&mut run, index);
            match mutation {
                0 => {
                    p.conclusions_wd.pop();
                }
                1 => {
                    p.stored_wd.pop();
                }
                2 => {
                    p.stored.pop();
                }
                _ => p.type_proofs.clear(),
            }
            c.compile_run(&run, "missing_shared_stage").expect_err(
                "every original callee WD and ordered caller WD/store remains required",
            );
        }
    }
}
