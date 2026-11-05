use crate::execute::execute_by_stmt::{ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess};
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;
const CASES: [(&str, usize); 3] = [
    (
        r#"# Reuse both quotient reconstruction facts from one theorem call, globally and inside a theorem.
thm shared_quotient_reconstruction:
    ? forall x,y R:
        y!=0
        =>:
            (x/y)*y=x
            (x/y) $in R
    (x/y)*y=x
    (x/y) $in R

have shared_numerator R=6
have shared_denominator R=2
release thm shared_quotient_reconstruction(shared_numerator,shared_denominator)

thm shared_quotient_in_context:
    ? forall x,y R:
        y!=0
        =>:
            (x/y) $in R
            (x/y)*y=x
    release thm shared_quotient_reconstruction(x,y)
"#,
        3,
    ),
    (
        r#"# A positive real supplies nonzero evidence and a well-defined reciprocal in one release.
thm nonzero_and_reciprocal:
    ? forall x R+:
        x!=0
        1/x $in R
    x!=0
    1/x $in R

have shared_positive R+=2
release thm nonzero_and_reciprocal(shared_positive)
"#,
        2,
    ),
    (
        r#"# Share a square's equality chain and nonnegative conjunction from one invocation.
thm shared_square_packages:
    ? forall x R:
        x*x=x^2=x*x
        0<=x^2 and x*x=x^2
    x*x=x^2=x*x
    0<=x^2 and x*x=x^2

release thm shared_square_packages(2)

thm square_nonnegative_from_shared_packages:
    ? forall x R:
        0<=x^2
    release thm shared_square_packages(x)
"#,
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
