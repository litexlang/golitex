use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ExpLogOperatorObjWellDefinedProofByDef;
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../lean/examples/evaluated_logarithms/statement.lit");
const RATIONAL: &str =
    include_str!("../../../lean/examples/evaluated_rational_logarithms/statement.lit");
const ARITHMETIC: &str =
    include_str!("../../../lean/examples/evaluated_logarithm_arithmetic/statement.lit");
const FUNCTIONS: &str =
    include_str!("../../../lean/examples/evaluated_logarithm_functions/statement.lit");
const LOCAL: &str = include_str!("../../../lean/examples/evaluated_local_logarithms/statement.lit");

fn eval(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[index]
    else {
        panic!("successful eval")
    };
    p
}

#[test]
fn log_eval_replays_exact_values_functions_arithmetic_and_scope() {
    for source in [SOURCE, RATIONAL, ARITHMETIC, FUNCTIONS, LOCAL] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "log_eval").expect(source);
        assert_eq!(lean, compiler.compile_run(&run, "log_eval").unwrap());
        assert!(!lean.contains("sorry") && !lean.contains("admit"));
    }
}

#[test]
fn log_eval_rejects_wrong_evaluated_value() {
    let (mut run, compiler) = super::execute("eval log(8,4)");
    let proof = eval(&mut run, 0);
    let wrong = Obj::Literal(Literal::Number(Number::new("3".into())));
    proof.evaluated_object = wrong.clone();
    proof.evaluated_equal_fact.right = wrong;
    compiler
        .compile_run(&run, "wrong_log_value")
        .expect_err("wrong value");
}

#[test]
fn log_eval_requires_original_children_in_order() {
    for change in ["missing", "reordered"] {
        let (mut run, compiler) = super::execute("eval log(8,4)");
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ExpLogOperator(ExpLogOperatorObjWellDefinedProofByDef::Log(
                    wd,
                )),
            ..
        } = eval(&mut run, 0)
            .source_well_defined
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("log WD")
        };
        if change == "missing" {
            wd.child_obj_well_defined.pop();
        } else {
            wd.child_obj_well_defined.swap(0, 1);
        }
        compiler
            .compile_run(&run, "wrong_log_wd")
            .expect_err(change);
    }
}

#[test]
fn log_eval_keeps_native_domain_and_exactness_boundaries() {
    for source in ["eval log(1,2)", "eval log(2,0)"] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}
