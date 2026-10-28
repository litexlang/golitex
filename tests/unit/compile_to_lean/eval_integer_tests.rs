use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    IntegerOperatorObjWellDefinedProofByDef as WD, LcmObjWellDefinedProof,
};
use crate::execute::{ExecCommandStmtResult, ExecEvalStmtResult, ExecEvalStmtSuccess};
use crate::prelude::*;

const OPERATIONS: &str =
    include_str!("../../../lean/examples/evaluated_integer_operations/statement.lit");
const CITATIONS: &str =
    include_str!("../../../lean/examples/evaluated_integer_citations/statement.lit");
const FUNCTIONS: &str =
    include_str!("../../../lean/examples/evaluated_integer_functions/statement.lit");
const LOCAL: &str =
    include_str!("../../../lean/examples/evaluated_local_integer_operations/statement.lit");
const AGGREGATES: &str =
    include_str!("../../../lean/examples/evaluated_integer_aggregates/statement.lit");

fn eval(run: &mut RunLitexCodeResult, index: usize) -> &mut ExecEvalStmtSuccess {
    let ExecStmtResult::Command(ExecCommandStmtResult::Eval(ExecEvalStmtResult::Success(p))) =
        &mut run.statement_results[index]
    else {
        panic!("successful eval")
    };
    p
}

#[test]
fn integer_eval_replays_values_references_functions_and_scope() {
    for source in [OPERATIONS, CITATIONS, FUNCTIONS, LOCAL, AGGREGATES] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "integer_eval").expect(source);
        assert_eq!(lean, compiler.compile_run(&run, "integer_eval").unwrap());
        assert!(!lean.contains("sorry") && !lean.contains("admit"));
    }
}

#[test]
fn integer_eval_rejects_false_outputs_for_each_operator() {
    for source in [
        "eval gcd(54,-24)",
        "eval lcm(-6,15)",
        "eval (-7)%(-3)",
        "eval quot(-7,3)",
        "eval factorial(6)",
    ] {
        let (mut run, compiler) = super::execute(source);
        let p = eval(&mut run, 0);
        let wrong = Obj::Literal(Literal::Number(Number::new("99".into())));
        p.evaluated_object = wrong.clone();
        p.evaluated_equal_fact.right = wrong;
        compiler
            .compile_run(&run, "wrong_integer_value")
            .expect_err(source);
    }
}

#[test]
fn integer_eval_requires_original_ordered_children_and_constructor() {
    for change in ["missing", "reordered", "tag"] {
        let (mut run, compiler) = super::execute("eval gcd(12,18)");
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::IntegerOperator(wd),
            ..
        } = eval(&mut run, 0)
            .source_well_defined
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("integer WD")
        };
        let WD::Gcd(p) = wd else { panic!("gcd WD") };
        match change {
            "missing" => {
                p.child_obj_well_defined.pop();
            }
            "reordered" => p.child_obj_well_defined.swap(0, 1),
            _ => {
                *wd = WD::Lcm(LcmObjWellDefinedProof {
                    child_obj_well_defined: std::mem::take(&mut p.child_obj_well_defined),
                    requirement_fact_verified: std::mem::take(&mut p.requirement_fact_verified),
                })
            }
        }
        compiler
            .compile_run(&run, "wrong_integer_wd")
            .expect_err(change);
    }
}

#[test]
fn integer_eval_replays_divisor_guard_even_for_positive_quotient() {
    for source in ["eval (-7)%3", "eval quot(-7,3)"] {
        let (mut run, compiler) = super::execute(source);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::IntegerOperator(wd),
            ..
        } = eval(&mut run, 0)
            .source_well_defined
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("integer WD")
        };
        let guards = match wd {
            WD::Mod(p) => &mut p.requirement_fact_verified,
            WD::Quot(p) => &mut p.requirement_fact_verified,
            _ => panic!("division"),
        };
        assert_eq!(guards.len(), 1);
        guards.clear();
        compiler
            .compile_run(&run, "missing_divisor_guard")
            .expect_err(source);
    }
}

#[test]
fn integer_eval_does_not_replace_nonclosed_domain_evidence() {
    let (mut run, compiler) =
        super::execute("have factorial_input N = 4\neval factorial(factorial_input)");
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::IntegerOperator(WD::Factorial(p)),
        ..
    } = eval(&mut run, 1)
        .source_well_defined
        .as_detailed_mut()
        .unwrap()
    else {
        panic!("factorial WD")
    };
    assert!(!p.requirement_fact_verified.is_empty());
    p.requirement_fact_verified.clear();
    compiler
        .compile_run(&run, "missing_natural_membership")
        .expect_err("original domain");
}

#[test]
fn integer_eval_requires_the_recorded_numeric_citations() {
    for change in ["missing", "reordered", "self"] {
        let (mut run, compiler) = super::execute(CITATIONS);
        let p = eval(&mut run, 2);
        assert_eq!(p.cited_equal_fact_ids.len(), 2);
        match change {
            "missing" => p.cited_equal_fact_ids.clear(),
            "reordered" => p.cited_equal_fact_ids.swap(0, 1),
            _ => p.cited_equal_fact_ids[0] = p.evaluated_equal_fact.fact_id,
        }
        compiler
            .compile_run(&run, "wrong_integer_citations")
            .expect_err(change);
    }
}

#[test]
fn integer_eval_keeps_native_domain_boundaries() {
    for source in [
        "eval gcd(0,0)",
        "eval gcd(1/2,3)",
        "eval lcm(1/2,3)",
        "eval 7%0",
        "eval quot(7,0)",
        "eval quot(7,-3)",
        "eval factorial(-1)",
        "eval factorial(1/2)",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}
