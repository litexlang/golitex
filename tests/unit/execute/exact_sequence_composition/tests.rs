//! Exact space aliases transport checked memberships; returned spaces retain
//! call layers, guards and the carrier equality used by application WD.

use crate::execute::ExecStmtResult;
use crate::json_output::{emit_run_detailed, project_stmt_detailed};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(), session: false, strict: true,
        language: OutputLanguage::English,
    })
}

fn execute(rt: &mut Runtime, source: &str) -> ExecStmtResult {
    let blocks = Tokenizer::new().tokenize(source, rt.current_file.clone()).unwrap();
    let statements = rt.parse(&blocks).unwrap();
    assert_eq!(statements.len(), 1);
    rt.exec_stmt(&statements[0]).unwrap()
}

fn fact_count(rt: &Runtime) -> usize {
    rt.execution_environments_stack.iter().map(|env| env.facts.facts_by_id.len()).sum()
}

#[test]
fn exact_function_sequence_space_aliases_and_return_applications_keep_checked_sources() {
    for source in [
        "have Carrier set=finite_seq(R,2)\nhave f Carrier\nf(1) $in R\nf(2) $in R",
        "have Base set=finite_seq(Z,2)\nhave Carrier set=Base\nhave f Carrier\nhave g Carrier=f\ng(1) $in Z\ng(1) $in R\ng $in finite_seq(R,2)\ng(2) $in Z",
        "have Carrier set=seq(Z)\nhave f Carrier\nf(1) $in Z\nf(100) $in R",
        "have Base set=fn(k N+: k<=2) Z\nhave Carrier set=Base\nhave f Carrier\nf(1) $in Z\nf(2) $in Z",
        "have length N+\nhave Carrier set=finite_seq(R,length)\nhave f Carrier\nf(length) $in R",
        "have Carrier set=finite_seq(R,0)\nhave f Carrier\nf $in fn(k closed_range(1,0)) R",
        "have Carrier set=finite_seq(R,2)\nhave f Carrier\n$is_set(fn_range(f))\nf(1) $in fn_range(f)",
        "have fn mk(x R) finite_seq(R,2)=(x,x)\nmk(7)(1) $in R\nmk(7)(2) $in R",
        "have Carrier set=finite_seq(Z,2)\nhave fn mk(x R) Carrier=(2,2)\nmk(7)(1) $in Z\nmk(7)(2) $in R",
        "have Base set=seq(R)\nhave Carrier set=Base\nhave fn mk(x R) Carrier=fn(k N+) R {x}\nmk(7)(10) $in R",
        "have Carrier set=fn(k N+: k<=2) R\nhave fn mk(x R) Carrier=fn(k N+: k<=2) R {x}\nmk(7)(2) $in R",
        "have fn mk(x R: x>0) finite_seq(R,2)=(x,x)\nmk(7)(2) $in R",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none(), "{source}\n{}",
            emit_run_detailed(&run, &rt, "exact-sequence-composition", None));
        assert!(run.statement_results.iter().all(|stmt| !stmt.is_failed()));
    }

    // The input carrier equality is a real WD requirement for the second
    // layer, rather than an unrecorded signature lookup side effect.
    let mut rt = runtime();
    assert!(rt.run_litex_code("have Carrier set=finite_seq(Z,2)\nhave fn mk(x R) Carrier=(2,2)").unwrap().success);
    let result = execute(&mut rt, "mk(7)(2) $in Z");
    assert!(!result.is_failed());
    let detailed = format!("{:?}", project_stmt_detailed(&result, &rt));
    assert!(detailed.contains("Carrier = finite_seq"), "missing return carrier equality: {detailed}");
    assert!(detailed.contains("cite_fact_id"), "missing stored source citation: {detailed}");
}

#[test]
fn exact_function_sequence_alias_controls_reject_wrong_domains_calls_and_publication() {
    for (setup, target) in [
        ("have Carrier set=finite_seq(R,2)\nhave f Carrier", "f(3) $in R"),
        ("have Carrier set=finite_seq(R,2)\nhave f Carrier", "f(0) $in R"),
        ("have Carrier set=finite_seq(R,2)\nhave f Carrier", "f(1/2) $in R"),
        ("have Carrier set=finite_seq(R,2)\nhave f Carrier", "f(1,2) $in R"),
        ("have Carrier set=finite_seq(R,2)\nhave f Carrier", "f(1) $in Z"),
        ("have Carrier set=finite_seq(R,0)\nhave f Carrier", "f(1) $in R"),
        ("have Carrier set=seq(R)\nhave f Carrier", "f(0) $in R"),
        ("have Base set=fn(k N+: k<=2) R\nhave Carrier set=Base\nhave f Carrier", "f(3) $in R"),
        ("have Space set=finite_seq(R,2)", "Space(1) $in R"),
        ("have Space set=seq(R)", "Space(1) $in R"),
        ("have Space set=fn(k closed_range(1,2)) R", "Space(1) $in R"),
        ("have Carrier set=finite_seq(R,2)\nhave fn z(k N+) R=0", "release thm fn_set_member(z,Carrier)"),
        ("have fn mk(x R) finite_seq(R,2)=(x,x)", "mk(7)(3) $in R"),
        ("have fn mk(x R: x>0) finite_seq(R,2)=(x,x)", "mk(0)(2) $in R"),
        ("have fn mk(x R) R=x", "mk(7)(1) $in R"),
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(setup).unwrap();
        assert!(run.success && run.session_error.is_none(), "{setup}\n{}",
            emit_run_detailed(&run, &rt, "exact-sequence-control-setup", None));
        let before = fact_count(&rt);
        assert!(execute(&mut rt, target).is_failed(), "false target: {setup}\n{target}");
        assert_eq!(fact_count(&rt), before, "failed target published facts: {target}");
    }
}
