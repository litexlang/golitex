use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
use crate::execute::{ExecReleaseAndExpandStmtResult, ExecStmtResult};
use crate::json_output::project_stmt_detailed;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn fact_count(rt: &Runtime) -> usize {
    rt.execution_environments_stack
        .iter()
        .map(|env| env.facts.facts_by_id.len())
        .sum()
}
fn fixture(name: &str, negative: bool) -> String {
    let directory = if negative {
        "examples/wd_negative"
    } else {
        "examples/stmt_nodes/release_and_expand/builtin_thm"
    };
    std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join(directory)
            .join(format!("{name}.lit")),
    )
    .unwrap()
}
fn execute(rt: &mut Runtime, source: &str) -> ExecStmtResult {
    let blocks = Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let stmts = rt.parse(&blocks).unwrap();
    assert_eq!(stmts.len(), 1);
    rt.exec_stmt(&stmts[0]).unwrap()
}

const POSITIVE: &[&str] = &[
    "real_least_upper_bound_from_definition",
    "real_greatest_lower_bound_from_definition",
    "real_least_upper_bound_upper_bound",
    "real_greatest_lower_bound_lower_bound",
    "real_least_upper_bound_unique",
    "real_greatest_lower_bound_unique",
    "real_least_upper_bound_crosses",
    "real_greatest_lower_bound_crosses",
];

#[test]
fn all_real_bound_contracts_have_checked_standalone_tracers() {
    for name in POSITIVE {
        let id = BuiltinTheoremId::from_name(name).unwrap();
        assert_eq!(id.as_str(), *name);
        let mut rt = runtime();
        let result = rt.run_litex_code(&fixture(name, false)).unwrap();
        assert!(
            result.success && result.session_error.is_none(),
            "{name}\n{}",
            crate::json_output::emit_run_detailed(&result, &rt, "test", None)
        );
    }
}

#[test]
fn false_extrema_empty_sets_and_missing_certificates_roll_back() {
    for name in [
        "real_bounds_bad_lub_candidate",
        "real_bounds_bad_glb_candidate",
        "real_bounds_empty_lub",
        "real_bounds_empty_glb",
        "real_bounds_missing_certificate",
        "real_bounds_not_crossed",
    ] {
        let mut rt = runtime();
        assert!(!execute(&mut rt, "have anchor R=7").is_failed());
        let code = fixture(name, true);
        let blocks = Tokenizer::new()
            .tokenize(&code, rt.current_file.clone())
            .unwrap();
        let stmts = rt.parse(&blocks).unwrap();
        for stmt in &stmts[..stmts.len() - 1] {
            assert!(!rt.exec_stmt(stmt).unwrap().is_failed(), "{name}");
        }
        let before = fact_count(&rt);
        let failed = rt.exec_stmt(stmts.last().unwrap()).unwrap();
        assert!(failed.is_failed(), "{name}");
        assert_eq!(
            fact_count(&rt),
            before,
            "{name}: failed theorem leaked facts"
        );
        assert!(!execute(&mut rt, "anchor+1=8").is_failed(), "{name}");
    }
}

#[test]
fn real_bound_definition_retains_both_quantified_obligations() {
    let mut rt = runtime();
    let setup = "forall u R:\n    forall x {0}:\n        x<=u\n    =>:\n        0<=u";
    assert!(rt.run_litex_code(setup).unwrap().success);
    let result = execute(
        &mut rt,
        "release thm real_least_upper_bound_from_definition({0},0)",
    );
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(ref success),
    )) = result
    else {
        panic!("expected bound proof")
    };
    assert_eq!(
        success.builtin.as_ref().unwrap().theorem,
        BuiltinTheoremId::RealLeastUpperBoundFromDefinition
    );
    assert_eq!(success.dom_proofs.len(), 5);
    assert_eq!(success.conclusions_wd.len(), 1);
    let output = project_stmt_detailed(&result, &rt).stringify();
    assert!(
        output.contains("requirements")
            && output.contains("conclusions_wd")
            && output.contains("forall")
            && output.contains("real_least_upper_bound_from_definition")
    );
}

#[test]
fn real_bound_contracts_reject_wrong_arity_and_invalid_carriers() {
    for code in [
        "release thm real_least_upper_bound_from_definition({0})",
        "release thm real_greatest_lower_bound_from_definition({i},0)",
        "release thm real_least_upper_bound_unique({0},0,1)",
        "release thm real_greatest_lower_bound_unique({0},0,1)",
        "release thm real_greatest_lower_bound_crosses({0},0,i)",
    ] {
        let mut rt = runtime();
        let before = fact_count(&rt);
        assert!(execute(&mut rt, code).is_failed(), "{code}");
        assert_eq!(fact_count(&rt), before, "{code}");
    }
}
