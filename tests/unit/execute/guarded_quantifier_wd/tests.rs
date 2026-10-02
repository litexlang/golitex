use crate::execute::execute_def_prop_stmt::ExecDefPropStmtResult;
use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::execute::{ExecDefinitionStmtResult, ExecStmtResult};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn check(rt: &mut Runtime, code: &str, expected: &[bool]) -> Vec<ExecStmtResult> {
    let result = rt
        .run_litex_code(code)
        .expect("parse and execute through exec_stmt");
    assert!(
        result.session_error.is_none(),
        "{code}: {:?}",
        result.session_error
    );
    assert_eq!(
        result
            .statement_results
            .iter()
            .map(|r| !r.is_failed())
            .collect::<Vec<_>>(),
        expected,
        "{code}"
    );
    assert_eq!(
        rt.execution_environments_stack.len(),
        1,
        "local proof scopes must close"
    );
    result.statement_results
}

#[test]
fn guarded_quantifier_wd_accepts_definitions_and_claim_before_proof() {
    check(
        &mut runtime(),
        include_str!("../../../../examples/wd/fact/guarded_quantifier_domains.lit"),
        &[true, true, true],
    );
}

#[test]
fn guarded_quantifier_wd_retains_stages_and_local_guard_evidence() {
    let mut rt = runtime();
    for (source, iff) in [
        ("prop guarded(x R):\n    not forall y R:\n        y != 0\n        =>:\n            1 / y != 1 / y\n", false),
        ("prop guarded_iff(x R):\n    forall y R:\n        y != 0\n        =>:\n            1 / y = 1 / y\n        <=>:\n            1 / y = 1 / y\n", true),
    ] {
        let results = check(&mut rt, source, &[true]);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(ExecDefPropStmtResult::Success(s))) = &results[0] else { panic!("definition success") };
        match (&s.iff_fact_well_defined[0], iff) {
            (FactWellDefinedProof::NotForall(p), false) => {
                assert_eq!((p.param_type_well_defined.len(), p.dom.len(), p.then.len()), (1, 1, 1));
                assert!(!p.local_env.well_defined_objects.object_to_wd_id.is_empty());
            }
            (FactWellDefinedProof::ForallFactWithIff(p), true) => {
                assert_eq!((p.param_type_well_defined.len(), p.dom.len(), p.then.len(), p.iff.len()), (1, 1, 1, 1));
                assert!(!p.local_env.well_defined_objects.object_to_wd_id.is_empty());
            }
            _ => panic!("independent quantified WD evidence must be retained"),
        }
    }
    check(
        &mut rt,
        "have y R\ny != 0\n1 / y = 1 / y\n0 = 1",
        &[true, false, false, false],
    );
}

#[test]
fn guarded_quantifier_wd_checks_each_guard_before_staging_it() {
    for quantifier in ["not forall", "forall"] {
        let source = format!("prop bad(x R):\n    {quantifier} y R:\n        1 / y = 1 / y\n        y != 0\n        =>:\n            1 / y != 1 / y\n{}", if quantifier == "forall" { "        <=>:\n            y = y\n" } else { "" });
        let mut rt = runtime();
        check(&mut rt, &source, &[false]);
        check(&mut rt, "prop bad(x R):\n    x = x\n", &[true]);
        check(
            &mut rt,
            "have y R\ny != 0\n1 / y = 1 / y",
            &[true, false, false],
        );
    }
}

#[test]
fn guarded_quantifier_wd_supports_later_domains_without_proving_conclusions() {
    for suffix in ["not forall", "forall"] {
        let source = format!("prop guarded(x R):\n    {suffix} y R:\n        y != 0\n        1 / y = 1 / y\n        =>:\n            1 / y != 1 / y\n{}", if suffix == "forall" { "        <=>:\n            y = y\n" } else { "" });
        let mut rt = runtime();
        check(&mut rt, &source, &[true]);
        check(&mut rt, "0 = 1", &[false]);
    }
}

#[test]
fn guarded_quantifier_wd_keeps_missing_zero_and_cross_branch_guards_invalid() {
    for source in [
        include_str!("../../../../examples/wd_negative/quantifier_domain_missing.lit"),
        include_str!("../../../../examples/wd_negative/quantifier_domain_zero.lit"),
        include_str!("../../../../examples/wd_negative/quantifier_domain_iff_cross_assumption.lit"),
        "prop bad(x R):\n    forall y R:\n        y = y\n        =>:\n            1 / y = 1 / y\n        <=>:\n            y != 0\n",
        "prop bad(x R):\n    not forall y R:\n        y = y\n        =>:\n            y != 0\n            1 / y != 1 / y\n",
    ] {
        let mut rt = runtime();
        check(&mut rt, source, &[false]);
        check(&mut rt, "0 = 1", &[false]);
    }
}
