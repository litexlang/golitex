use super::LitexToLeanCompiler;
use crate::prelude::*;

fn execute(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new(
        parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap(),
    );
    let run = runtime.run_litex_code(source).unwrap();
    assert!(run.success);
    (run, LitexToLeanCompiler::new(runtime))
}

fn compile(source: &str) -> String {
    let (run, compiler) = execute(source);
    let lean = compiler.compile_run(&run, "finite_statistics").unwrap();
    assert_eq!(
        lean,
        compiler.compile_run(&run, "finite_statistics").unwrap()
    );
    lean
}

fn equality(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[0] else {
        panic!()
    };
    let VerifyFactResult::Equality(p) = &mut p.verify_result else {
        panic!()
    };
    let VerifyEqualityResult::Success(p) = p.as_mut() else {
        panic!()
    };
    p
}

#[test]
fn finite_set_size_literal_replays_wd_and_calculation() {
    let lean = compile("finite_set_size({1, 2}) = 2\nfinite_set_size({}) = 0\n");
    assert!(lean.contains("Litex.finiteSetSize") && lean.contains("Litex.finiteCardInsert"));
}

#[test]
fn finite_set_size_symbolic_finite_parameter() {
    compile("forall S set:\n    $is_finite_set(S)\n    =>:\n        finite_set_size(S) $in N\n        finite_set_size(S) >= 0\n");
}

#[test]
fn finite_extrema_literal_selection() {
    compile("finite_set_max({-3, 2, 7}) = 7\nfinite_set_min({-3, 2, 7}) = -3\n");
}

#[test]
fn finite_set_parameter_kind() {
    compile("forall S finite_set => finite_set_size(S) >= 0\n");
}

#[test]
fn finite_extrema_bounds_and_membership() {
    compile("forall S finite_set, x S:\n    $is_nonempty_set(S)\n    S $subset R\n    =>:\n        finite_set_min(S) <= x\n        x <= finite_set_max(S)\n        finite_set_max(S) $in S\n");
}

#[test]
fn finite_extrema_reject_missing_or_reordered_domain_evidence() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FiniteSetStatObjWellDefinedProofByDef as P;
    for remove in 0..4 {
        let (mut run, compiler) = execute("finite_set_max({-3, 2, 7}) = 7\n");
        let ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FiniteSetStat(P::FiniteSetMax(p)),
            ..
        } = &mut equality(&mut run).well_defined_proof.left
        else {
            panic!()
        };
        if remove < 3 {
            p.requirement_fact_verified.remove(remove);
        } else {
            p.requirement_fact_verified.swap(0, 2);
        }
        assert!(compiler.compile_run(&run, "missing_domain").is_err());
    }
}

#[test]
fn finite_size_rejects_missing_finiteness() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FiniteSetStatObjWellDefinedProofByDef as P;
    let (mut run, compiler) = execute("finite_set_size({1, 2}) = 2\n");
    let ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FiniteSetStat(P::FiniteSetSize(p)),
        ..
    } = &mut equality(&mut run).well_defined_proof.left
    else {
        panic!()
    };
    p.requirement_fact_verified.clear();
    assert!(compiler.compile_run(&run, "missing_finite").is_err());
}

#[test]
fn finite_extrema_rejects_changed_selection_and_comparison() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_scalar_identities::ScalarIdentityBuiltinRuleProof as P;
    for wrong_index in [true, false] {
        let (mut run, compiler) = execute("finite_set_max({-3, 2, 7}) = 7\n");
        let EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::ScalarIdentity(P::FiniteSetMaxSelection(p)),
        ) = &mut equality(&mut run).searched_proof
        else {
            panic!()
        };
        if wrong_index {
            p.selected_index = 0;
        } else {
            p.comparisons[0].ordering = crate::rational_expression::NumberCompareResult::Greater;
        }
        assert!(compiler.compile_run(&run, "changed_certificate").is_err());
    }
}

#[test]
fn finite_extrema_reject_empty_or_complex_source() {
    for source in ["finite_set_max({}) = 0", "finite_set_min({i}) = 0"] {
        let mut runtime = Runtime::new(
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap(),
        );
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success);
        assert!(LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_domain")
            .is_err());
    }
}

#[test]
fn finite_stat_nested_arithmetic_and_rational_selection() {
    compile("finite_set_max({1 / 3, 1 / 2}) = 1 / 2\nfinite_set_size({1, 2, 3}) + 1 = 4\n");
}

#[test]
fn finite_set_parameter_theorem_call() {
    compile("thm cardinality_natural:\n    ? forall A finite_set => finite_set_size(A) $in N\n    finite_set_size(A) $in N\nby thm cardinality_natural({3, 5}) => finite_set_size({3, 5}) $in N\n");
}
