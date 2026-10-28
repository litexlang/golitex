use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::DetailedObjWellDefinedProof;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    FunctionSpaceObjWellDefinedProofByDef, ObjWellDefinedProofByDef, VerifyObjWellDefinedResult,
};
use crate::execute::execute_have_fn_equal_stmt::ExecHaveFnEqualStmtResult;
use crate::execute::{ExecDefinitionStmtResult, ExecStmtResult};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;

fn runtime() -> Runtime {
    Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    )
}

fn check(rt: &mut Runtime, code: &str, expected: &[bool]) {
    let run = rt.run_litex_code(code).expect("parse and execute Litex");
    assert!(
        run.session_error.is_none(),
        "{code}\n{:?}",
        run.session_error
    );
    assert_eq!(
        run.statement_results
            .iter()
            .map(|s| !s.is_failed())
            .collect::<Vec<_>>(),
        expected,
        "{code}"
    );
    assert_eq!(run.success, expected.iter().all(|ok| *ok), "{code}");
    assert_eq!(rt.execution_environments_stack.len(), 1, "{code}");
}

#[test]
fn family_intersection_requires_nonempty_family_and_preserves_failed_scope() {
    let mut rt = runtime();
    check(&mut rt, "have unproved_family set", &[true]);
    for source in [
        "$is_set(family_intersect({}))",
        "$is_set(family_intersect(unproved_family))",
    ] {
        let run = rt.run_litex_code(source).unwrap();
        let ExecStmtResult::Fact(crate::execute::execute_fact_stmt::ExecFactStmtResult::Failed(
            proof,
        )) = &run.statement_results[0]
        else {
            panic!("expected a failed fact: {source}");
        };
        assert!(proof.is_wd_failed(), "failure must be WD, not proof search");
        assert!(!run.success && run.session_error.is_none());
    }
    check(
        &mut rt,
        "let rejected_intersection = family_intersect({})",
        &[false],
    );
    let missing = rt
        .run_litex_code("rejected_intersection = rejected_intersection")
        .unwrap();
    assert!(!missing.success);
    assert!(
        format!("{:?}{:?}", missing.session_error, missing.input_error)
            .contains("undefined name `rejected_intersection`")
    );
    check(
        &mut rt,
        include_str!("../../../../examples/wd/family_intersection_nonempty.lit"),
        &[true, true, true, true, true],
    );
}

#[test]
fn finite_extrema_require_real_elements_and_discard_failed_bindings() {
    for operator in ["finite_set_max", "finite_set_min"] {
        let mut rt = runtime();
        check(&mut rt, &format!("let bad = {operator}({{i}})"), &[false]);
        let run = rt.run_litex_code("bad = bad").unwrap();
        assert!(!run.success);
        assert!(format!("{:?}{:?}", run.session_error, run.input_error)
            .contains("undefined name `bad`"));
        check(
            &mut rt,
            &format!("{operator}({{i}}) = {operator}({{i}})"),
            &[false],
        );
        check(&mut rt, "0 = 1", &[false]);
    }
}

#[test]
fn ordered_fold_checks_each_argument_domain_and_retains_empty_ranges() {
    for source in [
        "$is_set(reduce(1,2,fn(k {1}) Z{k},fn(a,b Z) Z{a+b},0))",
        "$is_set(reduce(0,1,fn(k Z: k != 0) Z{k},fn(a,b Z) Z{a+b},0))",
    ] {
        check(&mut runtime(), source, &[false]);
    }
    for source in [
        "$is_set(reduce(1,3,fn(k Z) Z{k},fn(a,b Z) Z{a-b},0))",
        "$is_set(reduce(-1,-2,fn(k N) N{k},fn(a,b N) N{a+b},0))",
        "$is_set(reduce(1,0,fn(k Z: k != 0) Z{k},fn(a,b Z) Z{a+b},7))",
    ] {
        check(&mut runtime(), source, &[true]);
    }
}

#[test]
fn finite_extrema_preserve_real_aliases_and_checked_set_domains() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(include_str!(
            "../../../../examples/wd/finite_extrema_real_carrier.lit"
        ))
        .unwrap();
    assert!(run.success, "{:?}", run.session_error);
    assert!(run.session_error.is_none());
}

#[test]
fn finite_extrema_preserve_empty_and_infinite_set_rejections() {
    for operator in ["finite_set_max", "finite_set_min"] {
        for set in ["{}", "R"] {
            check(
                &mut runtime(),
                &format!("let bad = {operator}({set})"),
                &[false],
            );
        }
    }
}

#[test]
fn finite_set_fold_preserves_valid_domain_literals_and_named_iterands() {
    let mut rt = runtime();
    let mut result = rt
        .run_litex_code(include_str!(
            "../../../../examples/wd/finite_set_fold_domain.lit"
        ))
        .unwrap();
    result.attach_normal_json(&rt, "eval", None);
    assert!(result.success, "{}", result.normal_json.as_deref().unwrap());
    assert!(result.session_error.is_none());
}

#[test]
fn finite_set_fold_requires_iterand_domain_and_predicate_coverage() {
    for function in ["fn(x {2}) Z {x}", "fn(x Z: x > 0) Z {x}"] {
        let mut rt = runtime();
        check(
            &mut rt,
            &format!(
                "let bad = finite_set_reduce({{0, 1}}, {function}, fn(a, b Z) Z {{a + b}}, 0)"
            ),
            &[false],
        );
        let result = rt.run_litex_code("bad = bad").unwrap();
        assert!(!result.success);
        assert!(
            format!("{:?}{:?}", result.session_error, result.input_error)
                .contains("undefined name `bad`")
        );
        check(&mut rt, "0 = 1", &[false]);
    }
}

#[test]
fn invalid_function_returns_fail_before_their_signature_can_prove_false_membership() {
    for definition in ["have fn f(x Z) N = x", "let f = fn(x Z) N {x}"] {
        let mut rt = runtime();
        check(&mut rt, definition, &[false]);
        check(&mut rt, "(-1) $in N\n-1 >= 0", &[false, false]);
        let run = rt.run_litex_code("f(-1) = -1").unwrap();
        assert!(!run.success);
        assert!(
            format!("{:?}{:?}", run.session_error, run.input_error).contains("undefined name `f`")
        );
    }
    check(
        &mut runtime(),
        "have fn f(x N, y Z) N = y\n(-1) $in N",
        &[false, false],
    );
    check(&mut runtime(), "fn(x Z) N {x}(-1) = -1", &[false]);
    check(&mut runtime(), "have fn f(x Z) N = -1", &[false]);
    check(
        &mut runtime(),
        "have fn f(x Z) N by cases:\n    case x = x: x",
        &[false],
    );
}

#[test]
fn valid_projection_returns_use_parameter_types_and_checked_domain_conditions() {
    for source in [
        "have fn f(x Z) Z = x\nf(-1) = -1",
        "have fn f(x N) Z = x\nf(0) = 0",
        "let f = fn(x Z) Z {x}\nf(-1) = -1",
        "have fn f(x R) R = x\nf(2) $in {2}",
        "have fn f(x Z, y N) N = y\nf(-1, 0) = 0",
    ] {
        check(&mut runtime(), source, &[true, true]);
    }
    check(
        &mut runtime(),
        "have fn f(x Z: x >= 0) N = x\nf(0) = 0\nf(-1) = -1",
        &[true, true, false],
    );
}

#[test]
fn struct_instances_require_concrete_argument_types_including_kind_and_dependent_domains() {
    let box_def = "struct Box<n N>:\n    value R\n    tag R\n";
    for bad_use in [
        "let bad = &Box<(-1)>",
        "&Box<(-1)> = &Box<(-1)>",
        "have fn f(x &Box<(-1)>) R = 0",
        "forall p &Box<(-1)>:\n    p = p",
        "let bad = &Box<1 / 0>",
        "let bad = &Box<0, 1>",
    ] {
        check(
            &mut runtime(),
            &format!("{box_def}{bad_use}\n(-1) $in N"),
            &[true, false, false],
        );
    }
    for (kind, bad_arg) in [("nonempty_set", "{}"), ("finite_set", "N")] {
        check(
            &mut runtime(),
            &format!("struct Pair<S {kind}>:\n    left S\n    right S\nlet bad = &Pair<{bad_arg}>"),
            &[true, false],
        );
    }
    check(
        &mut runtime(),
        "struct Pair<S set, a S>:\n    left S\n    right S\nlet bad = &Pair<{0}, 1>",
        &[true, false],
    );
}

#[test]
fn valid_struct_header_arguments_remain_well_defined() {
    check(
        &mut runtime(),
        "struct Box<n N>:\n    value R\n    tag R\nlet good = &Box<0>\n&Box<0> = &Box<0>",
        &[true, true, true],
    );
    for (kind, good_arg) in [
        ("set", "R"),
        ("set", "0"),
        ("nonempty_set", "{0}"),
        ("finite_set", "{0}"),
    ] {
        check(
            &mut runtime(),
            &format!(
                "struct Pair<S {kind}>:\n    left S\n    right S\nlet good = &Pair<{good_arg}>"
            ),
            &[true, true],
        );
    }
    check(
        &mut runtime(),
        "struct Pair<S set, a S>:\n    left S\n    right S\nlet good = &Pair<{0}, 0>",
        &[true, true],
    );
}

#[test]
fn failed_domain_checks_leave_no_function_binding_struct_binding_or_wd_cache() {
    let mut rt = runtime();
    check(&mut rt, "have fn f(x Z) N = x", &[false]);
    check(
        &mut rt,
        "have fn f(x Z) Z = x\nf(-1) = -1\n(-1) $in N",
        &[true, true, false],
    );
    check(&mut rt, "struct Box<n N>:\n    value R\n    tag R", &[true]);
    check(&mut rt, "let item = &Box<(-1)>", &[false]);
    check(&mut rt, "let item = &Box<0>", &[true]);
    check(
        &mut rt,
        "&Box<(-1)> = &Box<(-1)>\n(-1) $in N\n-1 >= 0",
        &[false, false, false],
    );
}

#[test]
fn wd_evidence_and_detailed_json_keep_mandatory_return_and_argument_type_proofs() {
    let mut rt = runtime();
    let run = rt.run_litex_code("have fn f(x Z) Z = x").unwrap();
    assert!(run.success && run.session_error.is_none());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
        ExecHaveFnEqualStmtResult::Success(success),
    )) = &run.statement_results[0]
    else {
        panic!("function definition success");
    };
    let Some(DetailedObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::FunctionSpace(FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(
                proof,
            )),
        ..
    }) = (&success.anonymous_fn_well_defined)
        .as_detailed_success()
        .unwrap()
    else {
        panic!("anonymous function WD evidence");
    };
    let crate::execute::execute_fact_stmt::well_defined_results::verify_obj::AnonymousFnBodyInReturnSetProof::CheckedMembership(return_proof) = &proof.body_in_ret_set
        else { panic!("nonempty integer domain must retain a checked return membership"); };
    assert!(!return_proof.is_failed());
    let json =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(json.contains("body_in_ret_set"), "{json}");
    check(&mut rt, "struct Box<n N>:\n    value R\n    tag R", &[true]);
    let run = rt.run_litex_code("let good = &Box<0>").unwrap();
    assert!(run.success && run.session_error.is_none());
    let json =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(
        json.contains("requirement_fact_verified") && json.contains("0 $in N"),
        "{json}"
    );
    let run = rt.run_litex_code("let bad = &Box<(-1)>").unwrap();
    assert!(!run.success && run.session_error.is_none());
    let json =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(
        json.contains("requirement") && json.contains("(-1) $in N"),
        "{json}"
    );
}

#[test]
fn run_examples_wd_return_and_struct_domains() {
    let source = include_str!("../../../../examples/wd/obj/return_and_struct_domains.lit");
    let mut rt = runtime();
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.success && run.session_error.is_none(),
        "{source}\n{:?}",
        run.session_error
    );
}
