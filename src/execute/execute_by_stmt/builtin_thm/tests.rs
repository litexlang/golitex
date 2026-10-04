use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::{ExecReleaseAndExpandStmtResult, ExecStmtResult};
use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
use crate::json_output::{project_stmt_normal, project_stmt_detailed};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language: OutputLanguage::English })
}
fn execute(rt: &mut Runtime, code: &str) -> ExecStmtResult {
    let blocks = Tokenizer::new().tokenize(code, rt.current_file.clone()).unwrap();
    let mut stmts = rt.parse(&blocks).unwrap();
    assert_eq!(stmts.len(), 1, "{code}");
    rt.exec_stmt(&stmts.remove(0)).unwrap()
}
fn count_facts(rt: &Runtime) -> usize {
    rt.execution_environments_stack.iter().map(|env| env.facts.facts_by_id.len()).sum()
}

#[test]
fn builtin_theorem_catalogue_has_twenty_nine_native_tracers() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/stmt_nodes/release_and_expand/builtin_thm");
    let mut count = 0;
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|x| x.to_str()) != Some("lit") { continue; }
        let name = path.file_stem().unwrap().to_str().unwrap();
        let id = BuiltinTheoremId::from_name(name).expect("each file names a builtin theorem");
        assert_eq!(id.as_str(), name);
        let code = std::fs::read_to_string(&path).unwrap();
        let mut rt = runtime();
        let result = rt.run_litex_code(&code).unwrap();
        assert!(result.session_error.is_none() && result.success, "{}\n{}", path.display(), crate::json_output::emit_run_detailed(&result, &rt, "test", None));
        count += 1;
    }
    assert_eq!(count, 29);
}

#[test]
fn finite_set_reduce_singleton_checks_set_carrier_laws_and_rollback() {
    for code in [
        "release thm finite_set_reduce_singleton(finite_set_reduce({2}, fn(x Z) Z{x}, fn(a,b Z) Z{a+b}, 0), 2)",
        "release thm finite_set_reduce_singleton(finite_set_reduce({1/2}, fn(x Q) Q{x}, fn(a,b Q) Q{a*b}, 3), 1/2)",
        "have S finite_set = {2}\nrelease thm finite_set_reduce_singleton(finite_set_reduce(S, fn(x Z) Z{x}, fn(a,b Z) Z{a+b}, 7), 2)",
    ] {
        let mut rt = runtime();
        let result = rt.run_litex_code(code).unwrap();
        assert!(result.success && result.session_error.is_none(), "{code}\n{}", crate::json_output::emit_run_detailed(&result, &rt, "test", None));
        let detailed = project_stmt_detailed(result.statement_results.last().unwrap(), &rt);
        let serialized = format!("{detailed:?}");
        assert!(serialized.contains("finite_set_reduce_singleton"));
        assert!(serialized.contains("well_defined"));
    }
    for code in [
        "release thm finite_set_reduce_singleton(finite_set_reduce({1,2}, fn(x Z) Z{x}, fn(a,b Z) Z{a+b}, 0), 1)",
        "release thm finite_set_reduce_singleton(finite_set_reduce({2}, fn(x Z) Z{x}, fn(a,b Z) Z{a+b}, 0), 3)",
        "release thm finite_set_reduce_singleton(finite_set_reduce({}, fn(x Z) Z{x}, fn(a,b Z) Z{a+b}, 0), 2)",
        "release thm finite_set_reduce_singleton(finite_set_reduce({2}, fn(x Z) Z{x}, fn(a,b Z) Z{a-b}, 0), 2)",
        "release thm finite_set_reduce_singleton(finite_set_reduce({2}, fn(x Z) Z{x}, fn(a,b Z) Z{a+b}, 1/2), 2)",
        "release thm finite_set_reduce_singleton(2, 2)",
        "release thm finite_set_reduce_singleton(2)",
    ] {
        let mut rt = runtime();
        let before = count_facts(&rt);
        assert!(execute(&mut rt, code).is_failed(), "{code}");
        assert_eq!(count_facts(&rt), before, "rejected singleton theorem must not publish facts");
    }
}

#[test]
fn intersection_contracts_reject_missing_fibers_empty_family_and_bad_shapes() {
    for code in [
        "release thm family_intersect_member(2, family_intersect({{1}}))",
        "release thm family_intersect_member(1, family_intersect({}))",
        "release thm family_intersect_member(1, family_intersect({1}))",
        "release thm family_intersect_member_facts(2, family_intersect({{1}}))",
        "release thm family_intersect_member_facts(1, family_intersect({}))",
        "release thm family_intersect_member(1, N)",
        "release thm index_intersect_member(2, index_intersect({1}, N, fn(k {1}) power_set(N) {{1}}))",
        "release thm index_intersect_member(1, index_intersect({}, N, fn(k {}) power_set(N) {{1}}))",
        "release thm index_intersect_member(1, index_intersect({2}, N, fn(k {1}) power_set(N) {{1}}))",
    ] {
        let mut rt = runtime();
        let before = count_facts(&rt);
        let result = execute(&mut rt, code);
        assert!(result.is_failed(), "{code}");
        assert_eq!(count_facts(&rt), before, "failed contract must not publish facts");
    }
}

#[test]
fn literal_tuple_extensionality_checks_all_coordinates_and_dimension() {
    for code in [
        "have a cart({1}, {2})\nrelease thm tuple_equal_from_coordinates(a, (1, 2))",
        "have a cart({1}, {2})\nrelease thm tuple_equal_from_coordinates((1, 2), a)",
        "have a cart({1}, {2}, {3})\nrelease thm tuple_equal_from_coordinates(a, (1, 2, 3))",
    ] {
        let mut rt = runtime();
        let result = rt.run_litex_code(code).unwrap();
        assert!(result.success && result.session_error.is_none(), "{code}\n{}", crate::json_output::emit_run_detailed(&result, &rt, "test", None));
    }
    for code in [
        "have a cart({1}, {2})\nrelease thm tuple_equal_from_coordinates(a, (1, 3))",
        "have a cart({1}, {2}, {3})\nrelease thm tuple_equal_from_coordinates(a, (1, 2))",
        "have a cart({1}, {2}, {3})\nrelease thm tuple_equal_from_coordinates(a, (1, 2, 4))",
        "have a cart({1}, {2})\nrelease thm tuple_equal_from_coordinates((1, 3), a)",
    ] {
        let mut rt = runtime();
        let result = rt.run_litex_code(code).unwrap();
        assert!(!result.success && result.session_error.is_none(), "false tuple equality: {code}");
    }
}

#[test]
fn builtin_theorem_failures_expose_premise_arity_shape_and_lookup() {
    for (code, phase, goal) in [
        ("release thm subset_of_finite_set_is_finite({2}, {1})", "premise", "{2} $subset {1}"),
        ("release thm rational_between_reals(1, 0)", "premise", "1 < 0"),
        ("release thm fn_set_member(1, R)", "call_shape", "function or sequence set"),
        ("release thm rational_between_reals(1)", "arity", "rational_between_reals"),
        ("release thm missing_theorem", "lookup", "missing_theorem"),
    ] {
        let mut rt = runtime();
        let before = count_facts(&rt);
        let result = execute(&mut rt, code);
        assert!(result.is_failed(), "{code}");
        assert_eq!(count_facts(&rt), before, "failed theorem must roll back");
        for json in [project_stmt_normal(&result, &rt), project_stmt_detailed(&result, &rt)] {
            let text = json.stringify();
            assert!(text.contains(phase) && text.contains(goal), "{code}: {text}");
        }
    }
}

#[test]
fn builtin_theorems_do_not_certify_missing_premises_or_bad_shapes() {
    for code in [
        "release thm fn_set_member(fn(x R) R {x}, fn(y R) N)",
        "release thm set_builder_member(-1, {x R: x > 0})",
        "release thm set_builder_member(1, R)",
        "release thm defined_set_member(1, R)",
        "release thm struct_member(1, R)",
        "release thm cart_member_from_coordinates((1, 2), cart(R, {3}))",
        "release thm index_cart_member(1, R)",
        "release thm index_cart_nonempty_by_choice_from_family(index_cart({1}, {{}, {1}}, fn(k {1}) {{}, {1}} {{1}}))",
        "release thm index_cart_nonempty_by_choice_from_pointwise(index_cart({1}, {{}, {1}}, fn(k {1}) {{}, {1}} {{}}))",
        "release thm sum_le_sum_from_pointwise(sum(1, 2, fn(x Z) R {x + 1}), sum(1, 2, fn(y Z) R {y}))",
        "release thm finite_set_sum_le_from_pointwise(finite_set_sum({1}, fn(x {1}) R {2}), finite_set_sum({1}, fn(y {1}) R {1}))",
        "release thm finite_set_summand_le_sum(1, finite_set_sum({1}, fn(x {1}) R {x}))",
        "release thm tuple_equal_from_coordinates((1, 2), (1, 3))",
        "release thm finite_set_sum_substitution(finite_set_sum({1}, fn(x {1}) R {2}), finite_set_sum({1}, fn(y {1}) R {1}))",
        "release thm sum_over_bijective_finite_set_enumerations(1, 2)",
        "release thm rational_has_unique_reduced_fraction(i)",
        "release thm subset_of_finite_set_is_finite({2}, {1})",
        "release thm finite_set_has_bijective_index(R)",
        "release thm real_least_upper_bound_exists({}, 0)",
        "release thm real_greatest_lower_bound_exists({}, 0)",
        "release thm real_least_upper_bound_exists({1}, 0)",
        "release thm real_greatest_lower_bound_exists({0}, 1)",
        "release thm real_member_le_least_upper_bound({0}, 0, 0)",
        "release thm real_greatest_lower_bound_le_member({0}, 0, 0)",
        "release thm real_least_upper_bound_le_upper_bound({0}, 0, 1)",
        "release thm real_lower_bound_le_greatest_lower_bound({0}, 0, -1)",
        "release thm real_archimedean_natural_upper_bound(i)",
        "release thm rational_between_reals(1, 0)",
        "$is_real_least_upper_bound({0}, 0)",
    ] {
        let mut rt = runtime();
        let before = count_facts(&rt);
        let result = execute(&mut rt, code);
        assert!(result.is_failed(), "unexpected builtin success: {code}");
        assert_eq!(count_facts(&rt), before, "failed application leaked facts: {code}");
    }
}

#[test]
fn chinese_theorem_diagnostics_keep_the_exact_failed_premise() {
    let mut rt = Runtime::new(LaunchCommand::Eval { code: String::new(), session: false, strict: true, language: OutputLanguage::Chinese });
    let result = execute(&mut rt, "release thm subset_of_finite_set_is_finite({2}, {1})");
    assert!(result.is_failed());
    for json in [project_stmt_normal(&result, &rt), project_stmt_detailed(&result, &rt)] {
        let text = json.stringify();
        for expected in ["定理名", "目标命题", "下标", "subset_of_finite_set_is_finite", "{2} $subset {1}"] {
            assert!(text.contains(expected), "missing {expected}: {text}");
        }
    }
}

#[test]
fn builtin_release_keeps_contract_premise_and_wd_evidence() {
    let mut rt = runtime();
    let result = execute(&mut rt, "release thm rational_between_reals(0, 1)");
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(ExecReleaseThmStmtResult::Success(ref success))) = result else { panic!("expected theorem success") };
    assert_eq!(success.builtin.as_ref().unwrap().theorem, BuiltinTheoremId::RationalBetweenReals);
    assert_eq!(success.dom_proofs.len(), 3);
    assert_eq!(success.conclusions_wd.len(), 1);
    assert_eq!(success.stored.len(), 1);
    let json = project_stmt_detailed(&result, &rt).stringify();
    assert!(json.contains("builtin_theorem") && json.contains("requirements") && json.contains("conclusions_wd"));
}

#[test]
fn builtin_by_thm_stores_only_selected_conclusion_and_rolls_back_failure() {
    let mut rt = runtime();
    let result = execute(&mut rt, "by thm subset_of_finite_set_is_finite({1}, {1, 2}) => $is_finite_set({1})");
    assert!(!result.is_failed(), "{}", project_stmt_detailed(&result, &rt).stringify());
    let before = count_facts(&rt);
    let failed = execute(&mut rt, "by thm rational_between_reals(2, 3) => 0 = 1");
    assert!(failed.is_failed());
    assert_eq!(count_facts(&rt), before);
    assert!(project_stmt_normal(&failed, &rt).stringify().contains("selected_fact"));
    assert!(execute(&mut rt, "exist q Q st {2 < q and q < 3}").is_failed());
}

#[test]
fn builtin_names_and_opaque_certificates_cannot_be_redefined() {
    for code in [
        "have fn_set_member R",
        "thm rational_between_reals:\n    ? 1 = 1",
        "prop is_real_least_upper_bound(S set, L R):\n    L = L",
        "abstract_prop is_real_greatest_lower_bound(S, L)",
    ] {
        let mut rt = runtime();
        let blocks = Tokenizer::new().tokenize(code, rt.current_file.clone()).unwrap();
        assert!(rt.parse(&blocks).is_err(), "reserved name accepted: {code}");
    }
}

#[test]
fn empty_named_and_anonymous_index_families_are_rejected_by_wd() {
    for op in ["index_union", "index_intersect", "index_cart"] {
        let mut rt = runtime();
        assert!(!execute(&mut rt, "have fn family(k {}) power_set(N) = {}").is_failed());
        for family in ["family", "fn(k {}) power_set(N) {{}}"] {
            let code = format!("{op}({{}}, {}, {family}) = {op}({{}}, {}, {family})", if op == "index_cart" { "power_set(N)" } else { "N" }, if op == "index_cart" { "power_set(N)" } else { "N" });
            let before = count_facts(&rt);
            let result = execute(&mut rt, &code);
            assert!(result.is_failed(), "empty index accepted: {code}");
            assert!(project_stmt_normal(&result, &rt).stringify().contains("well_defined"));
            assert_eq!(count_facts(&rt), before);
        }
    }
}

#[test]
fn complex_calculation_retains_typed_route_and_rejects_invalid_identities() {
    for code in ["i*i=-1", "i^2=-1", "i^3=-i", "(1+i)*(1-i)=2", "i/2+i/2=i"] {
        let mut rt = runtime();
        let result = execute(&mut rt, code);
        assert!(!result.is_failed(), "{code}");
        let json = project_stmt_detailed(&result, &rt).stringify();
        assert!(json.contains("by_closed_calculation") && json.contains("left_imaginary") && json.contains("right_imaginary"), "{json}");
    }
    for code in ["i*i=1", "i^3=i", "(1+i)*(1-i)=0", "i/0=i/0", "1/0=1/0", "0/0=1"] {
        let mut rt = runtime();
        assert!(execute(&mut rt, code).is_failed(), "invalid calculation accepted: {code}");
    }
}

#[test]
fn theorem_diagnostics_keep_nested_proof_failure_and_conclusion_wd() {
    let mut rt = runtime();
    let result = execute(&mut rt, "thm wrong:\n    ? 0 = 1\n    release thm subset_of_finite_set_is_finite({2}, {1})");
    assert!(result.is_failed());
    for json in [project_stmt_normal(&result, &rt), project_stmt_detailed(&result, &rt)] {
        let text = json.stringify();
        assert!(text.contains("proof_body") && text.contains("{2} $subset {1}"), "{text}");
    }
    let mut rt = runtime();
    let result = execute(&mut rt, "release thm index_cart_nonempty_by_choice_from_family(index_cart({}, {{1}}, fn(k {}) {{1}} {{1}}))");
    assert!(result.is_failed());
    let text = project_stmt_normal(&result, &rt).stringify();
    assert!(text.contains("well_defined") && (text.contains("nonempty") || text.contains("empty")), "{text}");
}
