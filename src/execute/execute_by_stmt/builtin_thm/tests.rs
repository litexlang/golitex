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
fn exact_function_finite_values_support_named_calls_carriers_aliases_and_complete_domains() {
    for code in [
        "have p cart(R,Z) = (1,2)\np(1)=1\np(2) $in Z",
        "have p cart(R,Z)\np(1) $in R\np(2) $in Z\np(2) $in R",
        "have Carrier set=cart(R,Z)\nhave p Carrier=(1,2)\nhave q Carrier=p\nq=(1,2)\nq(1)=1\nq(2) $in Z",
        "(1,2) $in finite_seq(Z,2)\n(1,2) $in finite_seq(R,2)\nrelease thm fn_set_member((1,2),finite_seq(R,2))",
        "let p=(1,2)\np $in finite_seq(Z,2)\nrelease thm fn_set_member(p,finite_seq(R,2))",
        "let p=(1,1)\np(1)=1\np(2)=1\np $in finite_seq(Z,2)",
        "let p=tuple(7)\np(1)=7\np $in finite_seq(Z,1)",
        "let empty=()\nrelease thm fn_set_member(empty,finite_seq(R,0))",
        "have a,b R\nlet p=(a,b)\np(1)=a\np(2)=b\np $in finite_seq(R,2)",
        "have fn mk(x R) cart(R,Z)=(x,2)\nmk(7)(2) $in Z",
        "release thm cart_member_from_coordinates((1,2),cart(R,Z))\nlet p=(1,2)\nrelease thm cart_member_from_coordinates(p,cart(R,Z))\nhave Carrier set=cart(R,Z)\nrelease thm cart_member_from_coordinates(p,Carrier)\np(2) $in Z",
        "have fn f(k closed_range(1,2)) Z=0\nrelease thm cart_member_from_coordinates(f,cart(R,Z))\nf $in cart(R,Z)\nf(2) $in Z",
    ] {
        let mut rt=runtime();
        let run=rt.run_litex_code(code).unwrap();
        assert!(run.success && run.session_error.is_none(), "{code}\n{}", crate::json_output::emit_run_detailed(&run,&rt,"test",None));
    }
    for (setup, negative) in [
        ("let p=(1,2)", "p(0)=1"),
        ("let p=(1,2)", "p(3)=2"),
        ("let p=(1,2)", "p(1/2)=1"),
        ("let p=(1,2)", "p(1,2)=1"),
        ("let p=(1,2)", "p(1)(1)=1"),
        ("let p=(1,2)", "p(1)=2"),
        ("let p=(1,2)", "release thm fn_set_member(p,finite_seq(R,3))"),
        ("let p=tuple(7)", "p(2)=7"),
        ("let p=()", "p(1)=0"),
        ("have p cart(R,Z)", "p(1) $in Z"),
        ("have fn mk(x R: x>0) cart(R,Z)=(x,2)", "mk(0)(2) $in Z"),
        ("have fn mk(x R) cart(R,Z)=(x,2)", "mk(7)(3) $in Z"),
        ("have fn z(k N+) Z=0", "release thm cart_member_from_coordinates(z,cart(R,Z))"),
        ("let p=(1,2,3)", "release thm cart_member_from_coordinates(p,cart(R,Z))"),
        ("let p=(1,2)", "release thm cart_member_from_coordinates(p,cart(R,{}))"),
    ] {
        let mut rt=runtime();
        assert!(rt.run_litex_code(setup).unwrap().success,"{setup}");
        let before=count_facts(&rt);
        assert!(execute(&mut rt,negative).is_failed(),"{setup}\n{negative}");
        assert_eq!(count_facts(&rt),before,"finite-function negative published facts");
    }
}

#[test]
fn exact_function_domain_acceptance_files_keep_successful_prefixes_and_failure_phases() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let negative_root = root.join("examples/negative/exact_function_domains");
    let manifest = std::fs::read_to_string(negative_root.join("manifest.json")).unwrap();
    let manifest = crate::knowledge_base::JsonValue::parse(&manifest).unwrap();
    for case in manifest.as_array().unwrap() {
        let case = case.as_object().unwrap();
        let file = case.get("file").unwrap().as_str().unwrap();
        let phase = case.get("expected_phase").unwrap().as_str().unwrap();
        let source = std::fs::read_to_string(negative_root.join(file)).unwrap();
        let mut rt = runtime();
        let run = rt.run_litex_code(&source).unwrap();
        assert!(!run.success, "negative fixture accepted: {file}");
        if phase == "retired_syntax" {
            let expected_count = case.get("expected_prefix_count")
                .map(|value| value.as_u64().unwrap() as usize).unwrap_or(2);
            let expected_diagnostic = case.get("expected_diagnostic")
                .map(|value| value.as_str().unwrap()).unwrap_or("cart_dim is removed");
            assert_eq!(run.statement_results.len(), expected_count, "{file}");
            assert!(run.statement_results.iter().all(|stmt| !stmt.is_failed()), "{file}");
            assert!(format!("{:?}", run.session_error).contains(expected_diagnostic), "{file}");
            continue;
        }
        assert!(run.session_error.is_none(), "unexpected parse/exec failure: {file}");
        let (last, prefix) = run.statement_results.split_last().expect("negative statement");
        assert!(prefix.iter().all(|stmt| !stmt.is_failed()), "failed setup: {file}");
        assert!(last.is_failed(), "negative target accepted: {file}");
        let json = project_stmt_normal(last, &rt);
        let failure = json.as_object().unwrap().get("why_failed").unwrap().as_object().unwrap();
        let mut actual_phase = failure.get("phase").unwrap().as_str().unwrap();
        // Release has an outer statement stage and a nested theorem stage.
        // Check that exact owner, rather than finding an arbitrary phase in
        // a premise's recursive proof tree.
        if actual_phase == "release_thm" {
            actual_phase = failure.get("failure").unwrap().as_object().unwrap()
                .get("phase").unwrap().as_str().unwrap();
        }
        assert_eq!(actual_phase, phase, "wrong failure boundary: {file}");
        if let Some(stage) = case.get("expected_constructor_stage") {
            // Follow the constructor's exact WD stage, rather than matching a
            // recursive child premise that happens to have the same label.
            let mut constructor_failure = failure;
            for _ in 0..4 {
                constructor_failure = constructor_failure.get("failure").unwrap().as_object().unwrap();
            }
            assert_eq!(constructor_failure.get("phase").unwrap().as_str().unwrap(),
                stage.as_str().unwrap(), "wrong constructor obligation: {file}");
        }
    }
    for file in [
        "examples/stmt_nodes/release_and_expand/builtin_thm/fn_set_member.lit",
        "examples/proof_nodes/atomic/by_builtin_strategy/exact_function_space_membership.lit",
        "examples/proof_nodes/atomic/by_builtin_strategy/finite_function_application_membership.lit",
        "examples/proof_nodes/forall/empty_parameter_domain.lit",
        "examples/proof_nodes/equal/by_object_definition/by_fn_application/both_function_bodies.lit",
        "examples/infer/atomic/in_sequence_space_alias_expand.lit",
        "examples/wd/sequence_return_application.lit",
        "examples/infer/atomic/in_equal_fn_set_expand.lit",
        "examples/infer/atomic/in_finite_seq_expand.lit",
        "examples/proof_nodes/equal/by_builtin_rule/function_empty_domain_graph.lit",
        "examples/proof_nodes/atomic/by_builtin_strategy/function_space_return_carrier_aliases.lit",
        "examples/proof_nodes/atomic/by_builtin_strategy/nested_sequence_space_nonempty.lit",
        "examples/proof_nodes/atomic/direct_closed_integer_range_membership.lit",
        "examples/proof_nodes/equal/by_builtin_rule/empty_function_graph_identity.lit",
        "examples/proof_nodes/equal/by_builtin_rule/empty_domain_function_space_singleton.lit",
        "examples/proof_nodes/atomic/by_builtin_rule/cart_zero_one_membership.lit",
        "examples/proof_nodes/equal/by_builtin_rule/cart_zero_one_size.lit",
        "examples/infer/atomic/cart_exact_function_coordinates.lit",
        "examples/infer/atomic/in_cart_projection.lit",
        "examples/stmt_nodes/definition/struct_function_coordinate_bridges.lit",
        "examples/proof_nodes/equal/by_object_definition/by_fn_application/finite_function_coordinate_call.lit",
        "examples/proof_nodes/atomic/by_known_special_property/function_return_standard_superset.lit",
        "examples/proof_nodes/equal/by_builtin_rule/finite_product_exact_restrictions.lit",
        "examples/proof_nodes/equal/by_object_definition/cart_function_set_definition.lit",
        "examples/proof_nodes/equal/by_builtin_rule/guarded_empty_function_domain.lit",
        "examples/proof_nodes/equal/by_known_special_property/tuple_reconstruction.lit",
        "examples/proof_nodes/equal/by_known_special_property/tuple_projection.lit",
        "examples/proof_nodes/equal/by_known_special_property/fn_tuple_projection.lit",
        "examples/wd/known_function_cart_projection.lit",
        "examples/proof_nodes/atomic/by_known_special_property/homogeneous_cart_coordinate.lit",
        "examples/proof_nodes/atomic/by_known_special_property/known_cart_index_upper_bound.lit",
        "examples/proof_nodes/equal/by_builtin_rule/cart_reconstruction.lit",
        "examples/stmt_nodes/release_and_expand/literal_tuple_extensionality.lit",
        "examples/stmt_nodes/release_and_expand/tuple_exact_function_extensionality.lit",
        "examples/proof_nodes/atomic/direct_structural_membership.lit",
        "examples/proof_nodes/equal/by_known_special_property/fn_tuple_carrier_after_equality.lit",
        "examples/proof_nodes/equal/by_object_definition/nested_call_one_step.lit",
        "examples/proof_nodes/equal/by_equivalence_class/stored_equality_before_builtin.lit",
        "examples/proof_nodes/equal/by_object_definition/by_fn_application/function_value_parameter_application.lit",
    ] {
        let source = std::fs::read_to_string(root.join(file)).unwrap();
        let mut rt = runtime();
        let run = rt.run_litex_code(&source).unwrap();
        assert!(run.success && run.session_error.is_none(), "{file}\n{}",
            crate::json_output::emit_run_detailed(&run, &rt, "test", None));
        assert!(!run.statement_results.is_empty(), "empty acceptance: {file}");
        assert!(run.statement_results.iter().all(|stmt| !stmt.is_failed()), "{file}");
    }
}

#[test]
fn exact_function_membership_rejects_short_long_empty_and_dropped_guards_without_publishing() {
    for (definition, target) in [
        ("have fn z(i1 N+) R = 0", "finite_seq(R,2)"),
        ("have fn z(i1 N+) R = 0", "finite_seq(R,3)"),
        ("have fn z(i1 N+) R = 0", "fn(k closed_range(1,2)) R"),
        ("have fn z(i1 N+) R = 0", "finite_seq(R,0)"),
        ("have fn z(i1 N+) R = 0", "fn(k {}) R"),
        ("have fn z(i1 closed_range(1,2)) R = 0", "finite_seq(R,3)"),
        ("have fn z(i1 closed_range(1,3)) R = 0", "finite_seq(R,2)"),
        ("have fn z(x R: x>0) R = 0", "fn(y R) R"),
    ] {
        for statement in [
            format!("z $in {target}"),
            format!("release thm fn_set_member(z, {target})"),
            format!("by thm fn_set_member(z, {target}) => z $in {target}"),
        ] {
            let mut rt = runtime();
            assert!(!execute(&mut rt, definition).is_failed(), "{definition}");
            let before = count_facts(&rt);
            let result = execute(&mut rt, &statement);
            assert!(result.is_failed(), "false exact membership: {definition}\n{statement}");
            assert_eq!(count_facts(&rt), before, "rejected exact membership published facts");
            if statement.contains("thm") {
                let detailed = format!("{:?}", project_stmt_detailed(&result, &rt));
                assert!(detailed.contains("function_domain"), "{detailed}");
            }
        }
    }
}

#[test]
fn exact_function_membership_preserves_return_bounds_restrictions_and_aliases() {
    for code in [
        "have fn z(i1 N+) R = 0\nz $in seq(R)\nz(1)=0",
        "have fn z(i1 N+) R = 0\nhave fn z2(k closed_range(1,2)) R = z(k)\nz2 $in finite_seq(R,2)\nrelease thm fn_set_member(z2, fn(j closed_range(1,2)) R)",
        "have fn u(i1 closed_range(1,2)) Z = 0\nu $in finite_seq(Z,2)\nu $in finite_seq(R,2)\nu(1) $in Z\nu(1) $in R",
        "have fn u(i1 closed_range(1,2)) Z = 0\nrelease thm fn_set_member(u, finite_seq(R,2))\nby thm fn_set_member(u, fn(j closed_range(1,2)) R) => u $in fn(k closed_range(1,2)) R",
        "have fn z(x R: x>0) Z = 0\nz $in fn(y R: y>0) R\nrelease thm fn_set_member(z, fn(y R: y>0) R)",
        "have F set = fn(k closed_range(1,2)) R\nhave fn z(x closed_range(1,2)) Z = 0\nhave q F = z\nq = fn(x closed_range(1,2)) Z {0}\nq $in finite_seq(R,2)\nq(1)=0",
        "have fn empty_fn(x {}) R = 0\nrelease thm fn_set_member(empty_fn, finite_seq(R,0))",
        "have n N\nhave fn z(k closed_range(1,n)) Z = 0\nz $in finite_seq(Z,n)\nrelease thm fn_set_member(z, finite_seq(R,n))\nfinite_seq(R,n)=fn(j closed_range(1,n)) R",
        "have fn z(k N+: k<=2) Z = 0\nrelease thm fn_set_member(z, fn(j closed_range(1,2)) R)\nz $in finite_seq(R,2)",
        "template<A set>:\n    have fn zero(x A) Z = 0\nrelease thm fn_set_member(\\zero<closed_range(1,2)>, finite_seq(R,2))\nlet selected=\\zero<closed_range(1,2)>\nselected $in finite_seq(R,2)\n\\zero<closed_range(1,2)> = fn(x closed_range(1,2)) Z {0}\nselected(1)=0",
        "template<a R>:\n    have fn maker(x R) fn(y R) Z = fn(y R) Z {0}\n\\maker<2>(3) $in fn(t R) R\nrelease thm fn_set_member(\\maker<2>(3), fn(t R) R)",
    ] {
        let mut rt = runtime();
        let result = rt.run_litex_code(code).unwrap();
        assert!(result.success && result.session_error.is_none(), "{code}\n{}", crate::json_output::emit_run_detailed(&result, &rt, "test", None));
        for statement in &result.statement_results { assert!(!statement.is_failed()); }
    }
}

#[test]
fn function_space_alias_is_a_set_and_does_not_construct_a_callable_function() {
    let mut rt = runtime();
    assert!(!execute(&mut rt, "have F set = fn(x R) R").is_failed());
    let before = count_facts(&rt);
    assert!(execute(&mut rt, "F(1) $in R").is_failed());
    assert_eq!(count_facts(&rt), before);
}

#[test]
fn exact_function_empty_cart_equalities_do_not_publish_dimensions_or_false_equalities() {
    let mut rt = runtime();
    for statement in ["cart({},R)={}", "cart({},R,Z)={}"] {
        assert!(!execute(&mut rt, statement).is_failed(), "{statement}");
    }
    for env in &rt.execution_environments_stack {
        for fact in env.facts.facts_by_id.values() {
            assert!(!fact.readable_string().contains("cart_dim"), "unexpected dimension fact: {}", fact.readable_string());
        }
    }
    let before = count_facts(&rt);
    assert!(execute(&mut rt, "2=3").is_failed());
    assert_eq!(count_facts(&rt), before);
}

#[test]
fn exact_function_retired_cart_dimension_has_no_parse_wd_or_numeric_route() {
    for code in ["cart_dim({})=2", "cart_dim(cart({},R))=2", "cart_dim(cart({},R,Z))=3"] {
        let mut rt = runtime();
        let result = rt.run_litex_code(code).unwrap();
        assert!(result.session_error.is_some(), "retired syntax accepted: {code}");
        assert!(result.statement_results.is_empty());
    }

}

#[test]
fn exact_function_extension_uses_full_domains_and_ignores_return_upper_bounds() {
    for code in [
        "have fn a(k closed_range(1,2)) Z = 0\nhave fn b(j closed_range(1,2)) R = 0\nby fn_extension a=b\na=b",
        "have fn a(x R: x>0) Z = 0\nhave fn b(y R: y>0) R = 0\nby fn_extension a=b",
        "have fn a(x {}) R = 0\nhave fn b(y {}) Z = 1\nby fn_extension a=b",
        "have fn make_a(x R) fn(y R) Z = fn(y R) Z {0}\nhave fn make_b(x R) fn(y R) R = fn(y R) R {0}\nby fn_extension:\n    ? make_a=make_b\n    claim:\n        ? forall x R:\n            make_a(x)=make_b(x)\n        by fn_extension make_a(x)=make_b(x)",
    ] {
        let mut rt=runtime();
        let result=rt.run_litex_code(code).unwrap();
        assert!(result.success && result.session_error.is_none(), "{code}\n{}", crate::json_output::emit_run_detailed(&result, &rt, "test", None));
    }
    for (setup, goal) in [
        ("have fn a(k closed_range(1,2)) R = 0\nhave fn b(j closed_range(1,3)) R = 0", "by fn_extension a=b"),
        ("have fn a(x R: x>0) R = 0\nhave fn b(y R) R = 0", "by fn_extension a=b"),
        ("have fn a(x {}) R = 0\nhave fn b(y R) R = 0", "by fn_extension a=b"),
        ("have fn a(x R) fn(y Z) R = fn(y Z) R {0}\nhave fn b(x R) fn(y R) R = fn(y R) R {0}", "by fn_extension:\n    ? a=b\n    claim:\n        ? forall x R:\n            a(x)=b(x)\n        by fn_extension a(x)=b(x)"),
    ] {
        let mut rt=runtime();
        let setup_result=rt.run_litex_code(setup).unwrap();
        assert!(setup_result.success && setup_result.session_error.is_none());
        let before=count_facts(&rt);
        let result=execute(&mut rt,goal);
        assert!(result.is_failed(),"{setup}\n{goal}");
        assert_eq!(count_facts(&rt),before);
        assert!(format!("{:?}",project_stmt_detailed(&result,&rt)).contains("function_domain"));
    }
}

#[test]
fn exact_function_empty_domain_universals_do_not_publish_their_conclusions() {
    for carrier in ["{}", "closed_range(1,0)"] {
        let mut rt=runtime();
        let universal=format!("forall x {carrier}:\n    2=3");
        let result=execute(&mut rt,&universal);
        assert!(!result.is_failed(),"empty-domain universal must be vacuous: {carrier}\n{:?}",project_stmt_detailed(&result,&rt));
        assert!(format!("{:?}",project_stmt_detailed(&result,&rt)).contains("empty_parameter_domain"));
        let before=count_facts(&rt);
        assert!(execute(&mut rt,"2=3").is_failed(),"vacuous conclusions must not escape");
        assert_eq!(count_facts(&rt),before);
        assert!(execute(&mut rt,&format!("forall x {carrier}:\n    1/0=0")).is_failed(),"vacuity must not bypass WD");
    }
    let mut rt=runtime();
    assert!(execute(&mut rt,"forall x {0}:\n    2=3").is_failed(),"nonempty-domain universal cannot be vacuous");
}

#[path = "../../../../tests/unit/execute/builtin_theorem_catalogue/tests.rs"]
mod catalogue_tests;

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
fn literal_tuple_extensionality_checks_all_coordinates_and_complete_domains() {
    for code in [
        "have a cart({1}, {2})\nrelease thm tuple_equal_from_coordinates(a, (1, 2))",
        "have a cart({1}, {2})\nrelease thm tuple_equal_from_coordinates((1, 2), a)",
        "have a cart({1}, {2}, {3})\nrelease thm tuple_equal_from_coordinates(a, (1, 2, 3))",
        "release thm tuple_equal_from_coordinates((),())",
        "have a cart({7})\nby thm tuple_equal_from_coordinates(a,tuple(7)) => a=tuple(7)",
        "have a cart({R},{Z})\nrelease thm tuple_equal_from_coordinates(a,(R,Z))",
        "have a cart({R},{Z})\nby thm tuple_equal_from_coordinates((R,Z),a) => (R,Z)=a",
    ] {
        let mut rt = runtime();
        let result = rt.run_litex_code(code).unwrap();
        assert!(result.success && result.session_error.is_none(), "{code}\n{}", crate::json_output::emit_run_detailed(&result, &rt, "test", None));
        use crate::execute::execute_by_stmt::{BuiltinFunctionDomainProof,ExecByStmtResult,ExecByThmStmtResult};
        let last=result.statement_results.last().unwrap();
        let domains=match last {
            ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(ExecReleaseThmStmtResult::Success(proof))) => &proof.function_domain,
            ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))) => &proof.function_domain,
            _ => panic!("native tuple theorem result"),
        };
        assert!(matches!(domains,Some(BuiltinFunctionDomainProof::TupleEquality{..})),"both complete-domain proofs must survive execution");
        let detailed=project_stmt_detailed(last,&rt).stringify();
        assert!(detailed.contains("tuple_exact_domains"),"{detailed}");
    }
    for (setup, negative) in [
        ("have a cart({1},{2})", "release thm tuple_equal_from_coordinates(a,(1,3))"),
        ("have a cart({1},{2},{3})", "release thm tuple_equal_from_coordinates(a,(1,2))"),
        ("have a cart({1},{2},{3})", "release thm tuple_equal_from_coordinates(a,(1,2,4))"),
        ("have a cart({1},{2})", "release thm tuple_equal_from_coordinates((1,3),a)"),
        ("have a cart({1},{2},{3})", "by thm tuple_equal_from_coordinates(a,(1,2)) => a=(1,2)"),
        ("let a=()", "release thm tuple_equal_from_coordinates(a,tuple(0))"),
        ("have fn z(k N+)R=0\nhave fn z2(k closed_range(1,2))R=z(k)", "release thm tuple_equal_from_coordinates(z,z2)"),
        ("have f,g cart({0},R)\nf(1)=g(1)", "release thm tuple_equal_from_coordinates(f,g)"),
    ] {
        let mut rt = runtime();
        let prefix = rt.run_litex_code(setup).unwrap();
        assert!(prefix.success && prefix.session_error.is_none(), "{setup}");
        let before=count_facts(&rt);
        assert!(execute(&mut rt,negative).is_failed(), "false tuple equality: {setup}\n{negative}");
        assert_eq!(count_facts(&rt),before,"failed extensionality published facts: {negative}");
    }
}

#[test]
fn native_tuple_exact_domain_output_keeps_release_and_selected_proofs_in_ten_languages() {
    let source=include_str!("../../../../examples/stmt_nodes/release_and_expand/tuple_exact_function_extensionality.lit");
    for language in [OutputLanguage::English,OutputLanguage::Chinese,OutputLanguage::ChineseTraditional,OutputLanguage::French,OutputLanguage::Russian,OutputLanguage::Spanish,OutputLanguage::Arabic,OutputLanguage::Japanese,OutputLanguage::Korean,OutputLanguage::Vietnamese] {
        let mut rt=Runtime::new(LaunchCommand::Eval {code:String::new(),session:false,strict:true,language});
        let run=rt.run_litex_code(source).unwrap();
        assert!(run.success && run.session_error.is_none(),"{language:?}");
        for index in [0,2,5,7,8] {
            let stmt=&run.statement_results[index];
            let normal=project_stmt_normal(stmt,&rt).stringify();
            let detailed=project_stmt_detailed(stmt,&rt).stringify();
            crate::knowledge_base::JsonValue::parse(&normal).unwrap();
            crate::knowledge_base::JsonValue::parse(&detailed).unwrap();
            assert!(detailed.contains("tuple_exact_domains"),"{language:?} stmt{index}: {detailed}");
        }
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
