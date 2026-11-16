use crate::prelude::*;
use std::collections::HashSet;

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

fn check(source: &str, expected: bool) {
    let run = runtime().run_litex_code(source).unwrap();
    assert_eq!(run.success, expected, "{source}");
    assert!(run.session_error.is_none(), "{source}");
}

#[test]
fn direct_analysis_all_80_audited_interfaces() {
    let operations = [
        "constant", "neg", "abs", "scale", "power", "add", "subtract", "multiply", "divide",
    ];
    let mut names = HashSet::new();
    let mut cases = Vec::new();
    for op in operations.into_iter().chain(["shift"]) {
        let name = format!("seq_limit_{op}");
        let (expression, result) = arithmetic_case(op, "a(k)", "b(k)", "k");
        let expression = if op == "shift" {
            "a(k+s)".to_string()
        } else {
            expression
        };
        let mut premises = String::new();
        if op != "constant" {
            premises.push_str("        $has_seq_limit(a,A)\n");
        }
        if matches!(op, "add" | "subtract" | "multiply" | "divide") {
            premises.push_str("        $has_seq_limit(b,B)\n");
        }
        if op == "divide" {
            premises.push_str("        B!=0\n        forall k N+:\n            b(k)!=0\n");
        }
        let conclusion = format!("$has_seq_limit(fn(k N+) R {{{expression}}},{result})");
        let facts = if premises.is_empty() {
            format!("        {conclusion}")
        } else {
            format!("{premises}        =>:\n            {conclusion}")
        };
        let source = format!("thm direct_{name}:\n    ? forall a,b seq(R),A,B,c R,n,s N:\n{facts}");
        cases.push((name, source));
    }
    for direction in ["at", "left", "right", "neg_inf", "pos_inf"] {
        for op in operations
            .into_iter()
            .chain(if matches!(direction, "at" | "left" | "right") {
                Some("identity")
            } else {
                None
            })
        {
            let name = format!("fn_limit_{direction}_{op}");
            let (expression, result) = arithmetic_case(op, "f(x)", "g(x)", "x");
            let point = if matches!(direction, "neg_inf" | "pos_inf") {
                ""
            } else {
                "x0,"
            };
            let mut premises = String::new();
            if !matches!(op, "constant" | "identity") {
                premises.push_str(&format!("        $has_limit_{direction}(f,{point}A)\n"));
            }
            if matches!(op, "add" | "subtract" | "multiply" | "divide") {
                premises.push_str(&format!("        $has_limit_{direction}(g,{point}B)\n"));
            }
            if op == "divide" {
                premises.push_str("        B!=0\n        forall x R:\n            g(x)!=0\n");
            }
            let conclusion =
                format!("$has_limit_{direction}(fn(x R) R {{{expression}}},{point}{result})");
            let facts = if premises.is_empty() {
                format!("        {conclusion}")
            } else {
                format!("{premises}        =>:\n            {conclusion}")
            };
            let source =
                format!("thm direct_{name}:\n    ? forall f,g fn(x R) R,x0,A,B,c R,n N:\n{facts}");
            cases.push((name, source));
        }
    }
    for side in ["left", "right"] {
        for op in operations.into_iter().chain(["identity", "compose"]) {
            let name = format!("fn_continuous_{side}_{op}");
            let (expression, _) = arithmetic_case(op, "f(x)", "g(x)", "x");
            let mut premises = String::new();
            if !matches!(op, "constant" | "identity") {
                premises.push_str(&format!("        $is_continuous_{side}(f,x0)\n"));
            }
            if matches!(op, "add" | "subtract" | "multiply" | "divide") {
                premises.push_str(&format!("        $is_continuous_{side}(g,x0)\n"));
            }
            if op == "compose" {
                premises.push_str("        $is_continuous_at(g,f(x0))\n");
            }
            if op == "divide" {
                premises.push_str("        g(x0)!=0\n");
            }
            let target_domain = if op == "divide" { "x R:g(x)!=0" } else { "x R" };
            let conclusion =
                format!("$is_continuous_{side}(fn({target_domain}) R {{{expression}}},x0)");
            let facts = if premises.is_empty() {
                format!("        {conclusion}")
            } else {
                format!("{premises}        =>:\n            {conclusion}")
            };
            let source =
                format!("thm direct_{name}:\n    ? forall f,g fn(x R) R,x0,c R,n N:\n{facts}");
            cases.push((name, source));
        }
    }
    for (name, source) in cases {
        assert!(names.insert(name.clone()), "duplicate {name}");
        assert!(
            crate::builtin_theorem::BuiltinTheoremId::from_name(&name).is_some(),
            "{name}"
        );
        assert!(!source.contains("by thm") && !source.contains("release thm"));
        let mut rt = runtime();
        let run = rt.run_litex_code(&source).unwrap();
        assert!(
            run.success && run.session_error.is_none(),
            "{name}\n{source}\n{}",
            crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify()
        );
        let json = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
        assert!(
            json.contains(if name.contains("continuous") {
                "PointwiseContinuity"
            } else {
                "StructuralLimit"
            }),
            "{name}: missing constructing certificate"
        );
        let old_path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("examples/stmt_nodes/release_and_expand/builtin_thm")
            .join(format!("{name}.lit"));
        let old_source = std::fs::read_to_string(&old_path).unwrap();
        let old_run = runtime().run_litex_code(&old_source).unwrap();
        assert!(
            old_run.success && old_run.session_error.is_none(),
            "old explicit path {name}"
        );
    }
    assert_eq!(names.len(), 80);
}

fn arithmetic_case(op: &str, f: &str, g: &str, variable: &str) -> (String, String) {
    match op {
        "constant" => ("c".into(), "c".into()),
        "identity" => (variable.into(), "x0".into()),
        "neg" => (format!("-{f}"), "-A".into()),
        "abs" => (format!("abs({f})"), "abs(A)".into()),
        "scale" => (format!("c*{f}"), "c*A".into()),
        "power" => (format!("{f}^n"), "A^n".into()),
        "add" => (format!("{f}+{g}"), "A+B".into()),
        "subtract" => (format!("{f}-{g}"), "A-B".into()),
        "multiply" => (format!("{f}*{g}"), "A*B".into()),
        "divide" => (format!("{f}/{g}"), "A/B".into()),
        "shift" => ("a(k+s)".into(), "A".into()),
        "compose" => ("g(f(x))".into(), String::new()),
        _ => panic!("unexpected {op}"),
    }
}

#[test]
fn structural_limit_wrong_values_missing_leaves_domains_and_directions() {
    for source in [
        "$has_seq_limit(fn(k N+) R {2},3)",
        "forall a,b seq(R),A,B R:\n    $has_seq_limit(a,A)\n    =>:\n        $has_seq_limit(fn(k N+) R {a(k)+b(k)},A+B)",
        "forall a,b seq(R),A,B R:\n    $has_seq_limit(a,A)\n    $has_seq_limit(b,B)\n    =>:\n        $has_seq_limit(fn(k N+) R {a(k)+b(k)},A+B+1)",
        "forall a,b seq(R),A R:\n    $has_seq_limit(a,A)\n    $has_seq_limit(b,0)\n    forall k N+:\n        b(k)!=0\n    =>:\n        $has_seq_limit(fn(k N+) R {a(k)/b(k)},0)",
        "forall a seq(R),A R:\n    $has_seq_limit(a,A)\n    =>:\n        $has_seq_limit(fn(k N+) R {a(k-1)},A)",
        "forall f fn(x R) R,A R:\n    $has_limit_left(f,0,A)\n    =>:\n        $has_limit_right(fn(x R) R {-f(x)},0,-A)",
        "have fn isolated(x {0}) R=1\n$has_limit_at(isolated,0,1)",
        "$has_limit_pos_inf(fn(x R) R {x},0)",
        "forall f,g fn(x R) R:\n    $is_continuous_left(f,0)\n    =>:\n        $is_continuous_right(fn(x R) R {f(x)},0)",
        "forall f,g fn(x R) R:\n    $is_continuous_left(f,0)\n    $is_continuous_at(g,0)\n    =>:\n        $is_continuous_left(fn(x R) R {g(f(x))},0)",
    ] { check(source,false); }
}

#[test]
fn structural_limit_nested_named_values_selector_and_output() {
    let mut rt = runtime();
    let source="have fn a(k N+) R=2\n$has_seq_limit(a,2)\nhave fn b(k N+) R=3\n$has_seq_limit(b,3)\nhave fn total(k N+) R=-(a(k)+b(k))*2+abs(a(k))\n$has_seq_limit(total,-8)\nlim(total)=-8";
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none());
    let json = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
    for tag in [
        "StructuralLimit",
        "body_equal",
        "body_well_defined",
        "LimitCandidate",
        "result_equal",
        "geometry",
    ] {
        assert!(json.contains(tag), "{tag}");
    }
    let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "structural_limits")
        .unwrap_err();
    assert_eq!(error.route, "Atomic/BuiltinStrategy");
    assert!(error.message.contains("Unsupported") || error.message.contains("not supported"));
}

#[test]
fn run_examples_structural_analysis_rules_80() {
    for source in [
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_strategy/structural_sequence_limit_arithmetic.lit"),
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_strategy/structural_function_limit_arithmetic.lit"),
        include_str!("../../../../examples/proof_nodes/atomic/by_builtin_strategy/directional_continuity_arithmetic.lit"),
    ] {
        check(source, true);
    }
}

#[test]
fn structural_limit_actual_domains_and_continuity_isolated_points() {
    for source in [
        "thm punctured:\n    ? forall f,g fn(x R:x!=0) R,A,B R:\n        $has_limit_at(f,0,A)\n        $has_limit_at(g,0,B)\n        =>:\n            $has_limit_at(fn(x R:x!=0) R {f(x)+g(x)},0,A+B)",
        "thm positive_infinity:\n    ? forall f,g fn(x R+) R,A,B R:\n        $has_limit_pos_inf(f,A)\n        $has_limit_pos_inf(g,B)\n        =>:\n            $has_limit_pos_inf(fn(x R+) R {f(x)*g(x)},A*B)",
        "have fn isolated(x {0}) R=2\n$is_continuous_left(isolated,0)\n$is_continuous_right(isolated,0)",
        "thm guarded_quotient:\n    ? forall f,g fn(x R) R:\n        $is_continuous_left(f,0)\n        $is_continuous_left(g,0)\n        g(0)!=0\n        =>:\n            $is_continuous_left(fn(x R:g(x)!=0) R {f(x)/g(x)},0)",
        "$has_seq_limit(fn(k N+) R {2^0},1)",
        "$has_limit_left(fn(x R) R {x},0,0)\n$has_limit_right(fn(x R) R {x},0,0)",
    ] { check(source,true); }
}

#[test]
fn structural_limit_respects_ceiling_and_failed_scope() {
    let mut rt = runtime();
    assert!(rt.run_litex_code("have fn a(k N+) R=2").unwrap().success);
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("$has_seq_limit(a,2)", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact");
    };
    assert!(rt
        .verify_fact(&goal, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    assert!(
        !rt.run_litex_code("claim:\n    ? 0=1\n    $has_seq_limit(a,2)\n    0=1")
            .unwrap()
            .success
    );
    assert!(rt.known_sequence_limit_candidates().is_empty());
    assert!(rt.run_litex_code("lim(a)=2").unwrap().success);
    assert!(rt.run_litex_code("$has_seq_limit(a,2)").unwrap().success);
    assert!(rt.run_litex_code("lim(a)=2").unwrap().success);
}

#[test]
fn structural_limit_selectors_direct_and_explicit_conditions() {
    for source in [
        "have fn f(x R) R=x^2\nfn_lim(f,2)=4",
        "have fn a(k N+) R=0\nlim(a)=0",
        "have fn f(x R) R=x+1\nfn_lim(f,0)=1",
        "have fn f(x R) R=x^2\n$has_limit_at(f,2,4)\nfn_lim(f,2)=4",
        "have fn a(n N+) R=1\nlim(a)=1",
        "have fn a(n N+) R=1\n$has_seq_limit(a,1)\nlim(a)=1",
        "have fn f(x R) R=x^2\nfn_lim(f,2) $in R",
        "have fn a(n N+) R=1\nlim(a) $in R",
        "have fn f(x R) R=(x+2)^2\n1=fn_lim(f,-1)",
        "forall c,p R:\n    fn_lim(fn(x R) R {c*x+1},p)=c*p+1",
        "forall c R:\n    lim(fn(n N+) R {c+2})=c+2",
        "have fn f(x R) R=x^2\nexist L R st {$has_limit_at(f,2,L)}",
        "have fn a(n N+) R=3\nexist L R st {$has_seq_limit(a,L)}",
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/examples/wd/calculus_automatic_conditions.lit"
        )),
    ] {
        check(source, true);
    }
}

#[test]
fn structural_limit_selectors_reject_wrong_values_and_missing_conditions() {
    for source in [
        "have fn f(x R) R=x^2\nfn_lim(f,2)=5",
        "have fn a(n N+) R=1\nlim(a)=2",
        "have f fn(x R) R\nfn_lim(f,2)=4",
        "have a seq(R)\nlim(a)=1",
        "have f fn(x R) R\n0*fn_lim(f,2)=0",
        "have a seq(R)\n0*lim(a)=0",
        "have fn a(n N+) R=n\nlim(a)=0",
        "have fn a(n N+) R=(-1)^n\nlim(a)=0",
        "have fn isolated(x {0}) R=1\nfn_lim(isolated,0)=1",
        "have fn corner(x R) R=abs(x)\nderiv(corner,0)=0",
        "have fn reciprocal(x R*) R=1/x\nderiv(reciprocal,0)=0",
        "have fn a(n N+) R=0\nexist L R+ st {$has_seq_limit(a,L)}",
        "have fn a(n N+) R=n\nexist! L R st {$has_seq_limit(a,L)}",
        "have fn a(n N+) R=1\nnot exist L R st {$has_seq_limit(a,L)}",
        "exist L R st {$has_limit_at(fn(x R) R {L+1},0,L)}",
        "exist L R st {$has_limit_at(fn(x R) R {x+1},L,L)}",
        "have fn a(n N+) R=1\nexist L R st {$has_seq_limit(a,L), L=2}",
    ] {
        check(source, false);
    }
}

#[test]
fn structural_limit_existence_keeps_shared_permissions_and_does_not_publish_candidates() {
    let targets = [
        (
            "have fn f(x R) R=x^2",
            "exist L R st {$has_limit_at(f,2,L)}",
        ),
        ("have fn a(n N+) R=1", "exist L R st {$has_seq_limit(a,L)}"),
        ("have fn f(x R) R=x^2", "fn_lim(f,2)=4"),
        ("have fn a(n N+) R=1", "lim(a)=1"),
    ];
    for (prefix, source) in targets {
        for level in [
            VerifyStateLevel::Direct,
            VerifyStateLevel::BuiltinRule,
            VerifyStateLevel::Strategy,
        ] {
            let mut rt = runtime();
            assert!(rt.run_litex_code(prefix).unwrap().success);
            let tokens = crate::tokenize::Tokenizer::new()
                .tokenize(source, rt.current_file.clone())
                .unwrap();
            let Stmt::Fact(goal) = rt.parse(&tokens).unwrap().remove(0) else {
                panic!("fact");
            };
            let result = rt.verify_fact(&goal, VerifyState::new(level)).unwrap();
            assert_eq!(
                !result.is_failed(),
                level == VerifyStateLevel::Strategy,
                "{source} {level:?}"
            );
            assert!(rt.known_function_limit_candidates().is_empty());
            assert!(rt.known_sequence_limit_candidates().is_empty());
        }
    }
}

#[test]
fn structural_limit_existence_records_evidence_and_preserves_lean_boundary() {
    for source in [
        "have fn f(x R) R=x^2\nfn_lim(f,2)=4",
        "have fn a(n N+) R=1\nlim(a)=1",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(source).unwrap();
        assert!(run.success);
        let json = crate::json_output::project_run_detailed(&run, &rt, "test", None).stringify();
        assert!(json.contains("LimitValue"));
        assert!(json.matches("StructuralLimit").count() >= 2);
        let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
            .compile_run(&run, "structural_limit_selection")
            .expect_err("structural limit strategy replay remains unsupported");
        assert!(format!("{error:?}").contains("Exist/StructuralLimit"));
    }
}
