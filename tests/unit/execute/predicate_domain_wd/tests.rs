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

#[test]
fn predicate_domain_wd_gcd_accepts_a_checked_nonzero_disjunction() {
    for code in [
        "forall x, y N:\n    $coprime(x, y)\n    =>:\n        $coprime(x, y)\n",
        include_str!("../../../../examples/wd/gcd_nonzero_disjunction.lit"),
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(run.success, "{code}");
        let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
        if code.contains("gcd(") {
            assert!(detail.contains("by_known_or") || detail.contains("by_selected_branch"), "{detail}");
        }
        assert_eq!(rt.execution_environments_stack.len(), 1);
        // The disjunction neither chooses a branch nor admits the all-zero pair.
        for negative in ["gcd(0, 0) = gcd(0, 0)\n", "0 = 1\n"] {
            let rejected = rt.run_litex_code(negative).unwrap();
            assert!(rejected.session_error.is_none());
            assert!(!rejected.success, "{negative}");
        }
    }
}

#[test]
fn predicate_domain_wd_gcd_nonzero_pair_is_symmetric_without_selecting_an_operand() {
    for code in [
        "forall a, b Z:\n    a != 0 or b != 0\n    =>:\n        gcd(b, a) = gcd(b, a)\n",
        "forall a, b Z:\n    b != 0 or a != 0\n    =>:\n        gcd(a, b) = gcd(a, b)\n",
        "claim:\n    ? forall a, b Z:\n        a != 0 or b != 0\n        =>:\n            gcd(b, a) = gcd(b, a)\n    gcd(b, a) = gcd(b, a)\n",
    ] {
        let mut rt = runtime();
        let run = rt.run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(run.success, "{code}");
        let detail = crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
        assert!(detail.contains("by_known_or"), "{detail}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
        for rejected in [
            "gcd(0, 0) = gcd(0, 0)\n",
            "forall a, b Z:\n    a != 0 or b != 0\n    =>:\n        a != 0\n",
            "forall a, b Z:\n    a != 0 or b != 0\n    =>:\n        b != 0\n",
            "gcd(0.5, 1) = gcd(0.5, 1)\n",
        ] {
            let run = rt.run_litex_code(rejected).unwrap();
            assert!(run.session_error.is_none(), "{rejected}: {:?}", run.session_error);
            assert!(!run.success, "{rejected}");
            assert_eq!(rt.execution_environments_stack.len(), 1);
        }
    }
}

#[test]
fn predicate_domain_wd_does_not_reopen_anonymous_function_peers() {
    // The stored `prior = fn(n N) N {1}` provides an equality peer.
    // Checking an unrelated numeric domain must not enter its binder again.
    for (body, expected) in [
        ("have n N\n0 <= n\n", true),
        ("have A set = R\nhave x A = 0\nx <= 1\n", true),
        ("forall x C:\n    x >= 0\n    =>:\n        x >= 0\n", false),
    ] {
        let mut rt = runtime();
        let code = format!("have fn prior(n N) N = 1\n{body}");
        let run = rt.run_litex_code(&code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert_eq!(run.success, expected, "{code}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
        assert!(!rt.run_litex_code("0 = 1\n").unwrap().success);
    }
}

#[test]
fn predicate_domain_wd_requires_the_numeric_domain_before_assuming_a_fact() {
    for (header, atom) in [
        ("x R", "$prime(x)"),
        ("x R", "$coprime(x, 1)"),
        ("x R", "$dvd(x, 1)"),
        ("x Z", "$dvd(x, 0)"),
        ("x C", "x < 0"),
        ("x C", "x > 0"),
        ("x C", "x <= 0"),
        ("x C", "x >= 0"),
        ("x R", "$injective(R, R, x)"),
        ("x R", "$surjective(R, R, x)"),
        ("x R", "$bijective(R, R, x)"),
        ("x R", "$is_choice_function_for(R, R, x, x)"),
    ] {
        for polarity in ["", "not "] {
            let code = format!(
                "forall {header}:\n    {polarity}{atom}\n    =>:\n        {polarity}{atom}\n"
            );
            let mut rt = runtime();
            let run = rt.run_litex_code(&code).unwrap();
            assert!(
                run.session_error.is_none(),
                "{code}: {:?}",
                run.session_error
            );
            assert!(!run.success, "{code}");
            let detail = format!(
                "{:?}",
                crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
            );
            assert!(detail.contains("predicate_domain"), "{code}: {detail}");
            assert_eq!(rt.execution_environments_stack.len(), 1);
            assert!(!rt.run_litex_code("0 = 1\n").unwrap().success);
        }
    }
}

#[test]
fn predicate_domain_wd_checks_valid_function_and_choice_signatures() {
    for atom in [
        "$injective(A, B, f)",
        "$surjective(A, B, f)",
        "$bijective(A, B, f)",
    ] {
        let code = format!("forall A, B set, f fn(x A) B:\n    {atom}\n    =>:\n        {atom}\n");
        let run = runtime().run_litex_code(&code).unwrap();
        assert!(run.success, "{code}: {:?}", run.session_error);
    }
    let code = "forall I, S set, g fn(x I) S, f fn(x I) family_union(S):\n    $is_choice_function_for(I, S, g, f)\n    =>:\n        $is_choice_function_for(I, S, g, f)\n";
    let run = runtime().run_litex_code(code).unwrap();
    assert!(run.success, "{:?}", run.session_error);
}

#[test]
fn predicate_domain_wd_valid_domains_and_prior_carrier_facts_succeed() {
    let mut rt = runtime();
    let run = rt
        .run_litex_code(include_str!(
            "../../../../examples/wd/predicate_numeric_domains.lit"
        ))
        .unwrap();
    assert!(run.success, "{:?}", run.session_error);
    let detail = format!(
        "{:?}",
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt)
    );
    assert!(detail.contains("predicate_domain"), "{detail}");
    assert!(detail.contains("requirement"), "{detail}");
    assert!(
        rt.run_litex_code("forall x R:\n    x $in N\n    $prime(x)\n    =>:\n        $prime(x)\n")
            .unwrap()
            .success
    );
    assert!(
        !rt.run_litex_code("forall x R:\n    $prime(x)\n    x $in N\n    =>:\n        $prime(x)\n")
            .unwrap()
            .success
    );
}

#[test]
fn retired_dimension_interfaces_reject_and_current_coordinate_carriers_remain_usable() {
    for source in ["cart_dim(A) $in N", "tuple_dim(0) $in N", "cart_dim(A)=2"] {
        let mut rt=runtime();
        assert!(rt.run_litex_code("have A set=cart(R,R)").unwrap().success);
        let result=rt.run_litex_code(source).unwrap();
        assert!(!result.success && result.session_error.is_some(), "{source}");
        assert!(result.statement_results.is_empty());
    }
    let mut rt=runtime();
    assert!(rt.run_litex_code("have p cart(R,R)\np(1) $in R\np(2) $in R").unwrap().success);
    for wrong in ["p(3) $in R", "0=1"] { assert!(!rt.run_litex_code(wrong).unwrap().success); }
}

#[test]
fn predicate_domain_wd_anonymous_function_signature_has_exact_boundaries() {
    let mut rt = runtime();
    let run = rt.run_litex_code(include_str!("../../../../examples/proof_nodes/atomic/by_builtin_rule/anonymous_function_declared_signature.lit")).unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(run.success);
    let detail =
        crate::json_output::project_stmt_detailed(&run.statement_results[0], &rt).stringify();
    assert!(detail.contains("AnonymousFnInDeclaredFnSet"), "{detail}");
    for code in [
        "fn(x R) R {x} $in fn(y N) R\n",
        "fn(x R) R {x} $in fn(y R) N\n",
        "fn(x R: x > 0) R {1 / x} $in fn(y R) R\n",
        "fn(x R) R {1 / 0} $in fn(y R) R\n",
        "have A set = R\nhave B set = N\nfn(x A) A {x} $in fn(y B) A\n",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(!run.success, "{code}");
    }
}

#[test]
fn predicate_domain_wd_restores_choice_release_without_weakening_signature() {
    let run = runtime()
        .run_litex_code(include_str!(
            "../../../../examples/test_statements/release_axiom_of_choice_stmt.lit"
        ))
        .unwrap();
    assert!(run.session_error.is_none(), "{:?}", run.session_error);
    assert!(run.success);
    for code in [
        "forall F set, f fn(A F) family_union(F):\n    $is_choice_function_for(F, F, fn(B F) F {B}, f)\n    =>:\n        $is_choice_function_for(F, F, fn(B F) F {B}, f)\n",
        "forall F set, f R:\n    $is_choice_function_for(F, F, fn(B F) F {B}, f)\n    =>:\n        $is_choice_function_for(F, F, fn(B F) F {B}, f)\n",
    ] {
        let run = runtime().run_litex_code(code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert_eq!(run.success, !code.contains("f R"), "{code}");
    }
}

#[test]
fn predicate_domain_wd_preserves_equal_carriers_and_the_exact_one_based_prefix() {
    for atom in ["$injective", "$surjective", "$bijective"] {
        for (setup, domain, codomain) in [
            ("have A set = R\nhave fn f(x A) A = x\n", "R", "R"),
            ("have fn f(k N+: k <= 2) R = 0\n", "closed_range(1, 2)", "R"),
        ] {
            let code = format!("{setup}forall t R:\n    {atom}({domain}, {codomain}, f)\n    =>:\n        {atom}({domain}, {codomain}, f)\n");
            let mut rt = runtime();
            let run = rt.run_litex_code(&code).unwrap();
            assert!(
                run.session_error.is_none(),
                "{code}: {:?}",
                run.session_error
            );
            assert!(run.success, "{code}");
            let detail = crate::json_output::project_stmt_detailed(
                run.statement_results.last().unwrap(),
                &rt,
            )
            .stringify();
            assert!(detail.contains("predicate_domain"), "{detail}");
            assert!(
                detail.contains("by_known_atomic"),
                "signature must cite its actual stored type: {detail}"
            );
        }
    }
    for (signature, domain, codomain) in [
        ("fn(k N+: k <= 2) R", "closed_range(0, 2)", "R"),
        ("fn(k N+: k <= 2) R", "closed_range(1, 3)", "R"),
        ("fn(k N+: k < 2) R", "closed_range(1, 2)", "R"),
        ("fn(k N+: k <= 2) R", "closed_range(1, 2)", "N"),
        ("fn(k N: k <= 2) R", "closed_range(1, 2)", "R"),
    ] {
        let code = format!("forall f {signature}:\n    $injective({domain}, {codomain}, f)\n    =>:\n        $injective({domain}, {codomain}, f)\n");
        let run = runtime().run_litex_code(&code).unwrap();
        assert!(
            run.session_error.is_none(),
            "{code}: {:?}",
            run.session_error
        );
        assert!(!run.success, "{code}");
    }
}

#[test]
fn predicate_domain_wd_closed_negative_carriers_terminate_and_positive_integer_evidence_remains() {
    let run = runtime().run_litex_code(include_str!(
        "../../../../examples/wd/predicate_positive_integer_carrier.lit"
    )).unwrap();
    assert!(run.success, "{:?}", run.session_error);
    for carrier in ["Z", "N", "N+"] {
        let mut rt = runtime();
        let code = format!("1 / 2 $in {carrier}\n");
        let run = rt.run_litex_code(&code).unwrap();
        assert!(run.session_error.is_none(), "{code}: {:?}", run.session_error);
        assert!(!run.success, "{code}");
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}
