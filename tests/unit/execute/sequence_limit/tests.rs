use crate::execute::execute_fact_stmt::VerifyStateLevel;
use crate::prelude::*;

#[test]
fn sequence_limit_tests_negation_preserves_payload_with_fresh_fact_ids() {
    let mut rt = runtime();
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("$has_seq_limit(fn(k N+) R {0},0)", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(Fact::AtomicFact(original)) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("native candidate")
    };
    let negative_id = rt.global_ids.allocate_fact_id();
    let negative = crate::ast::fact::negate_atomic_fact(&original, negative_id).unwrap();
    assert_eq!(negative.fact_id(), negative_id);
    assert_ne!(negative.fact_id(), original.fact_id());
    assert!(matches!(negative, AtomicFact::NotHasSequenceLimitFact(_)));
    let positive_id = rt.global_ids.allocate_fact_id();
    let positive = crate::ast::fact::negate_atomic_fact(&negative, positive_id).unwrap();
    assert_eq!(positive.fact_id(), positive_id);
    assert_eq!(positive.readable_string(), original.readable_string());
}

#[test]
fn sequence_limit_tests_durable_examples() {
    for source in [
        include_str!("../../../../examples/wd/sequence_limit.lit"),
        include_str!("../../../../examples/wd/sequence_limit_interfaces.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_from_epsilon.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_tail.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_constant.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_neg.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_abs.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_scale.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_power.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_add.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_subtract.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_multiply.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_divide.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_eventually_equal.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_shift.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_compare.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_squeeze.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_unique.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_exists.lit"),
        include_str!("../../../../examples/stmt_nodes/release_and_expand/builtin_thm/seq_limit_selected.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/sequence_limit_selected.lit"),
        include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/sequence_limit_unique.lit"),
    ] {check(&mut runtime(),source,true);}
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}
fn check(rt: &mut Runtime, code: &str, wanted: bool) {
    let run = rt.run_litex_code(code).expect("public runtime");
    assert!(
        run.session_error.is_none(),
        "hard error in {code}: {:?}",
        run.session_error
    );
    assert_eq!(
        run.success,
        wanted,
        "{code}\n{}",
        crate::json_output::project_run_detailed(&run, rt, "eval", None).stringify_pretty()
    );
}
#[test]
fn sequence_limit_tests_requires_proof_and_keeps_context() {
    let mut rt = runtime();
    check(&mut rt, "have fn a(k N+) R = 1/k", true);
    check(&mut rt, "lim(a)=0", false);
    check(&mut rt, "lim(a) $in R", false);
    check(&mut rt, "0*lim(a)=0", false);
    check(&mut rt, "a(2)=1/2", true);
    check(&mut rt, "have fn c(k N+) R = 3", true);
    check(&mut rt, "lim(c)=3", false);
    check(&mut rt, "release thm seq_limit_constant(c,3)", true);
    check(&mut rt, "lim(c)=3", true);
    check(&mut rt, "lim(c)+2=5", true);
    check(&mut rt, "lim(c) $in R", true);
    check(&mut rt, "lim(c)=4", false);
    check(&mut rt, "a(3)=1/3", true);
}
#[test]
fn sequence_limit_tests_equivalent_interfaces_and_arbitrary_existence() {
    for space in ["seq(R)", "fn(k N+) R"] {
        check(&mut runtime(),&format!("forall a {space}, L R:\n    $has_seq_limit(a,L)\n    =>:\n        lim(a)=L\n        lim(a) $in R"),true);
        check(&mut runtime(),&format!("forall a {space}:\n    exist L R st {{$has_seq_limit(a,L)}}\n    =>:\n        lim(a) $in R"),true);
    }
}
#[test]
fn sequence_limit_tests_algebra_from_proved_candidates() {
    for (theorem, result) in [
        (
            "seq_limit_add(a,b,A,B)",
            "$has_seq_limit(fn(k N+) R {a(k)+b(k)},A+B)",
        ),
        (
            "seq_limit_subtract(a,b,A,B)",
            "$has_seq_limit(fn(k N+) R {a(k)-b(k)},A-B)",
        ),
        (
            "seq_limit_multiply(a,b,A,B)",
            "$has_seq_limit(fn(k N+) R {a(k)*b(k)},A*B)",
        ),
        (
            "seq_limit_neg(a,A)",
            "$has_seq_limit(fn(k N+) R {-a(k)},-A)",
        ),
        (
            "seq_limit_abs(a,A)",
            "$has_seq_limit(fn(k N+) R {abs(a(k))},abs(A))",
        ),
        (
            "seq_limit_scale(a,A,2)",
            "$has_seq_limit(fn(k N+) R {2*a(k)},2*A)",
        ),
        (
            "seq_limit_power(a,A,2)",
            "$has_seq_limit(fn(k N+) R {a(k)^2},A^2)",
        ),
    ] {
        let code=format!("thm law:\n    ? forall a,b seq(R),A,B R:\n        $has_seq_limit(a,A)\n        $has_seq_limit(b,B)\n        =>:\n            {result}\n    by thm {theorem} => {result}");
        check(&mut runtime(), &code, true);
    }
}
#[test]
fn sequence_limit_tests_domains_and_false_neighbors() {
    for code in [
        "lim(3)=0",
        "lim(fn(k N) R {0})=0",
        "lim(fn(k {1,2}) R {0})=0",
        "lim(fn(k N+:k>1) R {1/(k-1)})=0",
        "lim(fn(k N+) C {i})=0",
        "$has_seq_limit(3,0)",
        "$has_seq_limit(fn(k N+) R {0},i)",
        "have fn c(k N+) R = 3\nrelease thm seq_limit_constant(c,4)",
        "have fn a(k N+) R = (-1)^k\nlim(a)=0",
        "have fn a(k N+) R = k\nlim(a)=0",
        "have fn b(k N+) R = 1-1/k\nrelease thm seq_limit_constant(b,1)",
    ] {
        check(&mut runtime(), code, false);
    }
}
#[test]
fn sequence_limit_tests_uniqueness_exists_and_selected_relation() {
    check(&mut runtime(),"forall a seq(R),L,M R:\n    $has_seq_limit(a,L)\n    $has_seq_limit(a,M)\n    =>:\n        L=M",true);
    check(&mut runtime(),"thm selected:\n    ? forall a seq(R),L R:\n        $has_seq_limit(a,L)\n        =>:\n            $has_seq_limit(a,lim(a))\n    release thm seq_limit_exists(a,L)\n    release thm seq_limit_selected(a)",true);
}
#[test]
fn sequence_limit_tests_substitution_congruence_latex_and_reserved_names() {
    check(
        &mut runtime(),
        "forall a,b seq(R),L R:\n    a=b\n    $has_seq_limit(a,L)\n    =>:\n        lim(a)=lim(b)",
        true,
    );
    let latex = crate::compile_to_latex::to_latex_from_source(
        "forall a seq(R),L R:\n    $has_seq_limit(a,L)\n    =>:\n        lim(a)=L",
        OutputLanguage::English,
    )
    .unwrap();
    assert!(latex.contains("lim"));
    for code in [
        "have lim R=1",
        "prop has_seq_limit(a seq(R),L R):\n    L=L",
        "lim()=0",
        "lim(1,2,3)=0",
        "$has_seq_limit(1)",
        "$has_seq_limit(1,2,3)",
    ] {
        let mut rt = runtime();
        let tokens = crate::tokenize::Tokenizer::new()
            .tokenize(code, rt.current_file.clone())
            .unwrap();
        assert!(rt.parse(&tokens).is_err(), "reserved: {code}");
    }
}

#[test]
fn sequence_limit_tests_evidence_permission_and_lean_boundary() {
    let source = "forall a seq(R),L R:\n    $has_seq_limit(a,L)\n    =>:\n        lim(a)=L";
    let mut rt = runtime();
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(source, rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    assert!(rt
        .verify_fact(&fact, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
    assert!(!rt
        .verify_fact(&fact, VerifyState::new(VerifyStateLevel::BuiltinRule))
        .unwrap()
        .is_failed());
    let run = rt.run_litex_code(source).unwrap();
    assert!(run.success && run.session_error.is_none());
    let detailed =
        crate::json_output::project_run_detailed(&run, &rt, "eval", None).stringify_pretty();
    for fragment in [
        "SequenceLimitSelectedValue",
        "sequence_wd",
        "sequence_domain",
        "convergence",
    ] {
        assert!(
            detailed.contains(fragment),
            "missing {fragment}: {detailed}"
        );
    }
    let error = crate::compile_to_lean::LitexToLeanCompiler::new(rt)
        .compile_run(&run, "sequence_limit_boundary")
        .unwrap_err();
    assert!(error.message.contains("not supported"), "{error}");
    let latex = crate::compile_to_latex::to_latex_from_source(
        "forall n seq(R),L R:\n    $has_seq_limit(n,L)\n    =>:\n        lim(n)=L",
        OutputLanguage::English,
    )
    .unwrap();
    assert!(
        latex.contains("\\lim_{\\mathit{nn}\\to\\infty}"),
        "capture avoidance: {latex}"
    );
}

#[test]
fn sequence_limit_tests_reject_missing_limit_and_tail_premises() {
    for code in [
        "have fn a(k N+) R=0\nrelease thm seq_limit_add(a,a,0,0)",
        "have fn a(k N+) R=0\nrelease thm seq_limit_neg(a,0)",
        "have fn a(k N+) R=0\nrelease thm seq_limit_shift(a,0,1)",
        "have fn a(k N+) R=0\nrelease thm seq_limit_exists(a,0)",
        "have fn a(k N+) R=0\nrelease thm seq_limit_selected(a)",
        "have fn a(k N+) R=0\nrelease thm seq_limit_constant(a,0)\nrelease thm seq_limit_tail(a,0,0)",
        "have fn a(k N+) R=0\nrelease thm seq_limit_constant(a,0)\nrelease thm seq_limit_scale(a,0,i)",
        "have fn a(k N+) R=1\nrelease thm seq_limit_constant(a,1)\nrelease thm seq_limit_power(a,1,-1)",
        "have fn a(k N+) R=0\nhave fn b(k N+) R=1\nrelease thm seq_limit_constant(a,0)\nrelease thm seq_limit_constant(b,1)\nrelease thm seq_limit_eventually_equal(a,b,0,1)",
        "have fn a(k N+) R=1\nhave fn b(k N+) R=0\nrelease thm seq_limit_constant(a,1)\nrelease thm seq_limit_constant(b,0)\nrelease thm seq_limit_compare(a,b,1,0,1)",
        "have fn a(k N+) R=0\nhave fn b(k N+) R=1\nrelease thm seq_limit_constant(a,0)\nrelease thm seq_limit_squeeze(a,b,a,0,1)",
        "have fn a(k N+) R=0\nnot $has_seq_limit(a,1)",
    ] {check(&mut runtime(),code,false);}
    for space in ["seq(R)", "fn(k N+) R"] {
        check(&mut runtime(),&format!("forall a {space},L R:\n    not $has_seq_limit(a,L)\n    =>:\n        not $has_seq_limit(a,L)"),true);
    }
    check(&mut runtime(),"claim:\n    ? forall a,b seq(R),A,B R:\n        $has_seq_limit(a,A)\n        $has_seq_limit(b,B)\n        forall k N+:\n            b(k)!=0\n        =>:\n            $has_seq_limit(fn(k N+) R {a(k)/b(k)},A/B)\n    release thm seq_limit_divide(a,b,A,B)",false);
}

#[test]
fn sequence_limit_tests_explicit_epsilon_proof_then_selection() {
    let mut rt = runtime();
    check(&mut rt, "have fn a(k N+) R = 1/k", true);
    check(
        &mut rt,
        r#"claim:
    ? forall epsilon R+:
        exist n0 N+ st {{n N+: n >= n0} $subset preimage_set(a,{v R: abs(v-0) < epsilon})}
    release thm real_archimedean_natural_upper_bound(1/epsilon)
    obtain n0 from exist n0 N+ st {1/epsilon < n0}
    0 < n0
    (1/epsilon)*epsilon < n0*epsilon
    (1/epsilon)*epsilon = 1
    1 < n0*epsilon
    1/n0 < (n0*epsilon)/n0
    (n0*epsilon)/n0 = epsilon
    1/n0 < epsilon
    claim:
        ? forall k N+:
            k >= n0
            =>:
                abs(a(k)-0) < epsilon
        0 < n0*k
        1/k = n0/(n0*k)
        n0/(n0*k) <= k/(n0*k)
        k/(n0*k) = 1/n0
        1/k <= 1/n0 < epsilon
        a(k)-0 = a(k) = 1/k
        0 < 1/k
        abs(a(k)-0) = abs(1/k)
        abs(1/k) = 1/k < epsilon
    witness exist cutoff N+ st {{k N+: k >= cutoff} $subset preimage_set(a,{v R: abs(v-0) < epsilon})} from n0:
        claim:
            ? forall k {j N+: j >= n0}:
                k $in preimage_set(a,{v R: abs(v-0) < epsilon})
            abs(a(k)-0) < epsilon
        by def {k N+: k >= n0} $subset preimage_set(a,{v R: abs(v-0) < epsilon})
"#,
        true,
    );
    check(&mut rt, "lim(a)=0", false);
    check(&mut rt, "by def $has_seq_limit(a,0)", true);
    check(&mut rt, "lim(a)=0", true);
    check(&mut rt, "lim(a)+2=2", true);
    check(&mut rt, "release thm seq_limit_tail(a,0,1/10)", true);
    check(&mut rt, "release thm seq_limit_from_epsilon(a,1)", false);
}

#[test]
fn sequence_limit_tests_remaining_laws_and_missing_premises() {
    for (params,premises,theorem,goal) in [
        ("a,b seq(R),A,B R", "$has_seq_limit(a,A)\n$has_seq_limit(b,B)\nB!=0\nforall k N+:\n    b(k)!=0", "seq_limit_divide(a,b,A,B)", "$has_seq_limit(fn(k N+) R {a(k)/b(k)},A/B)"),
        ("a,b seq(R),L R,cutoff N+", "$has_seq_limit(a,L)\nforall k N+:\n    k>=cutoff\n    =>:\n        a(k)=b(k)", "seq_limit_eventually_equal(a,b,L,cutoff)", "$has_seq_limit(b,L)"),
        ("a seq(R),L R,m N", "$has_seq_limit(a,L)", "seq_limit_shift(a,L,m)", "$has_seq_limit(fn(k N+) R {a(k+m)},L)"),
        ("a,b seq(R),A,B R,cutoff N+", "$has_seq_limit(a,A)\n$has_seq_limit(b,B)\nforall k N+:\n    k>=cutoff\n    =>:\n        a(k)<=b(k)", "seq_limit_compare(a,b,A,B,cutoff)", "A<=B"),
        ("a,b,c seq(R),L R,cutoff N+", "$has_seq_limit(a,L)\n$has_seq_limit(c,L)\nforall k N+:\n    k>=cutoff\n    =>:\n        a(k)<=b(k)\n        b(k)<=c(k)", "seq_limit_squeeze(a,b,c,L,cutoff)", "$has_seq_limit(b,L)"),
    ] {
        let premise_lines=premises.lines().map(|line|format!("        {line}\n")).collect::<String>();
        let code=format!("claim:\n    ? forall {params}:\n{premise_lines}        =>:\n            {goal}\n    by thm {theorem} => {goal}");
        check(&mut runtime(),&code,true);
    }
    for code in [
        "claim:\n    ? forall a,b seq(R),A,B R:\n        $has_seq_limit(a,A)\n        $has_seq_limit(b,B)\n        B!=0\n        =>:\n            $has_seq_limit(fn(k N+) R {a(k)/b(k)},A/B)\n    release thm seq_limit_divide(a,b,A,B)",
        "have fn a(k N+) R = 1/k\nrelease thm seq_limit_from_epsilon(a,0)",
        "forall a seq(R):\n    $has_seq_limit(a,lim(a))\n    =>:\n        lim(a)=0",
        "$has_seq_limit(fn(k,j N+) R {0},0)",
        "$has_seq_limit(fn(k N) R {0},0)",
    ] {check(&mut runtime(),code,false);}
    for code in [
        "forall a,b seq(R),A,B R:\n    B!=0\n    forall k N+:\n        b(k)!=0\n    $has_seq_limit(fn(k N+) R {a(k)/b(k)},A/B)\n    =>:\n        lim(fn(k N+) R {a(k)/b(k)})=A/B",
        "forall a seq(R),L R,m N:\n    $has_seq_limit(fn(k N+) R {a(k+m)},L)\n    =>:\n        lim(fn(k N+) R {a(k+m)})=L",
    ] {check(&mut runtime(),code,true);}
}
