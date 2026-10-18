use crate::prelude::*;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}
fn check(rt: &mut Runtime, source: &str, success: bool) -> RunLitexCodeResult {
    let run = rt.run_litex_code(source).unwrap();
    assert!(
        run.session_error.is_none(),
        "{source}: {:?}",
        run.session_error
    );
    assert_eq!(run.success, success, "{source}");
    run
}

#[test]
fn dvd_unified_native_producers_and_complete_irrationality() {
    for source in [
        include_str!("../../../examples/proof_nodes/atomic/by_builtin_rule/dvd_unified.lit"),
        "forall d Z*:\n    $dvd(0,d)\n",
        "forall a Z:\n    $dvd(a,1)\n",
        "forall a Z*:\n    $dvd(a,a)\n",
        "forall a Z*,b Z:\n    $dvd(a*b,a)\n    $dvd(b*a,a)\n",
        "forall a,b Z*:\n    $dvd(a,gcd(a,b))\n    $dvd(b,gcd(a,b))\n    $dvd(lcm(a,b),abs(a))\n    $dvd(lcm(a,b),abs(b))\n",
        "forall a Z,d Z*:\n    $dvd(a-a%d,d)\n",
        "forall a,b Z*,d N+:\n    $dvd(a,d)\n    $dvd(b,d)\n    =>:\n        $dvd(gcd(a,b),d)\n        d<=gcd(a,b)\n",
        "forall a,b N+,m Z:\n    $dvd(m,a)\n    $dvd(m,b)\n    =>:\n        $dvd(m,lcm(a,b))\n",
        "forall m,n N:\n    m<=n\n    =>:\n        $dvd(n!,m!)\n",
        "forall a,b Z:\n    b!=0\n    $dvd(a,b)\n    =>:\n        (a/b)^2 $in Z\n",
        "forall a N+:\n    $dvd(a,2)\n    =>:\n        1<a\n",
        "forall a,b Z*,m N+:\n    $dvd(m,abs(a))\n    $dvd(m,abs(b))\n    =>:\n        lcm(a,b)<=m\n",
        "forall a Z,m,d N+:\n    $dvd(m,d)\n    =>:\n        a%d=(a%m)%d\n",
    ] {
        check(&mut runtime(OutputLanguage::English), source, true);
    }
}

#[test]
fn dvd_unified_rejects_noninteger_factors_invalid_domains_and_missing_premises() {
    for source in [
        "$dvd(2*(1/2),2)",
        "$dvd((1/2)*2,2)",
        "$dvd(2*i,2)",
        "$dvd(0,0)",
        "$dvd(4,0)",
        "$dvd(1,2)",
        "$dvd(4,3)",
        "forall k R:\n    2*k $in Z\n    =>:\n        $dvd(2*k,2)\n",
        "forall a,b Z:\n    $dvd(a*b,a)\n",
        "forall a,b Z*:\n    $dvd(lcm(a,b),abs(a)+1)\n",
        "forall a,b Z*,d N+:\n    $dvd(a,d)\n    =>:\n        $dvd(gcd(a,b),d)\n",
        "forall a,b N+,m Z:\n    $dvd(m,a)\n    =>:\n        $dvd(m,lcm(a,b))\n",
        "forall m,n N:\n    $dvd(n!,m!)\n",
        "forall a,b Z:\n    b!=0\n    =>:\n        (a/b)^2 $in Z\n",
        "forall a,b Z:\n    b!=0\n    $dvd(a,b)\n    =>:\n        a/b $in N+\n",
        "not sqrt(4) $in Q",
    ] {
        check(&mut runtime(OutputLanguage::English), source, false);
    }
    let false_proof =
        include_str!("../../../examples/proof_nodes/atomic/by_builtin_rule/dvd_unified.lit")
            .replace("sqrt(2)", "sqrt(4)")
            .replace("p^2 = 2 * q^2", "p^2 = 4 * q^2")
            .replace("q^2 = p^2 / 2 = 2 * (p / 2)^2", "q^2 = p^2 / 4 = (p / 2)^2");
    check(&mut runtime(OutputLanguage::English), &false_proof, false);
}

#[test]
fn dvd_unified_zero_remainder_compatibility_is_read_only_and_scope_bound() {
    let mut rt = runtime(OutputLanguage::English);
    check(&mut rt, "have k Z\nhave a Z=2*k", true);
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("$dvd(a,2)", rt.current_file.clone())
        .unwrap();
    let Stmt::Fact(fact) = rt.parse(&tokens).unwrap().remove(0) else {
        panic!("fact")
    };
    assert!(rt
        .verify_fact(&fact, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
    let before = rt.top_exec_env().facts.facts_by_id.len();
    rt.run_in_local_env_and_take_env(|rt| {
        check(rt, "a%2=(2*k)%2=0", true);
        let stored = rt.top_exec_env().facts.facts_by_id.len();
        assert!(!rt
            .verify_fact(&fact, VerifyState::new(VerifyStateLevel::Direct))?
            .is_failed());
        assert_eq!(stored, rt.top_exec_env().facts.facts_by_id.len());
        Ok(())
    })
    .unwrap();
    assert_eq!(before, rt.top_exec_env().facts.facts_by_id.len());
    assert!(rt
        .verify_fact(&fact, VerifyState::new(VerifyStateLevel::Direct))
        .unwrap()
        .is_failed());
}

#[test]
fn dvd_unified_actual_certificates_and_all_locales() {
    for language in OutputLanguage::ALL {
        let mut rt = runtime(language);
        check(&mut rt, "have d Z*,k Z", true);
        let run = check(&mut rt, "$dvd(d*k,d)", true);
        let detail =
            crate::json_output::project_run_detailed(&run, &rt, "eval", None).stringify_pretty();
        assert!(
            detail.contains("DvdProductFactor") && detail.contains("multiplier_integer"),
            "{detail}"
        );
        assert!(
            detail.contains(&crate::json_output::json_keys::localize_key(
                "cite_fact_id",
                language
            )),
            "{detail}"
        );
        let normal =
            crate::json_output::project_run_normal(&run, &rt, "eval", None).stringify_pretty();
        assert!(
            !normal.contains("unreachable") && !normal.contains("unsupported"),
            "{normal}"
        );
        let run = check(
            &mut rt,
            "forall a,b Z:\n    b!=0\n    a%b=0\n    =>:\n        $dvd(a,b)\n",
            true,
        );
        let detail =
            crate::json_output::project_run_detailed(&run, &rt, "eval", None).stringify_pretty();
        assert!(
            detail.contains("by_known_zero_remainder") && detail.contains("zero_remainder"),
            "{detail}"
        );
    }
}
