//! Native codomains must work through ordinary WD and preserve domain failures.
use crate::execute::ExecStmtResult;
use crate::json_output::{project_stmt_detailed, project_stmt_normal};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime(language: OutputLanguage) -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language,
    })
}

fn exec(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    let mut last = None;
    for stmt in stmts {
        if let Some(previous) = &last {
            assert!(!ExecStmtResult::is_failed(previous), "setup failed: {code}");
        }
        last = Some(runtime.exec_stmt(&stmt).expect("exec_stmt"));
    }
    last.expect("at least one statement")
}

fn assert_accepts(code: &str) {
    let mut rt = runtime(OutputLanguage::English);
    let result = exec(&mut rt, code);
    assert!(
        !result.is_failed(),
        "{code}\n{}",
        project_stmt_normal(&result, &rt).stringify_pretty(),
    );
}

fn has_field(value: &JsonValue, key: &str, expected: &str) -> bool {
    match value {
        JsonValue::Object(map) => {
            map.get(key).and_then(|v| v.as_str().ok()) == Some(expected)
                || map
                    .keys_in_order()
                    .iter()
                    .any(|k| has_field(map.get(k).unwrap(), key, expected))
        }
        JsonValue::Array(values) => values.iter().any(|v| has_field(v, key, expected)),
        _ => false,
    }
}

#[test]
fn signed_carrier_nonzero_inference_is_known() {
    for carrier in ["N+", "Q+", "R+", "Q-", "Z-", "R-"] {
        let mut rt = runtime(OutputLanguage::English);
        assert!(!exec(&mut rt, &format!("have x {carrier}")).is_failed());
        let result = exec(&mut rt, "x != 0");
        assert!(!result.is_failed());
        assert!(has_field(&project_stmt_normal(&result, &rt), "type", "cite_known"));
    }
    let mut rt = runtime(OutputLanguage::English);
    assert!(exec(&mut rt, "have x R+ = 0").is_failed());
    assert!(exec(&mut rt, "$dvd(1, 0)").is_failed());
    let mut rt = runtime(OutputLanguage::English);
    assert!(!exec(&mut rt, "have x N").is_failed());
    assert!(exec(&mut rt, "x != 0").is_failed());
}

#[test]
fn positive_divisor_builder_inference_preserves_wd() {
    let mut rt = runtime(OutputLanguage::English);
    assert!(!exec(&mut rt, "have a, b Z").is_failed());
    // The direct carrier check must return a checked outcome, never InternalBug.
    // Its automatic subset proof is a separate capability from this inference.
    exec(&mut rt, "have c power_set(N) = {d N+: $dvd(a, d), $dvd(b, d)}");
    let mut rt = runtime(OutputLanguage::English);
    assert!(!exec(&mut rt, "have a, b Z").is_failed());
    let result = exec(&mut rt, "have c set = {d N+: $dvd(a, d), $dvd(b, d)}");
    assert!(!result.is_failed(), "{}", project_stmt_detailed(&result, &rt).stringify_pretty());
    assert!(!exec(&mut rt, "forall d c:\n    d $in N").is_failed());
    assert!(!exec(&mut rt, "by def c $subset N").is_failed());
    assert!(!exec(&mut rt, "c $in power_set(N)").is_failed());
}

#[test]
fn native_scalar_codomain_symbolic_memberships_and_supertypes() {
    let cases = [
        ("have a R", "sign(a)", vec!["Z", "Q", "R", "C"]),
        (
            "have a Z*\nhave b Z",
            "gcd(a, b)",
            vec!["N+", "N", "Z", "Q", "R", "Z*", "Q+", "R+", "Q*", "R*", "C"],
        ),
        (
            "have a Z\nhave b Z",
            "lcm(a, b)",
            vec!["N", "Z", "Q", "R", "C"],
        ),
        ("have x R", "exp(x)", vec!["R+", "R", "R*", "C"]),
        (
            "have n N",
            "n!",
            vec!["N+", "N", "Z", "Q", "R", "Z*", "Q+", "R+", "Q*", "R*", "C"],
        ),
    ];
    for (setup, obj, sets) in cases {
        for set in sets {
            // Fresh runtime: a previous stronger membership cannot mask a gap.
            assert_accepts(&format!("{setup}\n{obj} $in {set}"));
        }
    }
}

#[test]
fn native_scalar_codomain_nested_wd_needs_no_stored_carrier() {
    for code in [
        "have a R\nsign(0 - a) = 0 - sign(a)",
        "have a R\nsign(a) * abs(a) = a",
        "have a R\nabs(a) = sign(a) * a",
        "have a R\nhave b R\nsign(a * b) = sign(a) * sign(b)",
        "have a Z*\nhave b Z*\nlcm(a, b) * gcd(a, b) = abs(a * b)",
        "have a Z*\nhave b Z\na % gcd(a, b) = 0",
        "have x R\nln(exp(x)) = x",
        "have n N\n(n + 1)! = (n + 1) * n!",
        "have n N\nfactorial(n) $in N+",
        "have x R\ngcd(sign(x), 1) $in N+",
    ] {
        assert_accepts(code);
    }
}

#[test]
fn native_scalar_codomain_checked_membership_supplies_nonzero_inference() {
    // Division requires a separate != 0 obligation. The existing store/infer
    // path obtains it from a checked positive carrier; no trusted fact needed.
    for code in [
        "have a R\nexp(a) $in R+\n1 / exp(a) $in R",
        "have a Z*\nhave b Z\ngcd(a, b) $in N+\n1 / gcd(a, b) $in R",
        "have n N\nn! $in N+\n1 / n! $in R",
    ] {
        assert_accepts(code);
    }
}

#[test]
fn native_scalar_codomain_zero_and_signed_inputs() {
    for code in [
        "sign(0) $in Z",
        "sign(-1) $in Z",
        "gcd(0, -2) $in N+",
        "gcd(-2, 0) $in N+",
        "have a Z*\ngcd(0, a) $in N+",
        "have a Z\nlcm(a, 0) $in N",
        "lcm(0, 0) $in N",
        "exp(0) $in R+",
        "exp(-1) $in R+",
        "0! $in N+",
    ] {
        assert_accepts(code);
    }
}

#[test]
fn native_scalar_codomain_rejects_invalid_domains_and_narrowing() {
    for code in [
        "sign(i) $in C",
        "have a C\nsign(a) $in Z",
        "gcd(0, 0) $in N+",
        "gcd(0, 0) $in C",
        "gcd(1.5, 1) $in N+",
        "have a Z\nhave b Z\ngcd(a, b) $in N+",
        "lcm(1.5, 1) $in N",
        "exp(i) $in C",
        "have n Z\nn! $in N+",
        "factorial(-1) $in N+",
        "factorial(1.5) $in N+",
        "sign(0) $in N+",
        "sign(-1) $in N",
        "have a R\nsign(a) $in N+",
        "lcm(0, 0) $in N+",
        "have a Z\nhave b Z\nlcm(a, b) $in N+",
        "have x R\nexp(x) $in Z",
        "have n N\nn! $in Z-",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let result = exec(&mut rt, code);
        assert!(result.is_failed(), "unexpected acceptance: {code}");
    }
}

#[test]
fn native_scalar_codomain_normal_and_detailed_keep_native_carrier() {
    for (setup, goal, carrier) in [
        ("have a R", "sign(a) $in C", "Z"),
        ("have a Z*\nhave b Z", "gcd(a, b) $in N+", "N+"),
        ("have a Z\nhave b Z", "lcm(a, b) $in R", "N"),
        ("have x R", "exp(x) $in R+", "R+"),
        ("have n N", "n! $in N", "N+"),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let result = exec(&mut rt, &format!("{setup}\n{goal}"));
        assert!(!result.is_failed(), "{goal}");
        let normal = project_stmt_normal(&result, &rt);
        assert!(has_field(&normal, "rule_name", "Structural membership"));
        assert!(has_field(&normal, "type", "by_structural_membership"));
        let detailed = project_stmt_detailed(&result, &rt);
        assert!(has_field(&detailed, "kind", "intrinsic_codomain"));
        assert!(has_field(&detailed, "set", carrier));
    }
    let mut rt = runtime(OutputLanguage::Chinese);
    let result = exec(&mut rt, "have a R\nsign(a) $in R");
    let normal = project_stmt_normal(&result, &rt).stringify_pretty();
    assert!(normal.contains("结构归属"));
    assert!(normal.contains("已检查运算的返回类型"));
}


#[test]
fn finite_set_extrema_membership_preserves_wd_and_target() {
    for (operator, rule) in [("finite_set_max", "FiniteSetMaxMember"), ("finite_set_min", "FiniteSetMinMember")] {
        let source = format!("claim:\n    ? forall S finite_set:\n        S $subset R\n        $is_nonempty_set(S)\n        =>:\n            {operator}(S) $in S\n");
        let mut rt = runtime(OutputLanguage::English);
        let result = exec(&mut rt, &source);
        assert!(!result.is_failed(), "{}", project_stmt_detailed(&result, &rt).stringify());
        assert!(has_field(&project_stmt_detailed(&result, &rt), "rule", rule));
        for bad in [
            format!("{operator}({{}}) $in {{}}\n"),
            format!("{operator}(R) $in R\n"),
            format!("{operator}({{i}}) $in {{i}}\n"),
            format!("have S finite_set = {{1,2}}\n{operator}(S) $in {{9}}\n"),
            format!("have S finite_set\n{operator}(S) $in S\n"),
        ] {
            let mut negative = runtime(OutputLanguage::English);
            let result = exec(&mut negative, &bad);
            assert!(result.is_failed(), "wrongly accepted: {bad}");
        }
    }
}


#[test]
fn positive_common_divisor_gcd_bound_requires_both_residues() {
    let code = "claim:\n    ? forall a, b Z, d N+:\n        a != 0 or b != 0\n        a % d = 0\n        b % d = 0\n        =>:\n            d <= gcd(a,b)\n";
    let mut rt = runtime(OutputLanguage::English);
    let result = exec(&mut rt, code);
    assert!(!result.is_failed(), "{}",project_stmt_detailed(&result,&rt).stringify());
    let detail = project_stmt_detailed(&result,&rt);
    assert!(has_field(&detail, "rule", "PositiveCommonDivisorLeGcd"));
    let text = detail.stringify();
    for field in ["divisor_in_n_pos_proof", "left_remainder_zero_proof", "right_remainder_zero_proof"] {
        assert!(text.contains(field));
    }
    for bad in [
        code.replace("        a % d = 0\n", ""),
        code.replace("        b % d = 0\n", ""),
        code.replace("        a != 0 or b != 0\n", ""),
        code.replace("d <= gcd(a,b)", "d < gcd(a,b)"),
        "0 <= gcd(0,0)\n".into(),
        "have a Z = 12\nhave b Z = 18\nhave d N+ = 12\na != 0 or b != 0\na % d = 0\nd <= gcd(a,b)\n".into(),
    ] {
        let mut negative = runtime(OutputLanguage::English);
        assert!(exec(&mut negative,&bad).is_failed(), "accepted: {bad}");
    }
    for (a,b) in [("0","-18"),("-12","0"),("-12","-18"),("-12","18")] {
        assert_accepts(&format!("have a Z={a}\nhave b Z={b}\nhave d N+=6\na != 0 or b != 0\na%d=0\nb%d=0\nd<=gcd(a,b)\n"));
    }
}


#[test]
fn strict_lower_bound_positive_infer_composes_with_log_wd() {
    for code in [
        "claim:\n    ? forall x R:\n        1 < x\n        =>:\n            0 < log(2, x)\n    1 < 2\n",
        "forall b, x R:\n    0 <= b\n    b < x\n    =>:\n        0 < x\n",
        "forall x R:\n    x > 2\n    =>:\n        0 < x\n",
        "forall x R:\n    0 < x\n    =>:\n        0 < x\n",
    ] { assert_accepts(code); }
}

#[test]
fn strict_lower_bound_positive_infer_preserves_domains_and_scope() {
    for code in [
        "forall x R:\n    -1 < x\n    =>:\n        0 < x\n",
        "forall b, x R:\n    b < x\n    =>:\n        0 < x\n",
        "forall x R:\n    0 <= x\n    =>:\n        0 < x\n",
        "forall x R:\n    1 < x\n    =>:\n        0 < log(1/2, x)\n",
    ] {
        let mut rt = runtime(OutputLanguage::English);
        let result = exec(&mut rt, code);
        assert!(result.is_failed(), "{code}");
    }
    let mut rt = runtime(OutputLanguage::English);
    assert!(!exec(&mut rt, "forall x R:\n    2 < x\n    =>:\n        0 < x\n").is_failed());
    assert!(!exec(&mut rt, "have x R").is_failed());
    assert!(exec(&mut rt, "0 < x").is_failed());
}

#[test]
fn strict_lower_bound_positive_infer_keeps_source_and_bound_proof() {
    use crate::execute::ExecFactStmtResult;
    use crate::store_fact_and_infer::{InferFactResult, InferAtomicFactResult, InferAtomicExceptEqualityResult};
    let mut rt = runtime(OutputLanguage::English);
    assert!(!exec(&mut rt, "have x R = 3").is_failed());
    let result = exec(&mut rt, "2 < x");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) = &result else { panic!("fact success") };
    let InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules)) = &success.store_and_infer_result.infer else { panic!("infer") };
    let proof = rules.iter().find_map(|r| match r {
        InferAtomicExceptEqualityResult::StrictLowerBoundPositive(p) => Some(p),
        _ => None,
    }).expect("positive bound certificate");
    assert_eq!(proof.source_fact_id, success.store_and_infer_result.primary_fact_id());
    assert!(!proof.bound_nonnegative_proof.is_failed());
    let derived = proof.derived.primary_fact_id();
    let fact = rt.fact_by_id_in_stack(derived).expect("derived positive");
    assert!(fact.readable_string().contains("0 < x"));
    assert!(project_stmt_normal(&result, &rt).stringify_pretty().contains("0 < x"));
}

#[test]
fn weak_integer_lower_bound_in_n_keeps_both_certificates() {
    use crate::execute::ExecFactStmtResult;
    use crate::execute::execute_fact_stmt::VerifyFactResult;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult,
    };
    use crate::store_fact_and_infer::{InferFactResult, InferAtomicFactResult, InferAtomicExceptEqualityResult};
    for bound in ["0 <= n", "n >= 0", "1 / 2 <= n", "n >= 2"] {
        let mut rt = runtime(OutputLanguage::English);
        assert!(!exec(&mut rt, "have n Z = 3").is_failed());
        let result = exec(&mut rt, bound);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) = &result else { panic!("bound success") };
        let InferFactResult::AtomicFact(InferAtomicFactResult::ExceptEquality(rules)) = &success.store_and_infer_result.infer else { panic!("infer") };
        let proof = rules.iter().find_map(|r| match r {
            InferAtomicExceptEqualityResult::WeakIntegerLowerBoundInN(p) => Some(p),
            _ => None,
        }).expect("integer and nonnegative-bound certificates");
        assert_eq!(proof.source_fact_id, success.store_and_infer_result.primary_fact_id());
        assert!(!proof.integer_proof.is_failed());
        assert!(!proof.bound_nonnegative_proof.is_failed());
        let VerifyFactResult::AtomicExceptEquality(integer) = &proof.integer_proof else { panic!("integer proof") };
        let VerifyAtomicExceptEqualityFactResult::Success(integer) = integer.as_ref() else { panic!("proved integer") };
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &integer.searched_proof else { panic!("stored integer citation") };
        assert_eq!(rt.fact_by_id_in_stack(cite.cite_fact_id).unwrap().readable_string(), "n $in Z");
        let derived = proof.derived.primary_fact_id();
        assert_eq!(rt.fact_by_id_in_stack(derived).unwrap().readable_string(), "n $in N");
        for output in [project_stmt_normal(&result, &rt), project_stmt_detailed(&result, &rt)] {
            let text = output.stringify_pretty();
            assert!(text.contains("n $in N"), "{text}");
        }
        assert!(project_stmt_detailed(&result, &rt).stringify_pretty().contains(&derived.to_string()));
        let use_result = exec(&mut rt, "n $in N");
        assert!(!use_result.is_failed());
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(use_success)) = &use_result else { panic!("membership success") };
        let VerifyFactResult::AtomicExceptEquality(member) = &use_success.verify_result else { panic!("membership proof") };
        let VerifyAtomicExceptEqualityFactResult::Success(member) = member.as_ref() else { panic!("proved membership") };
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &member.searched_proof else { panic!("derived membership citation") };
        assert_eq!(cite.cite_fact_id, derived);
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
}

#[test]
fn weak_integer_lower_bound_in_n_unblocks_nested_induction_wd() {
    let proof = "have fn identity(n N) N = n\nby induc k from 0:\n    ? identity(k) >= 0\n    ? from k = 0:\n        identity(0) = 0\n    ? induc:\n        k $in N\n        k + 1 $in N\n        identity(k + 1) = k + 1\n        identity(k + 1) >= 0";
    assert_accepts(proof);
    assert_accepts(&proof.replace("by induc", "by strong_induc").replace("? induc:", "? strong_induc:"));
    assert_accepts("have fn identity(n N) N = n\nforall b R, n Z:\n    b >= 0\n    n >= b\n    =>:\n        identity(n) = n");
    assert_accepts("have fn identity(n N) N = n\nforall b R, n Z:\n    0 <= b\n    b <= n\n    =>:\n        identity(n) = n");
}

#[test]
fn weak_integer_lower_bound_in_n_keeps_domain_scope_and_rollback() {
    for (setup, bound) in [
        ("have n R = 1 / 2", "n >= 0"),
        ("have n Z = -1", "-2 <= n"),
        ("have n Z = -1", "n <= 0"),
    ] {
        let mut rt = runtime(OutputLanguage::English);
        assert!(!exec(&mut rt, setup).is_failed());
        assert!(!exec(&mut rt, bound).is_failed());
        assert!(exec(&mut rt, "n $in N").is_failed());
        assert_eq!(rt.execution_environments_stack.len(), 1);
    }
    let mut rt = runtime(OutputLanguage::English);
    assert!(!exec(&mut rt, "have n Z = 0\n0 <= n").is_failed());
    assert!(exec(&mut rt, "n $in N+").is_failed());
    assert!(exec(&mut rt, "n != 0").is_failed());
    let mut rt = runtime(OutputLanguage::English);
    assert!(!exec(&mut rt, "forall n Z:\n    n >= 0\n    =>:\n        n $in N").is_failed());
    assert!(!exec(&mut rt, "have n Z = -1").is_failed());
    assert!(exec(&mut rt, "n $in N").is_failed());
    let mut rt = runtime(OutputLanguage::English);
    assert!(exec(&mut rt, "claim:\n    ? 0 = 1\n    have n Z = 3\n    0 <= n").is_failed());
    assert!(!exec(&mut rt, "have n Z = -1").is_failed());
    assert!(exec(&mut rt, "n $in N").is_failed());
    assert_eq!(rt.execution_environments_stack.len(), 1);
    let mut rt = runtime(OutputLanguage::English);
    assert!(!exec(&mut rt, "have fn identity(n N) N = n").is_failed());
    assert!(exec(&mut rt, "by induc k from -1:\n    ? identity(k) >= 0\n    ? from k = -1:\n        identity(-1) = -1\n    ? induc:\n        identity(k + 1) = k + 1").is_failed());
}
