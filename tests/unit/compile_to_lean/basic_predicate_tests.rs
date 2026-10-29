use crate::prelude::*;

#[test]
fn basic_predicate_generated_examples_compile() {
    for source in [
        include_str!("../../../lean/examples/set_predicate_contexts/statement.lit"),
        include_str!("../../../lean/examples/proper_set_relations/statement.lit"),
        include_str!("../../../lean/examples/negative_set_values/statement.lit"),
        include_str!("../../../lean/examples/number_theory_predicate_contexts/statement.lit"),
        include_str!("../../../lean/examples/number_theory_values/statement.lit"),
        include_str!("../../../lean/examples/integer_divisibility/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "basic_predicate_examples")
            .unwrap();
    }
}

#[test]
fn basic_predicate_invalid_domains_and_false_claims_produce_no_artifact() {
    for source in [
        "$prime(9)",
        "$coprime(8,12)",
        "$dvd(15,0)",
        "$dvd(16,3)",
        "forall a R:\n    $prime(a)\n    =>:\n        $prime(a)",
        "not $is_set(1)",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_predicate")
            .is_err());
    }
}

#[test]
fn basic_predicate_families_preserve_generic_premises() {
    for (header, fact) in [
        ("forall A, B set:", "A $superset B"),
        ("forall A, B set:", "not A $superset B"),
        ("forall A, B set:", "A $proper_subset B"),
        ("forall A, B set:", "not A $proper_subset B"),
        ("forall A, B set:", "A $proper_superset B"),
        ("forall A, B set:", "not A $proper_superset B"),
        ("forall A set:", "not $is_set(A)"),
        ("forall A set:", "not $is_nonempty_set(A)"),
        ("forall A set:", "not $is_finite_set(A)"),
        ("forall a N:", "$prime(a)"),
        ("forall a N:", "not $prime(a)"),
        ("forall a, b N:", "$coprime(a,b)"),
        ("forall a, b N:", "not $coprime(a,b)"),
        ("forall a Z, b Z*:", "$dvd(a,b)"),
        ("forall a Z, b Z*:", "not $dvd(a,b)"),
    ] {
        let source = format!("{header}\n    {fact}\n    =>:\n        {fact}\n");
        let (run, compiler) = super::execute(&source);
        compiler
            .compile_run(&run, "generic_predicate")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn basic_predicate_selected_routes_and_inference_citations() {
    for source in [
        "by def {1,2} $proper_subset {1,2,3}",
        "by def {1,2,3} $proper_superset {1,2}",
        "forall A, B set:\n    A $proper_subset B\n    =>:\n        A $subset B\n        A != B",
        "forall A, B set:\n    A $proper_superset B\n    =>:\n        B $subset A\n        A != B",
        "R $superset N",
        "not $is_nonempty_set({})\nnot $is_finite_set(N)",
        "$prime(5)\nnot $prime(9)\n$coprime(8,15)\nnot $coprime(8,12)",
        "15 % 3 = 0\n$dvd(15,3)",
        "forall a Z, b Z*:\n    a % b = 0\n    =>:\n        $dvd(a,b)",
    ] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "basic_predicate")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn basic_predicate_rejects_missing_domain_and_altered_computation() {
    for source in ["$prime(5)", "$coprime(8,15)"] {
        let (mut run, compiler) = super::execute(source);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let p = super::atomic_proof_mut(&mut p.verify_result);
        match &mut p
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .predicate_domain
        {
            PredicateDomainProof::ByRequirements(r) => r.clear(),
            _ => panic!("expected original numeric domain"),
        }
        assert!(compiler.compile_run(&run, "missing_domain").is_err());
    }
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::search_atomic_except_equality_fact_proof_by_builtin_rule_result::PrimeFactSearchProofByBuiltinRule;
    let (mut run, compiler) = super::execute("$prime(5)");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[0] else {
        panic!()
    };
    let p = super::atomic_proof_mut(&mut p.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::PrimeFact(
            PrimeFactSearchProofByBuiltinRule::PrimeByComputation(p),
        ),
    ) = &mut p.searched_proof
    else {
        panic!()
    };
    p.resolved_value = "7".into();
    assert!(compiler.compile_run(&run, "wrong_prime_value").is_err());
}

#[test]
fn divisibility_rejects_a_remainder_certificate_for_another_divisor() {
    let (mut run, compiler) = super::execute("15 % 3 = 0\n$dvd(15,3)");
    let statement = super::fact_statement_mut(&mut run.statement_results[1]);
    let proof = super::atomic_proof_mut(&mut statement.verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownZeroRemainder(remainder) =
        &mut proof.searched_proof
    else {
        panic!("expected the captured zero-remainder route");
    };
    remainder.divisor = Obj::Literal(Literal::Number(Number::new("2".into())));
    assert!(compiler.compile_run(&run, "wrong_divisor").is_err());
}
