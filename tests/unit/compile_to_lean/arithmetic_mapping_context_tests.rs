use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_or_fact::{OrFactSearchedProof, VerifyOrFactSuccess};
use crate::prelude::*;

const ALTERNATIVES: &[(&str, &str)] = &[
    (
        "prime_subset_disjunction_instantiation",
        r#"# Instantiate a supplied arithmetic alternative on a generic numeric subset.
forall sc71_D set, n sc71_D:
    sc71_D $subset N
    forall x sc71_D:
        $prime(x) or x = 1
    =>:
        $prime(n) or n = 1
"#,
    ),
    (
        "negative_prime_subset_disjunction_instantiation",
        r#"# Instantiate a supplied arithmetic alternative on a generic numeric subset.
forall sc71_D set, n sc71_D:
    sc71_D $subset N
    forall x sc71_D:
        not $prime(x) or x = 0
    =>:
        not $prime(n) or n = 0
"#,
    ),
    (
        "coprime_subset_disjunction_instantiation",
        r#"# Instantiate a supplied arithmetic alternative on a generic numeric subset.
forall sc71_D set, n sc71_D, m N:
    sc71_D $subset N
    forall x sc71_D:
        $coprime(x,m) or x = 1
    =>:
        $coprime(n,m) or n = 1
"#,
    ),
    (
        "negative_coprime_subset_disjunction_instantiation",
        r#"# Instantiate a supplied arithmetic alternative on a generic numeric subset.
forall sc71_D set, n sc71_D, m N:
    sc71_D $subset N
    forall x sc71_D:
        not $coprime(x,m) or x = 0
    =>:
        not $coprime(n,m) or n = 0
"#,
    ),
    (
        "divisibility_subset_disjunction_instantiation",
        r#"# Instantiate a supplied arithmetic alternative on a generic numeric subset.
forall sc71_D set, n sc71_D, d Z*:
    sc71_D $subset Z
    forall x sc71_D:
        $dvd(x,d) or x = 0
    =>:
        $dvd(n,d) or n = 0
"#,
    ),
    (
        "negative_divisibility_subset_disjunction_instantiation",
        r#"# Instantiate a supplied arithmetic alternative on a generic numeric subset.
forall sc71_D set, n sc71_D, d Z*:
    sc71_D $subset Z
    forall x sc71_D:
        not $dvd(x,d) or x = 1
    =>:
        not $dvd(n,d) or n = 1
"#,
    ),
    (
        "injective_function_disjunction_instantiation",
        r#"# Instantiate a supplied mapping alternative for a function between generic sets.
forall sc71_A,sc71_B set, f fn(t sc71_A) sc71_B, a sc71_A, b sc71_B:
    forall g fn(t sc71_A) sc71_B:
        $injective(sc71_A,sc71_B,g) or g(a) = b
    =>:
        $injective(sc71_A,sc71_B,f) or f(a) = b
"#,
    ),
    (
        "negative_injective_function_disjunction_instantiation",
        r#"# Instantiate a supplied mapping alternative for a function between generic sets.
forall sc71_A,sc71_B set, f fn(t sc71_A) sc71_B, a sc71_A, b sc71_B:
    forall g fn(t sc71_A) sc71_B:
        not $injective(sc71_A,sc71_B,g) or g(a) = b
    =>:
        not $injective(sc71_A,sc71_B,f) or f(a) = b
"#,
    ),
    (
        "surjective_function_disjunction_instantiation",
        r#"# Instantiate a supplied mapping alternative for a function between generic sets.
forall sc71_A,sc71_B set, f fn(t sc71_A) sc71_B, a sc71_A, b sc71_B:
    forall g fn(t sc71_A) sc71_B:
        $surjective(sc71_A,sc71_B,g) or g(a) = b
    =>:
        $surjective(sc71_A,sc71_B,f) or f(a) = b
"#,
    ),
    (
        "negative_surjective_function_disjunction_instantiation",
        r#"# Instantiate a supplied mapping alternative for a function between generic sets.
forall sc71_A,sc71_B set, f fn(t sc71_A) sc71_B, a sc71_A, b sc71_B:
    forall g fn(t sc71_A) sc71_B:
        not $surjective(sc71_A,sc71_B,g) or g(a) = b
    =>:
        not $surjective(sc71_A,sc71_B,f) or f(a) = b
"#,
    ),
    (
        "bijective_function_disjunction_instantiation",
        r#"# Instantiate a supplied mapping alternative for a function between generic sets.
forall sc71_A,sc71_B set, f fn(t sc71_A) sc71_B, a sc71_A, b sc71_B:
    forall g fn(t sc71_A) sc71_B:
        $bijective(sc71_A,sc71_B,g) or g(a) = b
    =>:
        $bijective(sc71_A,sc71_B,f) or f(a) = b
"#,
    ),
    (
        "negative_bijective_function_disjunction_instantiation",
        r#"# Instantiate a supplied mapping alternative for a function between generic sets.
forall sc71_A,sc71_B set, f fn(t sc71_A) sc71_B, a sc71_A, b sc71_B:
    forall g fn(t sc71_A) sc71_B:
        not $bijective(sc71_A,sc71_B,g) or g(a) = b
    =>:
        not $bijective(sc71_A,sc71_B,f) or f(a) = b
"#,
    ),
];
const EQUAL_FUNCTIONS: &[(&str, &str)] = &[
    (
        "equal_functions_injective",
        r#"# Equal functions preserve the supplied mapping property on their original carriers.
forall sc71_A,sc71_B set, f,g fn(t sc71_A) sc71_B:
    f = g
    $injective(sc71_A,sc71_B,f)
    =>:
        $injective(sc71_A,sc71_B,g)
"#,
    ),
    (
        "equal_functions_negative_injective",
        r#"# Equal functions preserve the supplied mapping property on their original carriers.
forall sc71_A,sc71_B set, f,g fn(t sc71_A) sc71_B:
    f = g
    not $injective(sc71_A,sc71_B,f)
    =>:
        not $injective(sc71_A,sc71_B,g)
"#,
    ),
    (
        "equal_functions_surjective",
        r#"# Equal functions preserve the supplied mapping property on their original carriers.
forall sc71_A,sc71_B set, f,g fn(t sc71_A) sc71_B:
    f = g
    $surjective(sc71_A,sc71_B,f)
    =>:
        $surjective(sc71_A,sc71_B,g)
"#,
    ),
    (
        "equal_functions_negative_surjective",
        r#"# Equal functions preserve the supplied mapping property on their original carriers.
forall sc71_A,sc71_B set, f,g fn(t sc71_A) sc71_B:
    f = g
    not $surjective(sc71_A,sc71_B,f)
    =>:
        not $surjective(sc71_A,sc71_B,g)
"#,
    ),
    (
        "equal_functions_bijective",
        r#"# Equal functions preserve the supplied mapping property on their original carriers.
forall sc71_A,sc71_B set, f,g fn(t sc71_A) sc71_B:
    f = g
    $bijective(sc71_A,sc71_B,f)
    =>:
        $bijective(sc71_A,sc71_B,g)
"#,
    ),
    (
        "equal_functions_negative_bijective",
        r#"# Equal functions preserve the supplied mapping property on their original carriers.
forall sc71_A,sc71_B set, f,g fn(t sc71_A) sc71_B:
    f = g
    not $bijective(sc71_A,sc71_B,f)
    =>:
        not $bijective(sc71_A,sc71_B,g)
"#,
    ),
];

fn alternative(run: &RunLitexCodeResult) -> &VerifyOrFactSuccess {
    let outer = super::forall_proof(&run.statement_results[0]);
    let VerifyFactResult::OrFact(p) = &outer.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(p) = p.as_ref() else {
        panic!()
    };
    p
}
fn alternative_mut(run: &mut RunLitexCodeResult) -> &mut VerifyOrFactSuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    let VerifyFactResult::OrFact(p) = &mut outer.proved_then_facts[0].verify_result else {
        panic!()
    };
    let VerifyOrFactResult::Success(p) = p.as_mut() else {
        panic!()
    };
    p
}
fn mapping_mut(run: &mut RunLitexCodeResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::atomic_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn reject(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "ArithmeticMappingCorrupt")
        .expect_err("a changed predicate, original equality or source certificate must reject");
}

#[test]
fn arithmetic_and_mapping_alternatives_retain_the_actual_forall_citation_and_generic_domains() {
    for (name, source) in ALTERNATIVES {
        let (run, compiler) = super::execute(source);
        let proof = alternative(&run);
        let OrFactSearchedProof::ByKnownForallFact(app) = &proof.searched_proof else {
            panic!("{name}: original known-forall route");
        };
        let detailed = app.detailed_ref();
        assert_eq!(detailed.forall_parameters_match_what_args.len(), 1);
        assert_eq!(
            detailed.arg_match_proofs.len(),
            crate::ast::fact::or_fact_args_ref(&proof.fact).len()
        );
        let outer = super::forall_proof(&run.statement_results[0]);
        assert!(outer
            .fact
            .dom_facts
            .iter()
            .any(|f| f.fact_id() == detailed.cite.fact_id));
        let AndChainAtomicFact::AtomicFact(first) = &proof.fact.facts[0] else {
            panic!()
        };
        assert_eq!(
            crate::ast::fact::atomic_fact_has_positive_polarity(first),
            !name.starts_with("negative_")
        );
        compiler
            .compile_run(&run, "ArithmeticMappingAlternativeOriginal")
            .unwrap();
    }
}
#[test]
fn arithmetic_and_mapping_alternatives_require_original_citations_and_parameter_memberships() {
    for (_, source) in ALTERNATIVES {
        for mutation in 0..2 {
            let (mut run, compiler) = super::execute(source);
            let OrFactSearchedProof::ByKnownForallFact(app) =
                &mut alternative_mut(&mut run).searched_proof
            else {
                panic!()
            };
            let detailed = app.as_detailed_mut().unwrap();
            if mutation == 0 {
                detailed.cite.fact_id = FactId::new(u64::MAX);
            } else {
                detailed
                    .instantiation_requirements
                    .as_detailed_mut()
                    .unwrap()
                    .param_type_requirements
                    .pop();
            }
            reject(&run, &compiler);
        }
    }
}
#[test]
fn arithmetic_and_mapping_alternatives_require_ordered_matches_and_original_polarity() {
    for (_, source) in ALTERNATIVES {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let proof = alternative_mut(&mut run);
            if mutation == 2 {
                let AndChainAtomicFact::AtomicFact(first) = &mut proof.fact.facts[0] else {
                    panic!()
                };
                *first = crate::ast::fact::negate_atomic_fact(first, first.fact_id()).unwrap();
            } else {
                let OrFactSearchedProof::ByKnownForallFact(app) = &mut proof.searched_proof else {
                    panic!()
                };
                let matches = &mut app.as_detailed_mut().unwrap().arg_match_proofs;
                if mutation == 0 {
                    matches.pop();
                } else {
                    let last = matches.len() - 1;
                    matches.swap(0, last);
                }
            }
            reject(&run, &compiler);
        }
    }
}
#[test]
fn arithmetic_and_mapping_alternatives_retain_original_branch_wd() {
    for (_, source) in ALTERNATIVES {
        let (mut run, compiler) = super::execute(source);
        alternative_mut(&mut run)
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .branches
            .pop();
        reject(&run, &compiler);
    }
}
#[test]
fn equal_functions_replay_original_atomic_mapping_citations_and_all_three_equalities() {
    for (name, source) in EQUAL_FUNCTIONS {
        let (mut run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let prior = outer
            .fact
            .dom_facts
            .iter()
            .map(Fact::fact_id)
            .collect::<Vec<_>>();
        let proof = mapping_mut(&mut run);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(app) = &proof.searched_proof
        else {
            panic!("{name}: original known atomic route");
        };
        assert!(prior.contains(&app.cite_fact_id));
        assert_eq!(
            app.why_parameters_of_known_fact_are_equal_to_givens.len(),
            3
        );
        assert_eq!(
            crate::ast::fact::atomic_fact_has_positive_polarity(&proof.fact),
            !name.contains("negative")
        );
        compiler
            .compile_run(&run, "EqualFunctionsMappingOriginal")
            .unwrap();
    }
}
#[test]
fn equal_functions_require_original_mapping_citations_and_ordered_argument_evidence() {
    for (_, source) in EQUAL_FUNCTIONS {
        for mutation in 0..3 {
            let (mut run, compiler) = super::execute(source);
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(app) =
                &mut mapping_mut(&mut run).searched_proof
            else {
                panic!()
            };
            match mutation {
                0 => app.cite_fact_id = FactId::new(u64::MAX),
                1 => {
                    app.why_parameters_of_known_fact_are_equal_to_givens.pop();
                }
                2 => app
                    .why_parameters_of_known_fact_are_equal_to_givens
                    .swap(0, 2),
                _ => unreachable!(),
            }
            reject(&run, &compiler);
        }
    }
}
#[test]
fn equal_functions_cannot_change_mapping_polarity_or_discard_domain_wd() {
    for (_, source) in EQUAL_FUNCTIONS {
        for mutation in 0..2 {
            let (mut run, compiler) = super::execute(source);
            let proof = mapping_mut(&mut run);
            if mutation == 0 {
                proof.fact =
                    crate::ast::fact::negate_atomic_fact(&proof.fact, proof.fact.fact_id())
                        .unwrap();
            } else {
                let PredicateDomainProof::ByKnownFact(citation) = &mut proof
                    .well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .predicate_domain
                else {
                    panic!()
                };
                citation.cite_fact_id = FactId::new(u64::MAX);
            }
            reject(&run, &compiler);
        }
    }
}
#[test]
fn arithmetic_and_mapping_context_hypotheses_do_not_escape_their_original_forall() {
    for (_, source) in ALTERNATIVES.iter().chain(EQUAL_FUNCTIONS.iter()) {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let position = SourcePosition::new(None, SourceOwner::Run(&run), 1);
        for fact in &outer.fact.dom_facts {
            assert!(compiler
                .cited_fact_reference(fact.fact_id(), &position)
                .is_err());
        }
        compiler
            .compile_run(&run, "ArithmeticMappingClosed")
            .unwrap();
    }
}
