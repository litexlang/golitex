use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferHasRiemannIntegralFactResult, InferResult,
};

const SOURCE: &str = r#"# A proved oriented Riemann integral candidate determines the selected value.
forall f fn(x R) R, a, b, I R:
    $has_riemann_integral(f, a, b, I)
    =>:
        integral(f, a, b) = I
"#;

#[test]
fn closed_subtraction_bound_keeps_its_citation_and_exact_certificate() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
        closed_subtraction_bound::BoundDirection, less_equal::LessEqualFactSearchProofByBuiltinRule as Rule,
    };
    let source = r#"# Transport stored bounds through subtraction of an exact constant, preserving direction and strictness.

forall k, n R:
    1 <= k
    k <= n
    =>:
        0 <= k - 1
        k - 1 <= n

forall x R:
    x < 3
    =>:
        x - 1 < 2

forall x R:
    x >= 3
    =>:
        x - 1 >= 2
        x - 1 > 1

forall x, a R:
    x >= a
    =>:
        x - (0 - 1) > a
"#;
    for conclusion in 0..2 {
        for mutation in 0..6 {
            let (mut run, compiler) = super::execute(source);
            let all = super::forall_proof_mut(&mut run.statement_results[0]);
            let p = super::atomic_proof_mut(&mut all.proved_then_facts[conclusion].verify_result);
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                    Rule::ClosedSubtractionBound(p),
                ),
            ) = &mut p.searched_proof
            else {
                panic!("selected stored-bound subtraction")
            };
            let zero = Obj::Literal(Literal::Number(Number::new("0".into())));
            match mutation {
                0 => p.bound.cite_fact_id = FactId::new(u64::MAX),
                1 => p.bound.normalized_subtrahend = zero,
                2 => p.bound.translated_bound = Obj::StandardSet(StandardSet::R),
                3 => p.bound.target_bound = Obj::StandardSet(StandardSet::R),
                4 => {
                    p.bound.direction = match p.bound.direction {
                        BoundDirection::Lower => BoundDirection::Upper,
                        BoundDirection::Upper => BoundDirection::Lower,
                    }
                }
                _ => {
                    let AtomicFact::LessEqualFact(source) = &mut p.bound.source_fact else {
                        panic!("original weak bound")
                    };
                    source.fact_id = FactId::new(u64::MAX);
                }
            }
            compiler
                .compile_run(&run, "changed_closed_subtraction_bound")
                .expect_err("only the recorded exact bound translation is replayable");
        }
    }
}

#[test]
fn riemann_definition_fold_requires_all_original_clauses() {
    use crate::execute::execute_by_stmt::ExecByDefStmtResult;
    use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
        AtomicExceptEqualityFactSearchProofByDefinition as Definition,
        BuiltinPropDefinitionProof as Builtin,
    };
    use crate::execute::ExecDefinitionStmtResult;
    let source = r#"# Recover the oriented Riemann integral from boundedness and arbitrarily tight Darboux enclosures.

0 <= 1

forall k Z:
    1 <= k
    =>:
        0 <= k

thm integral_from_darboux_definition:
    ? forall f fn(x R) R, a, b, I R:
        '[min(a,b),max(a,b)] $subset R
        $is_real_bounded(fn_range(fn(x '[min(a,b),max(a,b)]) R {f(x)}))
        a != b or I = 0
        forall epsilon R+:
            min(a,b) < max(a,b)
            =>:
                exist n N+, p fn(k Z: 0 <= k, k <= n) R, lower fn(k Z: 1 <= k, k <= n) R, upper fn(k Z: 1 <= k, k <= n) R, lower_sum R, upper_sum R st {$is_darboux_enclosure(f,min(a,b),max(a,b),n,p,lower,upper), lower_sum = sum(1,n,fn(k Z: 1 <= k, k <= n) R {lower(k)*(p(k)-p(k-1))}), upper_sum = sum(1,n,fn(k Z: 1 <= k, k <= n) R {upper(k)*(p(k)-p(k-1))}), lower_sum <= sign(b-a)*I, sign(b-a)*I <= upper_sum, upper_sum-lower_sum < epsilon}
        =>:
            $has_riemann_integral(f,a,b,I)
    by def $has_riemann_integral(f,a,b,I)
"#;
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(source);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) = &mut run.statement_results[2]
        else {
            panic!("definition theorem")
        };
        let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
            panic!("forall")
        };
        let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(p))) =
            &mut body.proof_steps[0]
        else {
            panic!("explicit definition fold")
        };
        let p = super::atomic_proof_mut(&mut p.proof);
        let AtomicExceptEqualityFactSearchedProof::ByDefinition(Definition::BuiltinProp(
            Builtin::HasRiemannIntegral(p),
        )) = &mut p.searched_proof
        else {
            panic!("original integral definition certificate")
        };
        assert_eq!(p.requirement_facts.len(), 6);
        match mutation {
            0 => {
                p.requirement_facts.pop();
                p.proof_of_requirement_facts.pop();
            }
            1 => p.proof_of_requirement_facts.swap(0, 1),
            2 => p.function_domain.domain = Obj::StandardSet(StandardSet::C),
            3 => p.requirement_facts.swap(4, 5),
            _ => {
                let member = super::atomic_proof_mut(&mut p.function_domain.output_real);
                let AtomicFact::SubsetFact(bound) = &mut member.fact else {
                    panic!("real output carrier")
                };
                bound.right = Obj::StandardSet(StandardSet::C);
            }
        }
        compiler
            .compile_run(&run, "changed_riemann_definition_fold")
            .expect_err("boundedness, zero interval and exact approximation must all be retained");
    }
}

#[test]
fn darboux_enclosure_requires_original_partition_signatures() {
    let source = r#"# Preserve the checked partition signatures when citing a Darboux enclosure or its negation.

forall f fn(x R) R, a, b R, n N+, p fn(k Z: 0 <= k, k <= n) R, lower, upper fn(k Z: 1 <= k, k <= n) R:
    $is_darboux_enclosure(f, a, b, n, p, lower, upper)
    =>:
        $is_darboux_enclosure(f, a, b, n, p, lower, upper)

forall f fn(x R) R, a, b R, n N+, p fn(k Z: 0 <= k, k <= n) R, lower, upper fn(k Z: 1 <= k, k <= n) R:
    not $is_darboux_enclosure(f, a, b, n, p, lower, upper)
    =>:
        not $is_darboux_enclosure(f, a, b, n, p, lower, upper)
"#;
    for statement in 0..2 {
        for mutation in 0..6 {
            let (mut run, c) = super::execute(source);
            let all = super::forall_proof_mut(&mut run.statement_results[statement]);
            let FactWellDefinedProof::AtomicExceptEquality(wd) =
                &mut all.assumed_dom_facts[0].well_defined
            else {
                panic!("enclosure formation")
            };
            let PredicateDomainProof::FunctionAnalysis(domain) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!("enclosure domain")
            };
            assert_eq!(domain.requirements.len(), 7);
            match mutation {
                0 => {
                    domain.requirements.remove(2);
                }
                1 => domain.requirements.swap(4, 5),
                2 => {
                    let Fact::AtomicFact(AtomicFact::InFact(n)) =
                        &mut domain.requirements[3].requirement
                    else {
                        panic!("partition size")
                    };
                    n.set = Obj::StandardSet(StandardSet::N);
                }
                3 | 4 => {
                    let Fact::AtomicFact(AtomicFact::InFact(member)) =
                        &mut domain.requirements[4].requirement
                    else {
                        panic!("partition function")
                    };
                    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &mut member.set
                    else {
                        panic!("partition signature")
                    };
                    if mutation == 3 {
                        signature.dom_facts.swap(0, 1);
                    } else {
                        signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
                    }
                }
                _ => domain.function_domain.domain = Obj::StandardSet(StandardSet::C),
            }
            c.compile_run(&run, "changed_darboux_enclosure")
                .expect_err("enclosure WD must replay its exact interval and function signatures");
        }
    }
}

#[test]
fn riemann_closed_endpoints_keep_original_constructor_and_interval_evidence() {
    for source in [
        r#"# Integral selection preserves exactly evaluated real endpoints, orientation and zero-width intervals.
forall f fn(x R) R, I R:
    $has_riemann_integral(f, abs(-2), 3, I)
    =>:
        integral(f, abs(-2), 3) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, floor(-1.5), 2 ^ 3, I)
    =>:
        integral(f, floor(-1.5), 2 ^ 3) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, sqrt(4), max(3, ceil(2.5)), I)
    =>:
        integral(f, sqrt(4), max(3, ceil(2.5))) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, factorial(3), gcd(9, 6), I)
    =>:
        integral(f, factorial(3), gcd(9, 6)) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, abs(-2), abs(-2), I)
    =>:
        integral(f, abs(-2), abs(-2)) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, exp(0), ln(1), I)
    =>:
        integral(f, exp(0), ln(1)) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, sinh(0), cosh(0), I)
    =>:
        integral(f, sinh(0), cosh(0)) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, tanh(0), sech(0), I)
    =>:
        integral(f, tanh(0), sech(0)) = I
"#,
        r#"# Integral selection preserves rational interval endpoints, including thirds and reversed intervals.
forall f fn(x R) R, I R:
    $has_riemann_integral(f, 1 / 3, 1 / 2, I)
    =>:
        integral(f, 1 / 3, 1 / 2) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, 1 / 4, 1 / 3, I)
    =>:
        integral(f, 1 / 4, 1 / 3) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, 1 / 2, 1 / 3, I)
    =>:
        integral(f, 1 / 2, 1 / 3) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, 1 / 3, 1 / 4, I)
    =>:
        integral(f, 1 / 3, 1 / 4) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, 1 / 3, 2 / 3, I)
    =>:
        integral(f, 1 / 3, 2 / 3) = I
forall f fn(x R) R, I R:
    $has_riemann_integral(f, 1 / 3, 1 / 3, I)
    =>:
        integral(f, 1 / 3, 1 / 3) = I
"#,
    ] {
        for mutation in 0..3 {
            let (mut run, c) = super::execute(source);
            let all = super::forall_proof_mut(&mut run.statement_results[0]);
            let FactWellDefinedProof::AtomicExceptEquality(p) =
                &mut all.assumed_dom_facts[0].well_defined
            else {
                panic!("atomic formation")
            };
            let p = p.as_detailed_mut().unwrap();
            match mutation {
                0 => {
                    p.well_defined_of_each_parameter.remove(1);
                }
                1 => p.well_defined_of_each_parameter.swap(1, 2),
                _ => {
                    let PredicateDomainProof::FunctionAnalysis(domain) = &mut p.predicate_domain
                    else {
                        panic!("integral domain")
                    };
                    domain.requirements.remove(2);
                }
            }
            c.compile_run(&run, "changed_closed_integral_endpoints")
                .expect_err("numeric folding cannot replace source WD or interval evidence");
        }
    }
}

#[test]
fn riemann_definition_keeps_domain_and_ordered_publications() {
    for mutation in 0..5 {
        let (mut run, c) = super::execute(SOURCE);
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let Some(InferResult::AtomicFact(InferAtomicFactResult::HasRiemannIntegralFact(rules))) =
            &mut all.assumed_dom_facts[0].store_and_infer.infer
        else {
            panic!("integral inference")
        };
        let [InferHasRiemannIntegralFactResult::Definition(p)] = rules.as_mut_slice() else {
            panic!("definition")
        };
        assert_eq!(p.derived.len(), 8);
        assert!(p.function_domain.is_some());
        match mutation {
            0 => p.function_domain = None,
            1 => p.derived.swap(0, 1),
            2 => p.source_fact_id = FactId::new(u64::MAX),
            3 => p.function_domain.as_mut().unwrap().domain = Obj::StandardSet(StandardSet::C),
            _ => p.derived.swap(4, 5),
        }
        c.compile_run(&run, "changed_integral_inference")
            .expect_err("exact source publications");
    }
}

#[test]
fn riemann_predicate_wd_requires_interval_and_real_candidate() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(SOURCE);
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let FactWellDefinedProof::AtomicExceptEquality(p) =
            &mut all.assumed_dom_facts[0].well_defined
        else {
            panic!("atomic")
        };
        let PredicateDomainProof::FunctionAnalysis(p) =
            &mut p.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("analysis domain")
        };
        assert_eq!(p.requirements.len(), 4);
        match mutation {
            0 => {
                p.requirements.pop();
            }
            1 => p.requirements.swap(0, 1),
            _ => {
                let Fact::AtomicFact(AtomicFact::SubsetFact(s)) =
                    &mut p.requirements[2].requirement
                else {
                    panic!("interval")
                };
                s.right = Obj::StandardSet(StandardSet::C);
            }
        }
        c.compile_run(&run, "changed_integral_wd")
            .expect_err("recorded interval requirements");
    }
}

#[test]
fn riemann_selected_equality_requires_original_citation() {
    let (mut run, c) = super::execute(SOURCE);
    let all = super::forall_proof_mut(&mut run.statement_results[0]);
    let eq = super::equality_proof_mut(&mut all.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::RiemannIntegralSelectedValue(p),
    ) = &mut eq.searched_proof
    else {
        panic!("selected value")
    };
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(k) =
        p.candidate.searched_proof.as_mut()
    else {
        panic!("citation")
    };
    k.cite_fact_id = FactId::new(u64::MAX);
    c.compile_run(&run, "changed_integral_citation")
        .expect_err("exact cited fact ID");
}
