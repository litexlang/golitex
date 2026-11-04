use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferHasRiemannIntegralFactResult, InferResult,
};

const SOURCE: &str =
    include_str!("../../../lean/examples/riemann_integral_selection/statement.lit");

#[test]
fn riemann_integral_candidate_replays() {
    for source in [
        SOURCE,
        include_str!("../../../lean/examples/riemann_integral_existence/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_integrability/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_negative_citation/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_reversed_interval/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_zero_width/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_closed_domain/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_guarded_domain/statement.lit"),
        include_str!("../../../lean/examples/riemann_integrability_from_existence/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_nested_objects/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_rational_endpoints/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_closed_endpoints/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_fractional_bounds/statement.lit"),
        include_str!("../../../lean/examples/darboux_enclosure_citation/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_from_definition/statement.lit"),
        include_str!("../../../lean/examples/subtract_closed_bound/statement.lit"),
        include_str!("../../../lean/examples/renamed_range_binders/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        let compiled = c
            .compile_run(&run, "riemann_integral_selection")
            .expect(source);
        if source.contains("thm integral_from_darboux_definition:") {
            // The full statement remains intact; a finite local option lets
            // ordinary Lean check it without changing its importer's options.
            assert!(compiled.contains("set_option maxHeartbeats 1000000 in\ntheorem "));
            assert!(!compiled.contains("set_option maxHeartbeats 0"));
        }
    }
}

#[test]
fn closed_subtraction_bound_keeps_its_citation_and_exact_certificate() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::{
        closed_subtraction_bound::BoundDirection, less_equal::LessEqualFactSearchProofByBuiltinRule as Rule,
    };
    let source = include_str!("../../../lean/examples/subtract_closed_bound/statement.lit");
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
    let source =
        include_str!("../../../lean/examples/riemann_integral_from_definition/statement.lit");
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
    let source = include_str!("../../../lean/examples/darboux_enclosure_citation/statement.lit");
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
        include_str!("../../../lean/examples/riemann_integral_closed_endpoints/statement.lit"),
        include_str!("../../../lean/examples/riemann_integral_fractional_bounds/statement.lit"),
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
