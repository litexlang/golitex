use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_by_stmt::{
    ExecReleaseThmStmtResult, ExecReleaseThmStmtSuccess, TheoremDerivationProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::{ExecDefThmForallProof, ExecReleaseAndExpandStmtResult};
use crate::prelude::*;

const SOURCES: [&str; 5] = [
    include_str!("../../../lean/examples/riemann_explicit_from_definition/statement.lit"),
    include_str!("../../../lean/examples/riemann_explicit_to_definition/statement.lit"),
    include_str!("../../../lean/examples/riemann_zero_interval/statement.lit"),
    include_str!("../../../lean/examples/darboux_explicit_from_definition/statement.lit"),
    include_str!("../../../lean/examples/darboux_explicit_to_definition/statement.lit"),
];
fn theorem(run: &mut RunLitexCodeResult) -> &mut ExecDefThmForallProof {
    let p = run
        .statement_results
        .iter_mut()
        .find_map(|r| match r {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                ExecDefThmStmtResult::Success(p),
            )) => Some(p),
            _ => None,
        })
        .expect("original named theorem");
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("original forall");
    };
    p
}
fn invocation(run: &mut RunLitexCodeResult) -> &mut ExecReleaseThmStmtSuccess {
    let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
        ExecReleaseThmStmtResult::Success(p),
    )) = &mut theorem(run).proof_steps[0]
    else {
        panic!("original NativeSchema call");
    };
    p
}
#[test]
fn integral_definitions_replay_five_native_schemas_with_every_ordered_output() {
    use BuiltinTheoremId::*;
    for (source, id, requirements, outputs, law) in [
        (
            SOURCES[0],
            RiemannIntegralFromDefinition,
            10,
            1,
            "riemannIntegralFromDefiningClauses",
        ),
        (
            SOURCES[1],
            RiemannIntegralToDefinition,
            5,
            6,
            "riemannIntegralDefiningClauses",
        ),
        (
            SOURCES[2],
            RiemannIntegralZero,
            3,
            1,
            "riemannIntegralZeroCandidate",
        ),
        (
            SOURCES[3],
            DarbouxEnclosureFromDefinition,
            12,
            1,
            "darbouxEnclosureFromDefiningClauses",
        ),
        (
            SOURCES[4],
            DarbouxEnclosureToDefinition,
            4,
            9,
            "darbouxEnclosureDefiningClauses",
        ),
    ] {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(p.builtin.as_ref().unwrap().theorem, id);
        assert!(matches!(
            p.theorem_derivation,
            TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), requirements);
        assert_eq!(p.dom_stores.len(), requirements);
        assert_eq!(p.conclusions_wd.len(), outputs);
        assert_eq!(p.builtin.as_ref().unwrap().conclusions.len(), outputs);
        let output = c.compile_run(&run, "integral_definition").unwrap();
        assert!(output.contains(&format!("Litex.{law}")));
        assert_eq!(output, c.compile_run(&run, "integral_definition").unwrap());
    }
}
#[test]
fn integral_definitions_retain_guarded_domains_and_closed_endpoint_reductions() {
    for source in [
        include_str!("../../../lean/examples/riemann_zero_guarded_interval/statement.lit"),
        include_str!("../../../lean/examples/riemann_definition_closed_interval/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "integral_definition_domain").unwrap();
    }
}
#[test]
fn integral_definitions_require_all_original_pipeline_stages() {
    for source in SOURCES {
        for change in 0..9 {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                0 => {
                    p.dom_proofs.pop();
                }
                1 => {
                    p.dom_stores.pop();
                }
                2 => p.dom_proofs.swap(0, 2),
                3 => p.dom_stores.swap(0, 1),
                4 => {
                    p.conclusions_wd.pop();
                }
                5 => p.theorem_derivation = TheoremDerivationProof::UserTheorem,
                6 => p.builtin.as_mut().unwrap().arguments.clear(),
                7 => p.builtin.as_mut().unwrap().requirements.swap(0, 2),
                _ => {
                    p.builtin.as_mut().unwrap().conclusions.pop();
                }
            }
            assert!(
                c.compile_run(&run, "bad_integral_definition_stage")
                    .is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn integral_definition_elimination_preserves_every_output_and_its_order() {
    for source in [SOURCES[1], SOURCES[4]] {
        let (mut run, c) = super::execute(source);
        let outputs = invocation(&mut run).conclusions_wd.len();
        for index in 0..outputs - 1 {
            let (mut run, c) = super::execute(source);
            invocation(&mut run)
                .builtin
                .as_mut()
                .unwrap()
                .conclusions
                .swap(index, index + 1);
            assert!(
                c.compile_run(&run, "reordered_integral_output").is_err(),
                "{index}"
            );
        }
        invocation(&mut run).conclusions_wd.swap(0, outputs - 1);
        assert!(c.compile_run(&run, "reordered_integral_formation").is_err());
    }
}
#[test]
fn integral_definitions_keep_candidate_function_endpoints_and_value() {
    for (i, source) in SOURCES.iter().take(3).enumerate() {
        for change in 0..4 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let candidate = if i == 1 {
                &mut b.requirements[4]
            } else {
                &mut b.conclusions[0]
            };
            let Fact::AtomicFact(AtomicFact::HasRiemannIntegralFact(p)) = candidate else {
                panic!();
            };
            match change {
                0 => p.function = super::number_object("7"),
                1 => p.lower = super::number_object("7"),
                2 => p.upper = super::number_object("7"),
                _ => p.value = super::number_object("7"),
            }
            assert!(c
                .compile_run(&run, "changed_integral_definition_candidate")
                .is_err());
        }
    }
}
#[test]
fn integral_definitions_preserve_original_complete_function_formation() {
    for (i, source) in SOURCES.iter().enumerate() {
        for change in 0..3 {
            let (mut run, c) = super::execute(source);
            let original = if i == 1 || i == 4 {
                &mut theorem(&mut run).assumed_dom_facts[0].well_defined
            } else {
                &mut invocation(&mut run).conclusions_wd[0]
            };
            let FactWellDefinedProof::AtomicExceptEquality(wd) = original else {
                panic!();
            };
            let PredicateDomainProof::FunctionAnalysis(p) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!("original function analysis formation");
            };
            match change {
                0 => p.requirements.clear(),
                1 => p.function_domain.domain = Obj::StandardSet(StandardSet::Q),
                _ => {
                    let Fact::AtomicFact(AtomicFact::SubsetFact(q)) =
                        &mut p.requirements[2].requirement
                    else {
                        panic!();
                    };
                    q.right = Obj::StandardSet(StandardSet::Q);
                }
            }
            assert!(
                c.compile_run(&run, "damaged_integral_definition_domain")
                    .is_err(),
                "{i}/{change}"
            );
        }
    }
}
#[test]
fn riemann_definition_requires_zero_clause_and_original_epsilon_guard() {
    for source in [SOURCES[0], SOURCES[1]] {
        for change in 0..4 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let clauses = if b.theorem == BuiltinTheoremId::RiemannIntegralFromDefinition {
                &mut b.requirements[4..]
            } else {
                &mut b.conclusions[..]
            };
            if change == 0 {
                let Fact::OrFact(p) = &mut clauses[4] else {
                    panic!();
                };
                p.facts.swap(0, 1);
            } else {
                let Fact::ForallFact(p) = &mut clauses[5] else {
                    panic!();
                };
                match change {
                    1 => p.dom_facts.clear(),
                    2 => {
                        p.typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::R))
                    }
                    _ => {
                        let Fact::AtomicFact(AtomicFact::LessFact(q)) = &mut p.dom_facts[0] else {
                            panic!();
                        };
                        std::mem::swap(&mut q.left, &mut q.right);
                    }
                }
            }
            assert!(c.compile_run(&run, "changed_riemann_clause").is_err());
        }
    }
}
#[test]
fn darboux_definition_requires_exact_partition_and_cell_guards() {
    for source in [SOURCES[3], SOURCES[4]] {
        for change in 0..7 {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let clauses = if b.theorem == BuiltinTheoremId::DarbouxEnclosureFromDefinition {
                &mut b.requirements[3..]
            } else {
                &mut b.conclusions[..]
            };
            match change {
                0 => {
                    let Fact::AtomicFact(AtomicFact::EqualFact(q)) = &mut clauses[5] else {
                        panic!();
                    };
                    std::mem::swap(&mut q.left, &mut q.right);
                }
                1 => {
                    let Fact::AtomicFact(AtomicFact::InFact(q)) = &mut clauses[2] else {
                        panic!();
                    };
                    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &mut q.set else {
                        panic!();
                    };
                    signature.dom_facts.swap(0, 1);
                }
                2 => {
                    let Fact::ForallFact(q) = &mut clauses[7] else {
                        panic!();
                    };
                    q.then_facts.swap(0, 1);
                }
                _ => {
                    let Fact::ForallFact(q) = &mut clauses[8] else {
                        panic!();
                    };
                    match change {
                        3 => q.dom_facts.clear(),
                        4 => q.dom_facts.swap(0, 1),
                        5 => q.then_facts.swap(0, 1),
                        _ => {
                            q.typed_parameters.groups[1].params[0].id =
                                q.typed_parameters.groups[0].params[0].id
                        }
                    }
                }
            }
            assert!(
                c.compile_run(&run, "changed_darboux_clause").is_err(),
                "{change}"
            );
        }
    }
}
