use crate::execute::execute_fact_stmt::multivariable::expression::SmoothCoordinateConstructorProof as C;
use crate::execute::execute_fact_stmt::multivariable::strategy::{
    MultivariableInteriorProof as P, MultivariableStrategyProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainRequirementProof;
use crate::prelude::*;

const TWO: &str =
    include_str!("../../../lean/examples/partial_derivative_guarded_two_bounds/statement.lit");
const SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/partial_derivative_guarded_log/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_guarded_other_axis/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_guarded_log_other_axis/statement.lit"),
    TWO,
    include_str!("../../../lean/examples/partial_derivative_guarded_nonzero/statement.lit"),
    include_str!(
        "../../../lean/examples/partial_derivative_guarded_positive_membership/statement.lit"
    ),
    include_str!(
        "../../../lean/examples/partial_derivative_guarded_negative_membership/statement.lit"
    ),
    include_str!(
        "../../../lean/examples/partial_derivative_guarded_nonzero_membership/statement.lit"
    ),
    include_str!("../../../lean/examples/partial_derivative_guarded_exponential/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_guarded_power/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_guarded_quotient/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_guarded_nonstrict/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_guarded_nested_domains/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_guarded_selector/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_guarded_real_membership/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_guarded_variable_axis/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_guarded_trigonometric/statement.lit"),
    include_str!(
        "../../../lean/examples/partial_derivative_guarded_logarithm_condition/statement.lit"
    ),
    include_str!("../../../lean/examples/partial_derivative_guarded_sqrt_condition/statement.lit"),
    include_str!(
        "../../../lean/examples/partial_derivative_guarded_log_sqrt_product/statement.lit"
    ),
    include_str!(
        "../../../lean/examples/partial_derivative_guarded_sqrt_log_product/statement.lit"
    ),
    include_str!("../../../lean/examples/partial_derivative_guarded_exp_log_sqrt/statement.lit"),
];
fn number(n: i64) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.to_string())))
}
fn geometry(run: &mut RunLitexCodeResult) -> &mut P {
    let f = super::forall_proof_mut(&mut run.statement_results[0]);
    for fact in &mut f.proved_then_facts {
        let p = super::atomic_proof_mut(&mut fact.verify_result);
        if let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MultivariableAnalysis(
                MultivariableStrategyProof::PartialDerivativeAt(p),
            ),
        ) = &mut p.searched_proof
        {
            return &mut p.stages.geometry;
        }
    }
    panic!("original smooth partial route")
}

#[test]
fn multivariable_interior_replays_actual_axis_guard_domains_and_selector_wd() {
    for source in SOURCES {
        let (run, c) = super::execute(source);
        let lean = c
            .compile_run(&run, "guarded")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(lean.contains("Litex.partialInteriorOfNeighborhood"));
        assert_eq!(lean, c.compile_run(&run, "guarded").unwrap());
    }
}

#[test]
fn multivariable_interior_compound_guard_keeps_nested_domain_and_derivative_wd() {
    for (source, changes) in [
        (
            include_str!(
                "../../../lean/examples/partial_derivative_guarded_log_sqrt_product/statement.lit"
            ),
            6,
        ),
        (
            include_str!(
                "../../../lean/examples/partial_derivative_guarded_exp_log_sqrt/statement.lit"
            ),
            7,
        ),
    ] {
        for change in 0..changes {
            let (mut run, compiler) = super::execute(source);
            let P::OpenGuards { guards, .. } = geometry(&mut run) else {
                panic!("open guards");
            };
            let operand = &mut guards[1].operands[0];
            match change {
                0 | 1 | 6 => {
                    let C::Multiply { left, right } = &mut operand.constructor else {
                        panic!("product");
                    };
                    let child = if change == 1 { right } else { left };
                    let child = if change == 6 {
                        let C::Elementary { argument, .. } = &mut child.constructor else {
                            panic!("outer exponential");
                        };
                        argument
                    } else {
                        child
                    };
                    let C::Elementary { domain, .. } = &mut child.constructor else {
                        panic!("elementary function");
                    };
                    let AtomicFact::InFact(fact) = &mut super::atomic_proof_mut(domain).fact else {
                        panic!("domain membership");
                    };
                    fact.set = Obj::StandardSet(StandardSet::C);
                }
                2 => {
                    let AtomicFact::InFact(fact) =
                        &mut super::atomic_proof_mut(&mut operand.value_real).fact
                    else {
                        panic!("value membership");
                    };
                    fact.element = number(9);
                }
                3 => {
                    let AtomicFact::InFact(fact) =
                        &mut super::atomic_proof_mut(&mut operand.derivative_real).fact
                    else {
                        panic!("derivative membership");
                    };
                    fact.set = Obj::StandardSet(StandardSet::C);
                }
                4 => {
                    let proof = operand
                        .derivative_source_well_defined
                        .as_detailed_mut()
                        .unwrap();
                    let obj = match proof {
                        DetailedObjWellDefinedProof::ByDef { obj, .. }
                        | DetailedObjWellDefinedProof::ByKnown { obj, .. } => obj,
                    };
                    *obj = number(9);
                }
                _ => operand.derivative_reduction.result = number(9),
            }
            assert!(
                compiler
                    .compile_run(&run, "altered_compound_guard")
                    .is_err(),
                "mutation {change}"
            );
        }
    }
}

#[test]
fn multivariable_interior_rejects_changed_domain_guards_order_and_point_proofs() {
    for change in 0..9 {
        let (mut run, c) = super::execute(TWO);
        let P::OpenGuards {
            domain,
            base,
            guards,
        } = geometry(&mut run)
        else {
            panic!("guard geometry")
        };
        match change {
            0 => *domain = Obj::StandardSet(StandardSet::R),
            1 => {
                guards.pop();
            }
            2 => guards.swap(0, 1),
            3 => {
                let AtomicFact::GreaterFact(f) = &mut guards[0].guard else {
                    panic!("strict guard")
                };
                f.right = number(1);
            }
            4 => guards[0].operands.swap(0, 1),
            5 => guards[0].point_condition = guards[1].point_condition.clone(),
            6 => {
                let AtomicFact::GreaterFact(f) =
                    &mut super::atomic_proof_mut(&mut guards[0].point_proof).fact
                else {
                    panic!("point proof")
                };
                f.right = number(1);
            }
            7 => {
                let P::FullEuclideanSpace { point_member, .. } = base.as_mut() else {
                    panic!("original full base")
                };
                let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(point_member).fact else {
                    panic!("member")
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
            _ => {
                let Fact::AtomicFact(AtomicFact::GreaterFact(f)) = &guards[0].point_condition
                else {
                    panic!("strict point")
                };
                guards[0].point_condition = GreaterEqualFact {
                    fact_id: f.fact_id,
                    left: f.left.clone(),
                    right: f.right.clone(),
                    line_file: f.line_file.clone(),
                }
                .into();
            }
        }
        assert!(
            c.compile_run(&run, "changed_guard").is_err(),
            "mutation {change}"
        );
    }
}

#[test]
fn multivariable_interior_retains_original_axis_one_and_operand_certificates() {
    for change in 0..7 {
        let (mut run, c) = super::execute(SOURCES[1]);
        let P::OpenGuards { guards, .. } = geometry(&mut run) else {
            panic!("guard geometry")
        };
        let operand = &mut guards[0].operands[0];
        match change {
            0 => operand.expression = number(9),
            1 => operand.value = number(9),
            2 => operand.value_reduction.source = number(9),
            3 => operand.derivative_expression = number(9),
            4 => operand.derivative_value = number(9),
            5 => {
                let C::Coordinate {
                    axis_comparison, ..
                } = &mut operand.constructor
                else {
                    panic!("coordinate")
                };
                super::equality_proof_mut(axis_comparison).fact.right = number(2);
            }
            _ => {
                let C::Coordinate { index_member, .. } = &mut operand.constructor else {
                    panic!("coordinate")
                };
                let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(index_member).fact else {
                    panic!("index membership")
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
        }
        assert!(
            c.compile_run(&run, "changed_operand").is_err(),
            "mutation {change}"
        );
    }
}

#[test]
fn multivariable_interior_keeps_elementary_power_and_division_requirements() {
    for case in 8..=10 {
        for change in 0..3 {
            let (mut run, c) = super::execute(SOURCES[case]);
            let P::OpenGuards { guards, .. } = geometry(&mut run) else {
                panic!("guard geometry")
            };
            let operand = &mut guards[if case == 10 { 1 } else { 0 }].operands[0];
            if change == 2 {
                operand.derivative_expression = number(9);
            } else {
                match &mut operand.constructor {
                    C::Elementary {
                        argument, domain, ..
                    } => {
                        if change == 1 {
                            argument.expression = number(9);
                        } else {
                            let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(domain).fact
                            else {
                                panic!("domain")
                            };
                            f.set = Obj::StandardSet(StandardSet::C);
                        }
                    }
                    C::NaturalPower {
                        base,
                        exponent_natural,
                    } => {
                        if change == 1 {
                            base.expression = number(9);
                        } else {
                            let AtomicFact::InFact(f) =
                                &mut super::atomic_proof_mut(exponent_natural).fact
                            else {
                                panic!("natural exponent")
                            };
                            f.set = Obj::StandardSet(StandardSet::R);
                        }
                    }
                    C::Divide { right, nonzero, .. } => {
                        if change == 1 {
                            right.expression = number(9);
                        } else {
                            let AtomicFact::NotEqualFact(f) =
                                &mut super::atomic_proof_mut(nonzero).fact
                            else {
                                panic!("nonzero")
                            };
                            f.right = number(1);
                        }
                    }
                    _ => panic!("original guarded operation"),
                }
            }
            assert!(
                c.compile_run(&run, "changed_guard_operation").is_err(),
                "case {case}, mutation {change}"
            );
        }
    }
}

#[test]
fn multivariable_interior_nested_membership_strategy_retains_all_requirements() {
    for change in 0..4 {
        let (mut run, c) = super::execute(SOURCES[12]);
        let root = super::forall_proof_mut(&mut run.statement_results[0]);
        let atomic = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
        let PredicateDomainProof::MultivariableAnalysis(formation) = &mut atomic
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .predicate_domain
        else {
            panic!("partial formation")
        };
        let PredicateDomainRequirementProof::Verified(proof) =
            &mut formation.requirements[4].result
        else {
            panic!("point membership")
        };
        let atomic = super::atomic_proof_mut(proof);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SetBuilderMembership(p),
        ) = &mut atomic.searched_proof
        else {
            panic!("original nested builder strategy")
        };
        match change {
            0 => p.proof_of_requirement_facts.clear(),
            1 => p.requirement_facts.swap(0, 1),
            2 => {
                p.requirement_facts.swap(0, 1);
                p.proof_of_requirement_facts.swap(0, 1);
            }
            _ => {
                p.requirement_facts.remove(0);
                p.proof_of_requirement_facts.remove(0);
            }
        }
        assert!(
            c.compile_run(&run, "changed_nested_membership").is_err(),
            "mutation {change}"
        );
    }
}

// Compiler emission only: the local Lean stress check remains incomplete.
#[test]
fn multivariable_interior_emits_composite_guard_certificate() {
    let source = r#"# Differentiate a coordinate with logarithm and square-root domain guards.
forall p cart(R,R):
    p(1) > 0
    ln(p(1)) * sqrt(p(1)) > 0
    =>:
        $has_partial_derivative_at(fn(q cart(R,R): q(1) > 0, ln(q(1)) * sqrt(q(1)) > 0) R {q(2)},p,2,2,1)
"#;
    let (run, compiler) = super::execute(source);
    let lean = compiler.compile_run(&run, "composite_guard").unwrap();
    assert_eq!(lean, compiler.compile_run(&run, "composite_guard").unwrap());
}

const GEOMETRY_SOURCES: &[&str] = &[
    include_str!("../../../lean/examples/partial_derivative_finite_function_domain/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_finite_function_axis/statement.lit"),
    include_str!(
        "../../../lean/examples/partial_derivative_finite_function_dimension/statement.lit"
    ),
    include_str!("../../../lean/examples/partial_derivative_finite_function_product/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_finite_function_guard/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_known_interior/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_known_interior_axis/statement.lit"),
    include_str!("../../../lean/examples/partial_derivative_known_interior_selector/statement.lit"),
];

#[test]
fn multivariable_interior_replays_exact_spaces_and_known_balls() {
    for (i, source) in GEOMETRY_SOURCES.iter().enumerate() {
        let (mut run, compiler) = super::execute(source);
        let original = geometry(&mut run);
        match i {
            0..=3 => assert!(matches!(original, P::ExactFiniteFunctionSpace { .. })),
            4 => assert!(matches!(original, P::OpenGuards { base, .. }
                if matches!(base.as_ref(), P::ExactFiniteFunctionSpace { .. }))),
            _ => assert!(matches!(original, P::Known { .. })),
        }
        let lean = compiler
            .compile_run(&run, "geometry")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(lean.contains("Litex.partialInteriorOfNeighborhood"));
        if i >= 5 {
            assert!(lean.contains("Litex.coordinatePathNeighborhoodOfInterior"));
        }
        assert_eq!(lean, compiler.compile_run(&run, "geometry").unwrap());
    }
}

#[test]
fn multivariable_interior_rejects_altered_finite_signatures_and_members() {
    for change in 0..6 {
        let (mut run, compiler) = super::execute(GEOMETRY_SOURCES[0]);
        let P::ExactFiniteFunctionSpace {
            source,
            target,
            point_member,
            ..
        } = geometry(&mut run)
        else {
            panic!("exact finite space")
        };
        match change {
            0 => source.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            1 => target.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            2 | 3 => {
                let signature = if change == 2 { source } else { target };
                let Obj::SetFormer(SetFormer::ClosedRange(range)) =
                    signature.set_bound_parameters.groups[0].param_type.as_mut()
                else {
                    panic!("index range")
                };
                range.end = Box::new(number(3));
            }
            _ => {
                let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(point_member).fact else {
                    panic!("point membership")
                };
                if change == 4 {
                    f.element = number(0);
                } else {
                    f.set = Obj::StandardSet(StandardSet::R);
                }
            }
        }
        assert!(
            compiler.compile_run(&run, "changed_geometry").is_err(),
            "mutation {change}"
        );
    }
}

#[test]
fn multivariable_interior_rejects_altered_known_ball_contracts() {
    for change in 0..10 {
        let (mut run, compiler) = super::execute(GEOMETRY_SOURCES[5]);
        let P::Known { condition, .. } = geometry(&mut run) else {
            panic!("known ball")
        };
        let Fact::ExistFact(exists) = condition else {
            panic!("radius existence")
        };
        let [QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(subset))] =
            exists.facts.as_mut_slice()
        else {
            panic!("ball inclusion")
        };
        let Obj::SetFormer(SetFormer::SetBuilder(ball)) = &mut subset.left else {
            panic!("ball")
        };
        match change {
            0 => {
                exists.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R))
            }
            1 => subset.right = Obj::StandardSet(StandardSet::R),
            2 => ball.param_set = Box::new(Obj::StandardSet(StandardSet::R)),
            3 => ball.facts.clear(),
            8 => exists.typed_parameters.groups[0].params[0].id = ball.param_binding.id,
            9 => ball.facts.push(ball.facts[0].clone()),
            _ => {
                let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(bound)) =
                    &mut ball.facts[0]
                else {
                    panic!("strict distance bound")
                };
                match change {
                    4 => bound.right = number(0),
                    5 => {
                        ball.facts[0] = QuantifierFreeFact::AtomicFact(AtomicFact::LessEqualFact(
                            LessEqualFact {
                                fact_id: bound.fact_id,
                                left: bound.left.clone(),
                                right: bound.right.clone(),
                                line_file: bound.line_file.clone(),
                            },
                        ))
                    }
                    _ => {
                        let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(norm)) =
                            &mut bound.left
                        else {
                            panic!("distance norm")
                        };
                        if change == 6 {
                            norm.dimension = Box::new(number(3));
                        } else {
                            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) =
                                norm.vector.as_mut()
                            else {
                                panic!("difference function")
                            };
                            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(s)) =
                                f.equal_to.as_mut()
                            else {
                                panic!("point difference")
                            };
                            s.right = Box::new(number(0));
                        }
                    }
                }
            }
        }
        assert!(
            compiler.compile_run(&run, "changed_ball").is_err(),
            "mutation {change}"
        );
    }
}
