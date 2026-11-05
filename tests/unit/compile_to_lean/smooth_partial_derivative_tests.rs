use crate::execute::execute_fact_stmt::multivariable::expression::{
    MultivariableReductionStep, SmoothCoordinateConstructorProof,
};
use crate::execute::execute_fact_stmt::multivariable::strategy::{
    MultivariableStrategyProof, PartialDerivativeAtStrategyProof,
};
use crate::prelude::*;
const COORDINATE: &str = r#"# Differentiate a coordinate projection along the same and a different axis.
forall p cart(R,R,R):
    $has_partial_derivative_at(fn(q cart(R,R,R)) R {q(1)},p,3,1,1)
forall p cart(R,R,R):
    $has_partial_derivative_at(fn(q cart(R,R,R)) R {q(1)},p,3,2,0)
"#;
const FINITE_INTERSECTION: &str = r#"# Different exact spellings give the same singleton and a derivative coefficient of one.
finite_set_size(intersect({1/2},{0.5})) $in R
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {finite_set_size(intersect({1/2},{0.5}))*q(1)},p,2,1,1)
"#;
const MATRIX_ZERO: &str = r#"# Replay a native matrix entry as an exact partial-derivative coefficient.
zero_matrix(2,2)(1,1) $in R
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {zero_matrix(2,2)(1,1)*q(1)},p,2,1,0)
"#;
const MATRIX_CALCULATED_PAIR: &str = r#"# Retain both original domain proofs while calculating both matrix indices.
zero_matrix(3,3)(1+1,1+2) $in R
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {zero_matrix(3,3)(1+1,1+2)*q(1)},p,2,1,0)
"#;

#[test]
fn smooth_partial_native_calculated_indices_reject_changed_calculation_and_beta_tapes() {
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(MATRIX_CALCULATED_PAIR);
        let root = super::forall_proof_mut(&mut run.statement_results[1]);
        let atomic = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MultivariableAnalysis(
                MultivariableStrategyProof::PartialDerivativeAt(p),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!()
        };
        let tape = &mut p.stages.coordinates[0].reduction.steps;
        let beta = tape
            .iter()
            .position(|s| matches!(s, MultivariableReductionStep::NativeMatrixBeta { .. }))
            .unwrap();
        let calculations = tape
            .iter()
            .enumerate()
            .filter_map(|(i, s)| {
                matches!(s, MultivariableReductionStep::ExactRational { .. }).then_some(i)
            })
            .collect::<Vec<_>>();
        assert_eq!(calculations.len(), 2);
        match mutation {
            3 => {
                let MultivariableReductionStep::ExactRational { value, .. } =
                    &mut tape[calculations[0]]
                else {
                    panic!()
                };
                *value = number(7);
            }
            4 => tape.swap(calculations[0], calculations[1]),
            5 => {
                tape.remove(calculations[0]);
            }
            6 => {
                tape.remove(beta);
            }
            _ => {
                let MultivariableReductionStep::NativeMatrixBeta {
                    source,
                    arguments,
                    expanded,
                } = &mut tape[beta]
                else {
                    panic!()
                };
                match mutation {
                    0 => arguments[0] = number(7),
                    1 => *expanded = number(7),
                    _ => *source.function.equal_to = number(7),
                }
            }
        }
        compiler.compile_run(&run, "changed_native_calculated").expect_err("the original calculations, matrix definition, ordered reduced arguments and complete beta tape must agree");
    }
}

#[test]
fn smooth_partial_native_calculated_indices_require_original_call_wd() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(MATRIX_CALCULATED_PAIR);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(first)) =
            &mut run.statement_results[0]
        else {
            panic!()
        };
        let atomic = super::atomic_proof_mut(&mut first.verify_result);
        let wd = &mut atomic
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0];
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = wd.as_detailed_mut().unwrap()
        else {
            panic!()
        };
        match mutation {
            0 => call.child_obj_well_defined.clear(),
            1 => call.requirement_fact_verified.clear(),
            _ => call.domain_fn_set = None,
        }
        compiler.compile_run(&run, "missing_native_calculated_wd").expect_err("normalizing input values cannot replace the original call's checked WD and domain facts");
    }
}
const CURRIED_PRODUCT: &str = r#"# Differentiate multiplication expressed as a function returning a function.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(fn(x R) (fn(y R) R) {fn(z R) R {x*z}})(q(1))(q(2))},p,2,1,p(2))
"#;
const FUNCTION_PARAMETER_SQUARE: &str = r#"# Differentiate a square function passed as an ordinary function-valued argument.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(fn(f (fn(x R) R)) R {f(q(1))})(fn(y R) R {y*y})},p,2,1,2*p(1))
"#;
const APPLIED_CURRIED: &str = r#"# Differentiate a curried product after substituting a calculated captured parameter.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(fn(t R) R {(fn(x R) (fn(y R) R) {fn(z R) R {t*x*z}})(q(1))(q(2))})(1+1)},p,2,1,2*p(2))
"#;

#[test]
fn smooth_partial_applied_curried_calls_reject_changed_outer_and_grouped_beta_tape() {
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(APPLIED_CURRIED);
        let tape = &mut proof(&mut run).stages.coordinates[0].reduction.steps;
        let beta = tape
            .iter()
            .enumerate()
            .filter_map(|(i, s)| {
                matches!(s, MultivariableReductionStep::AnonymousBeta { .. }).then_some(i)
            })
            .collect::<Vec<_>>();
        assert_eq!(beta.len(), 3);
        match mutation {
            3 => tape.swap(beta[1], beta[2]),
            4 => {
                tape.remove(beta[2]);
            }
            5 => tape.push(MultivariableReductionStep::ExactRational {
                source: number(1),
                value: number(2),
            }),
            _ => {
                let index = if mutation == 6 {
                    beta[0]
                } else if mutation == 2 {
                    beta[1]
                } else {
                    beta[2]
                };
                let MultivariableReductionStep::AnonymousBeta {
                    function,
                    arguments,
                    expanded,
                } = &mut tape[index]
                else {
                    panic!()
                };
                match mutation {
                    0 | 2 => function.equal_to = Box::new(number(7)),
                    1 | 6 => arguments[0] = number(7),
                    _ => *expanded = number(7),
                }
            }
        }
        compiler.compile_run(&run, "changed_applied_curried").expect_err("outer substitution, grouped beta order and endpoints must remain the recorded proof route");
    }
}

#[test]
fn smooth_partial_applied_curried_calls_require_the_complete_original_grouped_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
    for source in [
        APPLIED_CURRIED,
        r#"# Apply a curried function passed through its original function membership interface.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(fn(f (fn(x R) (fn(y R) R))) R {f(q(1))(q(2))})(fn(x R) (fn(y R) R) {fn(z R) R {x*z}})},p,2,1,p(2))
"#,
    ] {
        for mutation in 0..4 {
            let (mut run, compiler) = super::execute(source);
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::FunctionSpace(
                        FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(root),
                    ),
                ..
            } = proof(&mut run)
                .stages
                .body_well_defined
                .as_detailed_mut()
                .unwrap()
            else {
                panic!()
            };
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(outer),
                ..
            } = root.body_well_defined.as_detailed_mut().unwrap()
            else {
                panic!()
            };
            let DetailedObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::FunctionSpace(
                        FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(function),
                    ),
                ..
            } = outer.child_obj_well_defined[0].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            let DetailedObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(call),
                ..
            } = function.body_well_defined.as_detailed_mut().unwrap()
            else {
                panic!()
            };
            match mutation {
                0 => call.requirement_fact_verified.clear(),
                1 => call.child_obj_well_defined.clear(),
                2 => call.domain_fn_set = None,
                _ => {
                    call.requirement_fact_verified.pop();
                }
            }
            compiler
                .compile_run(&run, "missing_applied_curried_wd")
                .expect_err(
                "all original receiver, argument and guard evidence is required in its own scope",
            );
        }
    }
}

#[test]
fn smooth_partial_function_parameters_reject_changed_substitution_and_tape() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(FUNCTION_PARAMETER_SQUARE);
        let tape = &mut proof(&mut run).stages.coordinates[0].reduction.steps;
        let beta = tape
            .iter()
            .enumerate()
            .filter_map(|(i, s)| {
                matches!(s, MultivariableReductionStep::AnonymousBeta { .. }).then_some(i)
            })
            .collect::<Vec<_>>();
        assert_eq!(beta.len(), 2);
        if mutation == 4 {
            tape.swap(beta[0], beta[1]);
        } else if mutation == 5 {
            tape.remove(beta[1]);
        } else {
            let index = if mutation == 0 { beta[0] } else { beta[1] };
            let MultivariableReductionStep::AnonymousBeta {
                function,
                arguments,
                expanded,
            } = &mut tape[index]
            else {
                unreachable!()
            };
            match mutation {
                0 => {
                    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = &mut arguments[0]
                    else {
                        panic!()
                    };
                    f.equal_to = Box::new(number(7));
                }
                1 => function.equal_to = Box::new(number(7)),
                2 => arguments[0] = number(7),
                _ => *expanded = number(7),
            }
        }
        compiler
            .compile_run(&run, "changed_function_parameter")
            .expect_err(
                "original function argument, beta body, argument order and endpoint must match",
            );
    }
}

#[test]
fn smooth_partial_function_parameters_require_original_parameter_call_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        FnObjDomainFnSetEvidence, FunctionSpaceObjWellDefinedProofByDef,
    };
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(FUNCTION_PARAMETER_SQUARE);
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(root),
                ),
            ..
        } = proof(&mut run)
            .stages
            .body_well_defined
            .as_detailed_mut()
            .unwrap()
        else {
            panic!()
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(outer),
            ..
        } = root.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!()
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(function),
                ),
            ..
        } = outer.child_obj_well_defined[0].as_detailed_mut().unwrap()
        else {
            panic!()
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = function.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!()
        };
        match mutation {
            0 => call.requirement_fact_verified.clear(),
            1 => call.child_obj_well_defined.clear(),
            2 => call.domain_fn_set = None,
            _ => {
                let Some(FnObjDomainFnSetEvidence::InFunctionSet { fn_set, .. }) =
                    &mut call.domain_fn_set
                else {
                    panic!()
                };
                fn_set.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
            }
        }
        compiler.compile_run(&run, "missing_function_parameter_wd").expect_err("function parameters still require the checked original membership, signature and input WD");
    }
}

#[test]
fn smooth_partial_grouped_calls_reject_changed_steps_arguments_endpoints_and_order() {
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(CURRIED_PRODUCT);
        let tape = &mut proof(&mut run).stages.coordinates[0].reduction.steps;
        let beta = tape
            .iter()
            .enumerate()
            .filter_map(|(i, s)| {
                matches!(s, MultivariableReductionStep::AnonymousBeta { .. }).then_some(i)
            })
            .collect::<Vec<_>>();
        assert_eq!(beta.len(), 2);
        if mutation < 3 {
            let MultivariableReductionStep::AnonymousBeta {
                function,
                arguments,
                expanded,
            } = &mut tape[beta[1]]
            else {
                unreachable!()
            };
            match mutation {
                0 => *expanded = number(99),
                1 => arguments[0] = number(7),
                _ => function.equal_to = Box::new(number(99)),
            }
        } else {
            match mutation {
                3 => tape.swap(beta[0], beta[1]),
                4 => {
                    tape.remove(beta[0]);
                }
                5 => tape.clear(),
                6 => tape.push(MultivariableReductionStep::ExactRational {
                    source: number(1),
                    value: number(2),
                }),
                _ => {
                    let MultivariableReductionStep::AnonymousBeta {
                        function,
                        arguments,
                        expanded,
                    } = &tape[beta[0]]
                    else {
                        unreachable!()
                    };
                    tape.push(MultivariableReductionStep::AnonymousBeta {
                        function: function.clone(),
                        arguments: arguments.clone(),
                        expanded: expanded.clone(),
                    });
                }
            }
        }
        compiler
            .compile_run(&run, "changed_grouped_calls")
            .expect_err("every recorded group, substitution and tape endpoint must match");
    }
}

#[test]
fn smooth_partial_grouped_calls_require_the_complete_original_call_wd() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(CURRIED_PRODUCT);
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(body),
                ),
            ..
        } = proof(&mut run)
            .stages
            .body_well_defined
            .as_detailed_mut()
            .unwrap()
        else {
            panic!()
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = body.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!()
        };
        match mutation {
            0 => {
                call.requirement_fact_verified.pop();
            }
            1 => {
                call.child_obj_well_defined.pop();
            }
            _ => call.domain_fn_set = None,
        }
        compiler
            .compile_run(&run, "missing_grouped_domain")
            .expect_err("later groups must retain their original domain and WD evidence");
    }
}

#[test]
fn smooth_partial_native_matrix_rejects_changed_expansion_arguments_and_definition() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(MATRIX_ZERO);
        let root = super::forall_proof_mut(&mut run.statement_results[1]);
        let atomic = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MultivariableAnalysis(
                MultivariableStrategyProof::PartialDerivativeAt(p),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!()
        };
        let tape = &mut p.stages.coordinates[0].reduction.steps;
        let index = tape
            .iter()
            .position(|s| matches!(s, MultivariableReductionStep::NativeMatrixBeta { .. }))
            .expect("original native matrix step");
        if mutation == 4 {
            tape.remove(index);
        } else {
            let MultivariableReductionStep::NativeMatrixBeta {
                source,
                arguments,
                expanded,
            } = &mut tape[index]
            else {
                unreachable!()
            };
            match mutation {
                0 => *expanded = number(7),
                1 => arguments[0] = number(2),
                2 => *source.function.equal_to = number(3),
                _ => source.function.body.set_bound_parameters.groups[0]
                    .params
                    .clear(),
            }
        }
        compiler
            .compile_run(&run, "changed_native_matrix")
            .expect_err(
            "original matrix definition, arguments, expanded body and complete tape are required",
        );
    }
}

#[test]
fn smooth_partial_finite_intersection_rejects_changed_certificate_and_tape() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(FINITE_INTERSECTION);
        let root = super::forall_proof_mut(&mut run.statement_results[1]);
        let atomic = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MultivariableAnalysis(
                MultivariableStrategyProof::PartialDerivativeAt(p),
            ),
        ) = &mut atomic.searched_proof
        else {
            panic!()
        };
        let tape = &mut p.stages.coordinates[0].reduction.steps;
        let index = tape
            .iter()
            .position(|s| matches!(s, MultivariableReductionStep::FiniteSetEvaluation { .. }))
            .expect("original finite-set certificate");
        if mutation == 4 {
            tape.remove(index);
        } else if mutation == 5 {
            tape.push(MultivariableReductionStep::ExactRational {
                source: number(0),
                value: number(1),
            });
        } else {
            let MultivariableReductionStep::FiniteSetEvaluation {
                source,
                left,
                right,
                value,
            } = &mut tape[index]
            else {
                unreachable!()
            };
            match mutation {
                0 => *left = EvalRational::new(0, 1).unwrap(),
                1 => *right = EvalRational::new(7, 1).unwrap(),
                2 => *value = number(0),
                _ => *source = number(0),
            }
        }
        compiler
            .compile_run(&run, "changed_finite_intersection")
            .expect_err("exact source, scalar operands, result and complete tape are required");
    }
}

fn proof(run: &mut RunLitexCodeResult) -> &mut PartialDerivativeAtStrategyProof {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::MultivariableAnalysis(
            MultivariableStrategyProof::PartialDerivativeAt(p),
        ),
    ) = &mut atomic.searched_proof
    else {
        panic!("original coordinate strategy")
    };
    p
}
fn number(n: i64) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.to_string())))
}
#[test]
fn smooth_partial_derivative_rejects_changed_subject_reduction_and_coordinate_selection() {
    for mutation in 0..9 {
        let (mut run, c) = super::execute(COORDINATE);
        let p = &mut proof(&mut run).stages;
        match mutation {
            0 => p.coordinates[0].row = 2,
            1 => p.coordinates[0].first_axis = number(2),
            2 => p.coordinates[0].second_axis = Some(number(1)),
            3 => p.coordinates[0].first.value = number(9),
            4 => p.coordinates[0].first.derivative_expression = number(0),
            5 => p.coordinates[0].first.derivative_value = number(9),
            6 => p.coordinates[0].first.value_reduction.steps.push(
                MultivariableReductionStep::ExactRational {
                    source: number(1),
                    value: number(9),
                },
            ),
            7 => p.conclusion_equalities[0].target_reduction.source = number(9),
            _ => p.coordinates[0].first.constructor = SmoothCoordinateConstructorProof::Constant,
        }
        c.compile_run(&run, "changed_smooth_partial")
            .expect_err("exact selected subjects and reduction tape");
    }
}
#[test]
fn smooth_partial_derivative_rejects_changed_axis_comparison_and_final_equality() {
    for mutation in 0..3 {
        let (mut run, c) = super::execute(COORDINATE);
        let p = &mut proof(&mut run).stages;
        if mutation < 2 {
            let SmoothCoordinateConstructorProof::Coordinate {
                index_member,
                axis_comparison,
                ..
            } = &mut p.coordinates[0].first.constructor
            else {
                panic!("coordinate")
            };
            if mutation == 0 {
                let a = super::atomic_proof_mut(index_member);
                let AtomicFact::InFact(m) = &mut a.fact else {
                    panic!("membership")
                };
                m.element = number(2);
            } else {
                super::equality_proof_mut(axis_comparison).fact.right = number(2);
            }
        } else {
            super::equality_proof_mut(&mut p.conclusion_equalities[0].equality)
                .fact
                .right = number(9);
        }
        c.compile_run(&run, "changed_smooth_evidence")
            .expect_err("original index, axis and conclusion children");
    }
}

#[test]
fn smooth_partial_derivative_rejects_changed_elementary_rule_child_and_domain() {
    use crate::execute::execute_fact_stmt::pointwise_elementary::ElementaryRealFunction as K;
    for source in [
        r#"# Differentiate the first-coordinate sine.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {sin(q(1))},p,2,1,cos(p(1)))
"#,
        r#"# Differentiate a logarithm using the positive exponential argument.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {ln(exp(q(1)))},p,2,1,exp(p(1))/exp(p(1)))
"#,
        r#"# Differentiate a square root using the strictly positive exponential argument.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {sqrt(exp(q(1)))},p,2,1,(exp(p(1))/2)/sqrt(exp(p(1))))
"#,
    ] {
        for change in 0..9 {
            let (mut run, c) = super::execute(source);
            let p = &mut proof(&mut run).stages.coordinates[0].first;
            let SmoothCoordinateConstructorProof::Elementary {
                kind,
                argument,
                domain,
            } = &mut p.constructor
            else {
                panic!("original elementary rule");
            };
            match change {
                0 => *kind = K::Cos,
                1 => argument.expression = number(0),
                2 | 3 | 8 => {
                    let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(domain).fact else {
                        panic!("original point-domain fact");
                    };
                    if change == 2 {
                        f.element = number(0);
                    } else if change == 3 {
                        f.set = Obj::StandardSet(StandardSet::C);
                    } else {
                        f.set = Obj::StandardSet(if f.set == Obj::StandardSet(StandardSet::RPos) {
                            StandardSet::R
                        } else {
                            StandardSet::RPos
                        });
                    }
                }
                4 => p.derivative_expression = number(0),
                5 => p.value_reduction.result = number(0),
                6 => argument.derivative_expression = number(0),
                _ => p.expression = number(0),
            }
            assert!(
                c.compile_run(&run, "changed_elementary").is_err(),
                "mutation {change}: {source}"
            );
        }
    }
}

#[test]
fn smooth_partial_derivative_replays_guarded_interior() {
    let source = "forall p cart(R,R):\n    p(1) > 0\n    =>:\n        $has_partial_derivative_at(fn(q cart(R,R): q(1) > 0) R {ln(q(1))},p,2,1,1/p(1))\n";
    let (run, c) = super::execute(source);
    let lean = c.compile_run(&run, "guarded_interior").unwrap();
    assert!(lean.contains("Litex.partialInteriorOfNeighborhood"));
}

#[test]
fn smooth_partial_derivative_preserves_reduction_tape_under_elementary_operations() {
    for change in 0..3 {
        let (mut run, c) = super::execute(
            r#"# Replay exact reductions inside a sine and its chain-rule coefficient.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {sin(q(1)*(1+1))},p,2,1,cos(p(1)*2)*2)
"#,
        );
        let p = &mut proof(&mut run).stages.coordinates[0].reduction;
        assert!(!p.steps.is_empty());
        match change {
            0 => p.steps.clear(),
            1 => p.steps.push(MultivariableReductionStep::ExactRational {
                source: number(1),
                value: number(9),
            }),
            _ => p.source = number(9),
        }
        assert!(
            c.compile_run(&run, "changed_elementary_reduction").is_err(),
            "mutation {change}"
        );
    }
}

const SQUARE: &str = r#"# Differentiate the square of a coordinate at an arbitrary real point.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {q(1)^2},p,2,1,2*p(1))
"#;
const QUOTIENT: &str = r#"# Divide a coordinate by a nonzero constant, including denominator one.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {q(1)/2},p,2,1,1/2)

forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {q(1)/1},p,2,1,1)
"#;

#[test]
fn smooth_partial_derivative_rejects_changed_quotient_children_and_nonzero_subjects() {
    for mutation in 0..4 {
        let (mut run, c) = super::execute(QUOTIENT);
        let p = &mut proof(&mut run).stages.coordinates[0].first;
        let SmoothCoordinateConstructorProof::Divide { right, nonzero, .. } = &mut p.constructor
        else {
            panic!("original quotient")
        };
        match mutation {
            0 | 1 => {
                let AtomicFact::NotEqualFact(f) = &mut super::atomic_proof_mut(nonzero).fact else {
                    panic!("denominator nonzero")
                };
                if mutation == 0 {
                    f.left = number(3);
                } else {
                    f.right = number(1);
                }
            }
            2 => right.expression = number(3),
            _ => p.derivative_expression = number(0),
        }
        assert!(
            c.compile_run(&run, "changed_quotient").is_err(),
            "mutation {mutation}"
        );
    }
}
const SEPARATE: &str = r#"# Differentiate two independently reduced coordinate powers along the first axis.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {q(1)^(1+1)+q(2)^(2+1)},p,2,1,2*p(1))
"#;

#[test]
fn smooth_partial_derivative_rejects_changed_power_and_nested_tape() {
    for mutation in 0..8 {
        let (mut run, c) = super::execute(SQUARE);
        let p = &mut proof(&mut run).stages.coordinates[0].first;
        assert_eq!(p.derivative_reduction.steps.len(), 1);
        match mutation {
            0 => p.derivative_reduction.steps.clear(),
            1 => {
                let MultivariableReductionStep::ExactRational { value, .. } =
                    &mut p.derivative_reduction.steps[0]
                else {
                    panic!("exact index")
                };
                *value = number(2);
            }
            2 => p
                .derivative_reduction
                .steps
                .push(MultivariableReductionStep::ExactRational {
                    source: number(7),
                    value: number(7),
                }),
            3 => {
                let MultivariableReductionStep::ExactRational { source, .. } =
                    &mut p.derivative_reduction.steps[0]
                else {
                    panic!("exact index")
                };
                *source = number(1);
            }
            4 => p.derivative_reduction.result = number(9),
            5 | 6 => {
                let SmoothCoordinateConstructorProof::NaturalPower {
                    base,
                    exponent_natural,
                } = &mut p.constructor
                else {
                    panic!("natural power")
                };
                if mutation == 5 {
                    let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(exponent_natural).fact
                    else {
                        panic!("natural exponent")
                    };
                    f.element = number(3);
                } else {
                    base.expression = number(2);
                }
            }
            _ => p.derivative_expression = number(0),
        }
        c.compile_run(&run, "changed_power")
            .expect_err("exact power children and reduction tape");
    }
}

#[test]
fn smooth_partial_derivative_rejects_missing_reordered_or_extra_body_reductions() {
    for mutation in 0..4 {
        let (mut run, c) = super::execute(SEPARATE);
        let p = &mut proof(&mut run).stages.coordinates[0].reduction;
        assert_eq!(p.steps.len(), 2);
        match mutation {
            0 => p.steps.swap(0, 1),
            1 => {
                p.steps.remove(0);
            }
            2 => p.steps.push(MultivariableReductionStep::ExactRational {
                source: number(1),
                value: number(9),
            }),
            _ => p.source = number(9),
        }
        assert!(
            c.compile_run(&run, "changed_body_reductions").is_err(),
            "mutation {mutation}: original ordered body tape"
        );
    }
}

const BETA_PRODUCT: &str = r#"# Differentiate a binary anonymous function of two coordinates.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(fn(x, y R) R {x*y})(q(1),q(2))},p,2,1,p(2))
"#;
const BETA_REDUCED: &str = r#"# Retain an argument calculation before anonymous beta reduction.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(fn(x, y R) R {x*y})(q(1),1+1)},p,2,1,2)
"#;

#[test]
fn smooth_partial_beta_rejects_changed_function_arguments_endpoint_and_order() {
    for mutation in 0..8 {
        let (mut run, compiler) = super::execute(BETA_REDUCED);
        let reduction = &mut proof(&mut run).stages.coordinates[0].reduction;
        let index = reduction
            .steps
            .iter()
            .position(|step| matches!(step, MultivariableReductionStep::AnonymousBeta { .. }))
            .unwrap();
        if mutation < 5 {
            let MultivariableReductionStep::AnonymousBeta {
                function,
                arguments,
                expanded,
            } = &mut reduction.steps[index]
            else {
                panic!("beta");
            };
            match mutation {
                0 => *expanded = number(99),
                1 => arguments.swap(0, 1),
                2 => arguments[1] = number(3),
                3 => function.equal_to = Box::new(number(99)),
                _ => {
                    arguments.pop();
                }
            }
        } else {
            match mutation {
                5 => {
                    reduction.steps.remove(index);
                }
                6 => {
                    assert!(index > 0);
                    reduction.steps.swap(index - 1, index);
                }
                _ => {
                    let MultivariableReductionStep::AnonymousBeta {
                        function,
                        arguments,
                        expanded,
                    } = &reduction.steps[index]
                    else {
                        panic!("beta");
                    };
                    reduction
                        .steps
                        .push(MultivariableReductionStep::AnonymousBeta {
                            function: function.clone(),
                            arguments: arguments.clone(),
                            expanded: expanded.clone(),
                        });
                }
            }
        }
        compiler
            .compile_run(&run, "changed_beta")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn smooth_partial_beta_rejects_missing_original_call_formation() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(BETA_PRODUCT);
        let body = &mut proof(&mut run).stages.body_well_defined;
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(wd),
                ),
            ..
        } = body.as_detailed_mut().unwrap()
        else {
            panic!("original literal formation");
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = wd.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!("original call formation");
        };
        match mutation {
            0 => call.requirement_fact_verified.clear(),
            1 => call.child_obj_well_defined.clear(),
            _ => call.domain_fn_set = None,
        }
        compiler
            .compile_run(&run, "missing_beta_wd")
            .expect_err(&format!("mutation {mutation}"));
    }
}

#[test]
fn smooth_partial_beta_retains_the_endpoint_before_following_calculation() {
    let source = r#"# Keep beta substitution and its following exact calculation as separate stages.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(fn(x R) R {1+1})(q(1))},p,2,1,0)
"#;
    let (mut run, compiler) = super::execute(source);
    let reduction = &proof(&mut run).stages.coordinates[0].reduction;
    let index = reduction
        .steps
        .iter()
        .position(|step| matches!(step, MultivariableReductionStep::AnonymousBeta { .. }))
        .unwrap();
    let MultivariableReductionStep::AnonymousBeta { expanded, .. } = &reduction.steps[index] else {
        panic!("selected beta");
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = expanded else {
        panic!("unreduced substitution endpoint");
    };
    assert_eq!(*sum.left, number(1));
    assert_eq!(*sum.right, number(1));
    let MultivariableReductionStep::ExactRational { source, value } = &reduction.steps[index + 1]
    else {
        panic!("following calculation");
    };
    assert_eq!(source, expanded);
    assert_eq!(*value, number(2));
    compiler.compile_run(&run, "beta_then_calculation").unwrap();
}

#[test]
fn smooth_partial_nested_body_rejects_missing_inner_call_formation() {
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef;
    let source = r#"# Differentiate a coordinate square computed through two nested formula calls.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(fn(x R) R {(fn(y R) R {y*y})(x)})(q(1))},p,2,1,2*p(1))
"#;
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(source);
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(outer),
                ),
            ..
        } = proof(&mut run)
            .stages
            .body_well_defined
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("coordinate literal")
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = outer.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!("outer call")
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(inner),
                ),
            ..
        } = call.child_obj_well_defined[0].as_detailed_mut().unwrap()
        else {
            panic!("original x literal")
        };
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(call),
            ..
        } = inner.body_well_defined.as_detailed_mut().unwrap()
        else {
            panic!("original y call")
        };
        match mutation {
            0 => call.requirement_fact_verified.clear(),
            1 => call.child_obj_well_defined.clear(),
            _ => call.domain_fn_set = None,
        }
        compiler
            .compile_run(&run, "missing_nested_formation")
            .expect_err("the original inner-call WD cannot be skipped");
    }
}

#[test]
fn smooth_partial_nested_body_rejects_changed_capture_argument_and_tape_order() {
    let source = r#"# Differentiate a nested call whose inner formula captures its outer parameter.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(fn(x R) R {(fn(y R) R {y*x})(x)})(q(1))},p,2,1,2*p(1))
"#;
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(source);
        let steps = &mut proof(&mut run).stages.coordinates[0].reduction.steps;
        let indices = steps
            .iter()
            .enumerate()
            .filter_map(|(i, step)| {
                matches!(step, MultivariableReductionStep::AnonymousBeta { .. }).then_some(i)
            })
            .collect::<Vec<_>>();
        assert_eq!(indices.len(), 2);
        if mutation == 4 {
            steps.swap(indices[0], indices[1]);
        } else {
            let MultivariableReductionStep::AnonymousBeta {
                function,
                arguments,
                expanded,
            } = &mut steps[indices[1]]
            else {
                unreachable!()
            };
            match mutation {
                0 => arguments[0] = number(7),
                1 => *expanded = number(7),
                2 => function.equal_to = Box::new(number(7)),
                _ => function.body.ret_set = Box::new(Obj::StandardSet(StandardSet::N)),
            }
        }
        compiler
            .compile_run(&run, "changed_nested_beta")
            .expect_err(
                "nested substitutions must match the exact recorded body and ordered arguments",
            );
    }
}

const TUPLE_FIRST: &str = r#"# Differentiate the first component of a tuple-valued expression.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(q(1)*q(2),q(1)+q(2))(1)},p,2,1,p(2))
"#;

#[test]
fn smooth_partial_tuple_projection_rejects_wrong_tuple_index_and_endpoint() {
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(TUPLE_FIRST);
        let p = &mut proof(&mut run).stages.coordinates[0].reduction;
        let i = p
            .steps
            .iter()
            .position(|step| matches!(step, MultivariableReductionStep::TupleProjection { .. }))
            .unwrap();
        match mutation {
            0..=3 => {
                let MultivariableReductionStep::TupleProjection { tuple, index } = &mut p.steps[i]
                else {
                    unreachable!()
                };
                match mutation {
                    0 => *index = 0,
                    1 => *index = 3,
                    2 => *index = usize::MAX,
                    _ => tuple.args.swap(0, 1),
                }
            }
            4 => {
                p.steps.remove(i);
            }
            5 => {
                let MultivariableReductionStep::TupleProjection { tuple, index } = &p.steps[i]
                else {
                    unreachable!()
                };
                let duplicate = MultivariableReductionStep::TupleProjection {
                    tuple: tuple.clone(),
                    index: *index,
                };
                p.steps.insert(i, duplicate);
            }
            _ => p.result = number(9),
        }
        compiler
            .compile_run(&run, "changed_tuple_projection")
            .expect_err("selected tuple, one-based index and final endpoint must be exact");
    }
}

#[test]
fn smooth_partial_tuple_projection_rejects_reordered_index_calculation() {
    let source = r#"# Differentiate the second tuple component selected by an exact calculated index.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(q(1)*q(2),q(1)+q(2))(1+1)},p,2,1,1)
"#;
    for remove in [false, true] {
        let (mut run, compiler) = super::execute(source);
        let steps = &mut proof(&mut run).stages.coordinates[0].reduction.steps;
        let calculation = steps
            .iter()
            .position(|s| matches!(s, MultivariableReductionStep::ExactRational { .. }))
            .unwrap();
        let projection = steps
            .iter()
            .position(|s| matches!(s, MultivariableReductionStep::TupleProjection { .. }))
            .unwrap();
        assert!(calculation < projection);
        if remove {
            steps.remove(calculation);
        } else {
            steps.swap(calculation, projection);
        }
        compiler
            .compile_run(&run, "reordered_tuple_index")
            .expect_err("the checked index calculation must precede projection");
    }
}

#[test]
fn tuple_uniform_membership_rejects_changed_index_carrier_and_coordinates() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty as Known,
        InFactSearchProofByKnownSpecialProperty as InKnown,
    };
    use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
        AnonymousFnBodyInReturnSetProof, FunctionSpaceObjWellDefinedProofByDef,
    };
    let source = r#"# Differentiate the second tuple component selected by an exact calculated index.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(q(1)*q(2),q(1)+q(2))(1+1)},p,2,1,1)
"#;
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(source);
        let DetailedObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(body),
                ),
            ..
        } = proof(&mut run)
            .stages
            .body_well_defined
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("original literal WD")
        };
        let AnonymousFnBodyInReturnSetProof::CheckedMembership(member) = &mut body.body_in_ret_set
        else {
            panic!("checked return membership")
        };
        let atomic = super::atomic_proof_mut(member);
        let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(Known::InFact(
            InKnown::UniformTupleCoordinateCarrier(p),
        )) = &mut atomic.searched_proof
        else {
            panic!("original uniform tuple evidence")
        };
        match mutation {
            0 => p.index = number(1),
            1 => {
                p.coordinates.pop();
            }
            2 => p.coordinates.swap(0, 1),
            3 => p.coordinates[0].set = StandardSet::N,
            4 => p.carrier = StandardSet::N,
            _ => p.tuple.value.args.swap(0, 1),
        }
        compiler
            .compile_run(&run, "changed_uniform_tuple")
            .expect_err(
                "the original tuple, index, carrier and every coordinate proof are required",
            );
    }
}

#[test]
fn smooth_partial_periodic_rejects_changed_source_coefficient_value_and_endpoint() {
    let source = r#"# Differentiate a coordinate multiplied by sine of one complete turn.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {sin(2*pi)*q(1)},p,2,1,0)
"#;
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(source);
        let p = &mut proof(&mut run).stages.coordinates[0].reduction;
        if mutation == 3 {
            p.steps.clear();
        } else if mutation == 4 {
            p.result = number(7);
        } else {
            let (source, proof) = p
                .steps
                .iter_mut()
                .find_map(|s| match s {
                    MultivariableReductionStep::PeriodicTrig { source, proof } => {
                        Some((source, proof))
                    }
                    _ => None,
                })
                .expect("original periodic record");
            match mutation {
                0 => *source = number(7),
                1 => proof.coefficient = number(7),
                _ => proof.value = number(7),
            }
        }
        compiler
            .compile_run(&run, "changed_periodic")
            .expect_err("the exact source, coefficient, value and ordered tape must be retained");
    }
}

#[test]
fn smooth_partial_periodic_rejects_sibling_and_parent_reordering() {
    for (source, parent) in [
        (
            r#"# Differentiate after two exact trigonometric values combine to one.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {(sin(pi/6)+cos(pi/3))*q(1)},p,2,1,1)
"#,
            false,
        ),
        (
            r#"# Differentiate a nested trigonometric constant times a coordinate.
forall p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {sin(cos(pi/2))*q(1)},p,2,1,0)
"#,
            true,
        ),
    ] {
        let (mut run, compiler) = super::execute(source);
        let steps = &mut proof(&mut run).stages.coordinates[0].reduction.steps;
        let positions = steps
            .iter()
            .enumerate()
            .filter_map(|(i, s)| {
                matches!(s, MultivariableReductionStep::PeriodicTrig { .. }).then_some(i)
            })
            .collect::<Vec<_>>();
        assert_eq!(positions.len(), 2, "{source}");
        if parent {
            assert_eq!(positions[1], positions[0] + 1);
        }
        steps.swap(positions[0], positions[1]);
        compiler
            .compile_run(&run, "reordered_periodic")
            .expect_err("periodic children and their parent must follow the original tape order");
    }
}

#[test]
fn smooth_partial_integer_period_rejects_changed_membership_tape() {
    let source = r#"# Differentiate a coordinate with two independent integral sine periods.
forall k,l Z, p cart(R,R):
    $has_partial_derivative_at(fn(q cart(R,R)) R {sin((2*k-4*l+13/6)*pi)*q(1)},p,2,1,1/2)
"#;
    for mutation in 0..7 {
        let (mut run, compiler) = super::execute(source);
        let p = proof(&mut run).stages.coordinates[0]
            .reduction
            .steps
            .iter_mut()
            .find_map(|step| match step {
                MultivariableReductionStep::PeriodicTrig { proof, .. } => Some(proof),
                _ => None,
            })
            .expect("original integral-period certificate");
        assert_eq!(p.integer_requirements.len(), 2);
        match mutation {
            0 => p.integer_requirements.clear(),
            1 => {
                p.integer_requirements.pop();
            }
            2 => p.integer_requirements.swap(0, 1),
            3 | 4 => {
                let AtomicFact::InFact(fact) =
                    &mut super::atomic_proof_mut(&mut p.integer_requirements[0]).fact
                else {
                    panic!()
                };
                if mutation == 3 {
                    fact.set = Obj::StandardSet(StandardSet::R);
                } else {
                    fact.element = number(7);
                }
            }
            5 => p.coefficient = number(7),
            _ => p.value = number(7),
        }
        compiler
            .compile_run(&run, "bad_integer_period")
            .expect_err("retain exact coefficient, value, ordered integer subjects and carriers");
    }
}
