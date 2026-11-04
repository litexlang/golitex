use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const VECTOR: &str = include_str!("../../../lean/examples/euclidean_norm_zero/statement.lit");
const MATRIX: &str = include_str!("../../../lean/examples/frobenius_norm_zero/statement.lit");

fn retain_reverse_shape(b: &mut crate::execute::execute_by_stmt::BuiltinThmApplication) {
    let Fact::ForallFact(forward) = &b.conclusions[0] else {
        panic!()
    };
    let forward = forward.clone();
    let Fact::ForallFact(reverse) = &mut b.conclusions[1] else {
        panic!()
    };
    reverse.dom_facts[0] = forward.then_facts[0].clone().into();
    let Fact::AtomicFact(norm) = &forward.dom_facts[0] else {
        panic!()
    };
    reverse.then_facts[0] = ExistOrAndChainAtomicFact::AtomicFact(norm.clone());
}

#[test]
fn norm_zero_replays_both_original_implications_for_complex_real_and_empty_domains() {
    for (source, law) in [
        (VECTOR, "euclideanNormZeroFormula"),
        (MATRIX, "frobeniusNormZeroCharacterization"),
        (
            include_str!("../../../lean/examples/euclidean_norm_zero_real/statement.lit"),
            "euclideanNormZeroFormula",
        ),
        (
            include_str!("../../../lean/examples/frobenius_norm_zero_real/statement.lit"),
            "frobeniusNormZeroCharacterization",
        ),
        (
            include_str!("../../../lean/examples/euclidean_norm_zero_empty/statement.lit"),
            "euclideanNormZeroFormula",
        ),
        (
            include_str!("../../../lean/examples/frobenius_norm_zero_empty/statement.lit"),
            "frobeniusNormZeroCharacterization",
        ),
    ] {
        let (mut run, compiler) = super::execute(source);
        let premises = invocation(&mut run)
            .builtin
            .as_ref()
            .unwrap()
            .conclusions
            .iter()
            .map(|fact| {
                let Fact::ForallFact(clause) = fact else {
                    panic!("original norm-zero implication")
                };
                clause.dom_facts[0].fact_id()
            })
            .collect::<Vec<_>>();
        assert_eq!(premises.len(), 2);
        let output = compiler
            .compile_run(&run, "norm_zero")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains(&format!("Litex.{law}")));
        for (index, premise) in premises.iter().enumerate() {
            assert!(
                output.contains(&format!(").{} h_{}", index + 1, premise.value())),
                "retain the direction and exact premise of each original implication"
            );
        }
        assert_eq!(output, compiler.compile_run(&run, "norm_zero").unwrap());
    }
}

#[test]
fn norm_zero_requires_all_original_requirement_and_conditional_wd_stages() {
    for source in [VECTOR, MATRIX] {
        for change in [
            "proof",
            "store",
            "wd",
            "conclusion",
            "order",
            "subject",
            "fact_id",
        ] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            match change {
                "proof" => {
                    call.dom_proofs.pop();
                }
                "store" => {
                    call.dom_stores.pop();
                }
                "wd" => {
                    call.conclusions_wd.pop();
                }
                "conclusion" => {
                    call.builtin.as_mut().unwrap().conclusions.pop();
                }
                "order" => {
                    call.dom_proofs.swap(0, 1);
                }
                _ => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) =
                        &mut call.builtin.as_mut().unwrap().requirements[0]
                    else {
                        panic!()
                    };
                    if change == "subject" {
                        f.element = super::number_object("99");
                    } else {
                        f.fact_id = FactId::new(u64::MAX);
                    }
                }
            }
            assert!(compiler.compile_run(&run, change).is_err(), "{change}");
        }
    }
}

#[test]
fn norm_zero_rejects_swapped_implications_extra_guards_and_missing_branches() {
    for source in [VECTOR, MATRIX] {
        for change in ["swap", "guard", "then", "reverse"] {
            let (mut run, compiler) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            if change == "swap" {
                b.conclusions.swap(0, 1);
            } else {
                let Fact::ForallFact(f) = &mut b.conclusions[1] else {
                    panic!()
                };
                match change {
                    "guard" => f.dom_facts.push(f.dom_facts[0].clone()),
                    "then" => f.then_facts.clear(),
                    _ => {
                        let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut f.dom_facts[0]
                        else {
                            panic!()
                        };
                        std::mem::swap(&mut eq.left, &mut eq.right);
                    }
                }
            }
            assert!(compiler.compile_run(&run, change).is_err(), "{change}");
        }
    }
}

#[test]
fn norm_zero_rejects_changed_zero_function_value_domain_target_and_guard() {
    for change in ["value", "domain", "target", "guard"] {
        let (mut run, compiler) = super::execute(VECTOR);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::ForallFact(f) = &mut b.conclusions[0] else {
            panic!()
        };
        let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut f.then_facts[0]
        else {
            panic!()
        };
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(zero)) = &mut eq.right else {
            panic!()
        };
        match change {
            "value" => zero.equal_to = Box::new(super::number_object("1")),
            "domain" => {
                let Obj::SetFormer(SetFormer::ClosedRange(range)) =
                    zero.body.set_bound_parameters.groups[0].param_type.as_mut()
                else {
                    panic!()
                };
                range.start = Box::new(super::number_object("0"));
            }
            "target" => zero.body.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
            _ => {
                let Fact::AtomicFact(guard) = &f.dom_facts[0] else {
                    panic!()
                };
                zero.body
                    .dom_facts
                    .push(QuantifierFreeFact::AtomicFact(guard.clone()));
            }
        }
        retain_reverse_shape(b);
        let error = compiler.compile_run(&run, change).unwrap_err();
        assert_eq!(
            error.route, "NormZero/ExactZeroFunction",
            "{change}: {error}"
        );
    }
}

#[test]
fn norm_zero_rejects_changed_matrix_zero_shape_and_norm_subject() {
    for change in [
        "zero_rows",
        "zero_cols",
        "norm_rows",
        "norm_cols",
        "norm_subject",
        "norm_value",
    ] {
        let (mut run, compiler) = super::execute(MATRIX);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::ForallFact(f) = &mut b.conclusions[0] else {
            panic!()
        };
        if change.starts_with("zero") {
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                &mut f.then_facts[0]
            else {
                panic!()
            };
            let Obj::MatrixOperator(MatrixOperator::ZeroMatrix(z)) = &mut eq.right else {
                panic!()
            };
            if change == "zero_rows" {
                z.rows = Box::new(super::number_object("7"));
            } else {
                z.cols = Box::new(super::number_object("7"));
            }
        } else {
            let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = &mut f.dom_facts[0] else {
                panic!()
            };
            if change == "norm_value" {
                eq.right = super::number_object("1");
            } else {
                let Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(z)) = &mut eq.left else {
                    panic!()
                };
                match change {
                    "norm_rows" => z.rows = Box::new(super::number_object("7")),
                    "norm_cols" => z.cols = Box::new(super::number_object("7")),
                    _ => z.matrix = Box::new(super::number_object("7")),
                }
            }
        }
        retain_reverse_shape(b);
        let error = compiler.compile_run(&run, change).unwrap_err();
        let expected = if change.starts_with("zero") {
            "NormZero/ZeroMatrixDimensions"
        } else if change == "norm_value" {
            "NormZero/OrderedImplications"
        } else {
            "NormZero/OriginalNorm"
        };
        assert_eq!(error.route, expected, "{change}: {error}");
    }
}

#[test]
fn norm_zero_requires_original_local_assumption_and_then_formation_evidence() {
    for source in [VECTOR, MATRIX] {
        for branch in 0..2 {
            for change in ["assumption", "then", "assumption_store"] {
                let (mut run, compiler) = super::execute(source);
                let call = invocation(&mut run);
                let FactWellDefinedProof::ForallFact(wd) = &mut call.conclusions_wd[branch] else {
                    panic!()
                };
                let detail = wd.as_detailed_mut().unwrap();
                match change {
                    "assumption" => detail.assumed_dom_facts.clear(),
                    "then" => detail.then.clear(),
                    _ => {
                        let store = &mut detail.assumed_dom_facts[0].store_and_infer.store;
                        let StoreFactResult::AtomicFact(atomic) = store else {
                            panic!()
                        };
                        let AtomicFact::EqualFact(eq) = &mut atomic.fact else {
                            panic!()
                        };
                        eq.right = super::number_object("99");
                    }
                }
                assert!(
                    compiler.compile_run(&run, change).is_err(),
                    "{branch}/{change}"
                );
            }
        }
    }
}

#[test]
fn norm_zero_requires_original_native_rule_identity_and_argument_order() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    for source in [VECTOR, MATRIX] {
        for change in ["derivation", "rule", "args"] {
            let (mut run, compiler) = super::execute(source);
            let call = invocation(&mut run);
            match change {
                "derivation" => call.theorem_derivation = TheoremDerivationProof::UserTheorem,
                "rule" => {
                    call.builtin.as_mut().unwrap().theorem =
                        crate::builtin_theorem::BuiltinTheoremId::EuclideanNormSquare
                }
                _ => call.builtin.as_mut().unwrap().arguments.swap(0, 1),
            }
            assert!(compiler.compile_run(&run, change).is_err(), "{change}");
        }
    }
}
