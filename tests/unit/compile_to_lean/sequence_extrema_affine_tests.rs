use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
const SOURCES: [&str; 10] = [
    include_str!("../../../lean/examples/sequence_limsup_add_constant/statement.lit"),
    include_str!("../../../lean/examples/sequence_limsup_scale_nonnegative/statement.lit"),
    include_str!("../../../lean/examples/sequence_limsup_scale_negative/statement.lit"),
    include_str!("../../../lean/examples/sequence_limsup_add_convergent/statement.lit"),
    include_str!("../../../lean/examples/sequence_limsup_sum_bound/statement.lit"),
    include_str!("../../../lean/examples/sequence_liminf_add_constant/statement.lit"),
    include_str!("../../../lean/examples/sequence_liminf_scale_nonnegative/statement.lit"),
    include_str!("../../../lean/examples/sequence_liminf_scale_negative/statement.lit"),
    include_str!("../../../lean/examples/sequence_liminf_add_convergent/statement.lit"),
    include_str!("../../../lean/examples/sequence_liminf_sum_bound/statement.lit"),
];
fn value(f: &mut Fact) -> &mut Obj {
    match f {
        Fact::AtomicFact(AtomicFact::HasSequenceLimsupFact(f)) => &mut f.value,
        Fact::AtomicFact(AtomicFact::HasSequenceLiminfFact(f)) => &mut f.value,
        Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f)) => &mut f.value,
        _ => panic!("actual sequence candidate"),
    }
}
#[test]
fn sequence_extrema_affine_replays_ten_actual_ids_deterministically() {
    use crate::builtin_theorem::BuiltinTheoremId::*;
    for (i, (source, id)) in SOURCES
        .into_iter()
        .zip([
            SequenceLimsupAddConstant,
            SequenceLimsupScaleNonnegative,
            SequenceLimsupScaleNegative,
            SequenceLimsupAddConvergent,
            SequenceLimsupSumBound,
            SequenceLiminfAddConstant,
            SequenceLiminfScaleNonnegative,
            SequenceLiminfScaleNegative,
            SequenceLiminfAddConvergent,
            SequenceLiminfSumBound,
        ])
        .enumerate()
    {
        let (mut run, c) = super::execute(source);
        let p = invocation(&mut run);
        assert_eq!(p.builtin.as_ref().unwrap().theorem, id);
        assert!(matches!(
            p.theorem_derivation,
            crate::execute::execute_by_stmt::TheoremDerivationProof::NativeSchema
        ));
        assert_eq!(p.dom_proofs.len(), [5, 6, 6, 6, 11][i % 5]);
        let law = [
            "sequenceExtremumAddConstant",
            "sequenceExtremumScaleNonnegative",
            "sequenceExtremumScaleNegative",
            "sequenceExtremumAddConvergent",
            "sequenceExtremumSumBound",
        ][i % 5];
        let out = c
            .compile_run(&run, "extrema_affine")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(out.contains(&format!("Litex.{law} {}", i < 5)));
        assert_eq!(out, c.compile_run(&run, "extrema_affine").unwrap());
    }
}
#[test]
fn sequence_extrema_affine_handles_zero_negative_closed_alias_literal_and_call_profiles() {
    for source in [
        include_str!("../../../lean/examples/sequence_limsup_add_constant_closed/statement.lit"),
        include_str!(
            "../../../lean/examples/sequence_limsup_scale_nonnegative_closed/statement.lit"
        ),
        include_str!("../../../lean/examples/sequence_limsup_scale_negative_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_limsup_add_convergent_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_limsup_sum_bound_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_add_constant_closed/statement.lit"),
        include_str!(
            "../../../lean/examples/sequence_liminf_scale_nonnegative_closed/statement.lit"
        ),
        include_str!("../../../lean/examples/sequence_liminf_scale_negative_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_add_convergent_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_sum_bound_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_limsup_add_constant_aliased/statement.lit"),
        include_str!("../../../lean/examples/sequence_limsup_sum_bound_aliased/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_add_constant_aliased/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_sum_bound_aliased/statement.lit"),
        include_str!(
            "../../../lean/examples/sequence_limsup_scale_nonnegative_literal/statement.lit"
        ),
        include_str!("../../../lean/examples/sequence_limsup_add_convergent_call/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_sum_bound_call/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "affine_profiles")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}
#[test]
fn sequence_extrema_affine_requires_original_ordered_proofs_stores_and_wd() {
    for source in SOURCES {
        for change in [
            "proof",
            "store",
            "wd",
            "proof_order",
            "store_order",
            "args",
            "conclusion",
            "derivation",
        ] {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "proof" => {
                    p.dom_proofs.pop();
                }
                "store" => {
                    p.dom_stores.pop();
                }
                "wd" => p.conclusions_wd.clear(),
                "proof_order" => p.dom_proofs.swap(0, 1),
                "store_order" => p.dom_stores.swap(0, 1),
                "args" => {
                    p.builtin.as_mut().unwrap().arguments.pop();
                }
                "conclusion" => p.builtin.as_mut().unwrap().conclusions.clear(),
                _ => {
                    p.theorem_derivation =
                        crate::execute::execute_by_stmt::TheoremDerivationProof::UserTheorem
                }
            }
            assert!(
                c.compile_run(&run, "bad_affine_stages").is_err(),
                "{change}"
            );
        }
    }
}
#[test]
fn sequence_extrema_affine_keeps_all_real_sequence_carriers() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for seq in 0..if i % 5 >= 3 { 3 } else { 2 } {
            let (mut run, c) = super::execute(source);
            let p = invocation(&mut run);
            let Fact::AtomicFact(AtomicFact::InFact(f)) =
                &mut p.builtin.as_mut().unwrap().requirements[seq]
            else {
                panic!()
            };
            let Obj::FunctionSpace(FunctionSpace::FnSet(s)) = &mut f.set else {
                panic!()
            };
            s.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
            assert!(
                c.compile_run(&run, "bad_affine_domain").is_err(),
                "{i} {seq}"
            );
        }
    }
}
#[test]
fn sequence_extrema_affine_requires_exact_candidate_values_and_visible_citations() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        let indices: &[usize] = if i % 5 == 4 {
            &[3, 4, 6]
        } else if i % 5 == 3 {
            &[3, 4]
        } else {
            &[2]
        };
        for &index in indices {
            for future in [false, true] {
                let (mut run, c) = super::execute(source);
                let p = invocation(&mut run);
                if future {
                    let id = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
                    let child = super::atomic_proof_mut(&mut p.dom_proofs[index]);
                    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                        &mut child.searched_proof
                    else {
                        panic!("actual known candidate")
                    };
                    cite.cite_fact_id = id;
                } else {
                    *value(&mut p.builtin.as_mut().unwrap().requirements[index]) =
                        super::number_object("0");
                }
                assert!(
                    c.compile_run(&run, "bad_affine_candidate").is_err(),
                    "{i} {index} {future}"
                );
            }
        }
    }
}
#[test]
fn sequence_extrema_scaling_requires_exact_scalar_sign_and_carrier() {
    for i in [1, 2, 6, 7] {
        for change in ["carrier", "sign", "orientation", "scalar"] {
            let (mut run, c) = super::execute(SOURCES[i]);
            let req = &mut invocation(&mut run).builtin.as_mut().unwrap().requirements;
            match change {
                "carrier" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut req[3] else {
                        panic!()
                    };
                    f.set = Obj::StandardSet(StandardSet::C);
                }
                "sign" => req[4] = req[3].clone(),
                _ => match &mut req[4] {
                    Fact::AtomicFact(AtomicFact::LessEqualFact(f)) => {
                        if change == "orientation" {
                            std::mem::swap(&mut f.left, &mut f.right);
                        } else {
                            f.right = super::number_object("1");
                        }
                    }
                    Fact::AtomicFact(AtomicFact::LessFact(f)) => {
                        if change == "orientation" {
                            std::mem::swap(&mut f.left, &mut f.right);
                        } else {
                            f.left = super::number_object("1");
                        }
                    }
                    _ => panic!(),
                },
            }
            assert!(
                c.compile_run(&run, "bad_affine_sign").is_err(),
                "{i} {change}"
            );
        }
    }
}
#[test]
fn sequence_extrema_affine_formulas_keep_positive_indices_and_original_operations() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for change in ["binder", "guard", "equation", "output", "operation"] {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            let index = if i % 5 == 0 { 4 } else { 5 };
            let scalar = b.arguments.last().unwrap().clone();
            let Fact::ForallFact(f) = &mut b.requirements[index] else {
                panic!()
            };
            match change {
                "binder" => {
                    f.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::N))
                }
                "guard" => f.dom_facts.push(Fact::AtomicFact(AtomicFact::InFact(
                    crate::ast::fact::InFact {
                        fact_id: FactId::new(999999),
                        element: scalar,
                        set: Obj::StandardSet(StandardSet::R),
                        line_file: None,
                    },
                ))),
                _ => {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                        &mut f.then_facts[0]
                    else {
                        panic!()
                    };
                    if change == "equation" {
                        std::mem::swap(&mut eq.left, &mut eq.right);
                    } else if change == "output" {
                        eq.left = super::number_object("0");
                    } else {
                        eq.right = super::number_object("0");
                    }
                }
            }
            assert!(
                c.compile_run(&run, "bad_affine_formula").is_err(),
                "{i} {change}"
            );
        }
    }
}
#[test]
fn sequence_extrema_sum_bounds_require_both_original_positive_absolute_bounds() {
    for i in [4, 9] {
        for which in [0, 1] {
            for change in ["carrier", "bound", "absolute", "proof", "store"] {
                let (mut run, c) = super::execute(SOURCES[i]);
                let p = invocation(&mut run);
                let index = 7 + 2 * which;
                match change {
                    "proof" => {
                        p.dom_proofs.remove(index + 1);
                    }
                    "store" => {
                        p.dom_stores.remove(index + 1);
                    }
                    "carrier" => {
                        let Fact::AtomicFact(AtomicFact::InFact(f)) =
                            &mut p.builtin.as_mut().unwrap().requirements[index]
                        else {
                            panic!()
                        };
                        f.set = Obj::StandardSet(StandardSet::R);
                    }
                    _ => {
                        let Fact::ForallFact(f) =
                            &mut p.builtin.as_mut().unwrap().requirements[index + 1]
                        else {
                            panic!()
                        };
                        let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(eq)) =
                            &mut f.then_facts[0]
                        else {
                            panic!()
                        };
                        if change == "bound" {
                            eq.right = super::number_object("0");
                        } else {
                            let Obj::ArithmeticOperator(ArithmeticOperator::Abs(a)) = &eq.left
                            else {
                                panic!()
                            };
                            eq.left = (*a.arg).clone();
                        }
                    }
                }
                assert!(
                    c.compile_run(&run, "bad_original_global_bound").is_err(),
                    "{i} {which} {change}"
                );
            }
        }
    }
}
#[test]
fn sequence_extrema_add_convergent_keeps_the_ordinary_limit_family() {
    for i in [3, 8] {
        let (mut run, c) = super::execute(SOURCES[i]);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(f)) = &b.requirements[4] else {
            panic!()
        };
        b.requirements[4] = Fact::AtomicFact(AtomicFact::NotHasSequenceLimitFact(
            crate::ast::fact::NotHasSequenceLimitFact {
                fact_id: f.fact_id,
                sequence: f.sequence.clone(),
                value: f.value.clone(),
                line_file: f.line_file.clone(),
            },
        ));
        assert!(c.compile_run(&run, "bad_ordinary_limit_polarity").is_err());
    }
}
#[test]
fn sequence_extrema_affine_conclusions_preserve_operation_polarity_and_order() {
    for (i, source) in SOURCES.into_iter().enumerate() {
        for change in ["polarity", "value", "operation"] {
            let (mut run, c) = super::execute(source);
            let b = invocation(&mut run).builtin.as_mut().unwrap();
            if change == "polarity" {
                let Fact::AtomicFact(g) = &b.conclusions[0] else {
                    panic!()
                };
                b.conclusions[0] =
                    Fact::AtomicFact(crate::ast::fact::negate_atomic_fact(g, g.fact_id()).unwrap());
            } else if i % 5 == 4 {
                let Fact::AtomicFact(AtomicFact::LessEqualFact(g)) = &mut b.conclusions[0] else {
                    panic!()
                };
                if change == "value" {
                    std::mem::swap(&mut g.left, &mut g.right);
                } else {
                    g.right = super::number_object("0");
                }
            } else {
                *value(&mut b.conclusions[0]) = if change == "value" {
                    b.arguments[2].clone()
                } else {
                    super::number_object("0")
                };
            }
            assert!(
                c.compile_run(&run, "bad_affine_conclusion").is_err(),
                "{i} {change}"
            );
        }
    }
}
#[test]
fn sequence_extrema_affine_call_owners_require_original_bound_and_candidate_evidence() {
    use crate::execute::execute_by_stmt::{ExecByStmtResult, ExecByThmStmtResult};
    for source in [
        include_str!("../../../lean/examples/sequence_limsup_add_convergent_call/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_sum_bound_call/statement.lit"),
    ] {
        let (mut run, c) = super::execute(source);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(p),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let ExecDefThmBodyProof::Forall(b) = &mut p.body else {
            panic!()
        };
        let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(p))) =
            &mut b.proof_steps[0]
        else {
            panic!("actual Call owner")
        };
        p.dom_proofs.pop();
        assert!(c.compile_run(&run, "bad_affine_call").is_err());
    }
}
#[test]
fn sequence_extrema_affine_closed_limit_values_require_the_original_real_formation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    for source in [
        include_str!("../../../lean/examples/sequence_limsup_add_convergent_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_add_convergent_closed/statement.lit"),
    ] {
        for candidate in [0, 1] {
            for carrier in [false, true] {
                let (mut run, c) = super::execute(source);
                let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                    ExecDefThmStmtResult::Success(p),
                )) = &mut run.statement_results[0]
                else {
                    panic!()
                };
                let ExecDefThmBodyProof::Forall(b) = &mut p.body else {
                    panic!()
                };
                let FactWellDefinedProof::AtomicExceptEquality(wd) =
                    &mut b.assumed_dom_facts[candidate].well_defined
                else {
                    panic!()
                };
                let PredicateDomainProof::SequenceLimit(p) =
                    &mut wd.as_detailed_mut().unwrap().predicate_domain
                else {
                    panic!("actual fresh sequence formation")
                };
                if carrier {
                    p.value_real.set = StandardSet::C;
                } else {
                    p.value_real.element = super::number_object("1");
                }
                assert!(
                    c.compile_run(&run, "bad_original_real_formation").is_err(),
                    "{candidate} {carrier}"
                );
            }
        }
    }
}
