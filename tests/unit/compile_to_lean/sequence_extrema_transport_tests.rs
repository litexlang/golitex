use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
const SOURCES: [&str; 10] = [
    include_str!("../../../lean/examples/sequence_limsup_compare/statement.lit"),
    include_str!("../../../lean/examples/sequence_limsup_eventually_equal/statement.lit"),
    include_str!("../../../lean/examples/sequence_limsup_shift/statement.lit"),
    include_str!("../../../lean/examples/sequence_limsup_neg/statement.lit"),
    include_str!("../../../lean/examples/sequence_liminf_compare/statement.lit"),
    include_str!("../../../lean/examples/sequence_liminf_eventually_equal/statement.lit"),
    include_str!("../../../lean/examples/sequence_liminf_shift/statement.lit"),
    include_str!("../../../lean/examples/sequence_liminf_neg/statement.lit"),
    include_str!("../../../lean/examples/sequence_limit_from_extrema/statement.lit"),
    include_str!("../../../lean/examples/sequence_extrema_order/statement.lit"),
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
fn sequence_extrema_transport_replays_ten_actual_selected_schemas_deterministically() {
    use crate::builtin_theorem::BuiltinTheoremId::*;
    for (i, (source, id)) in SOURCES
        .into_iter()
        .zip([
            SequenceLimsupCompare,
            SequenceLimsupEventuallyEqual,
            SequenceLimsupShift,
            SequenceLimsupNeg,
            SequenceLiminfCompare,
            SequenceLiminfEventuallyEqual,
            SequenceLiminfShift,
            SequenceLiminfNeg,
            SequenceLimitFromExtrema,
            SequenceExtremaOrder,
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
        let out = c
            .compile_run(&run, "extrema_transport")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        let law = if i < 8 {
            [
                "sequenceExtremumCompare",
                "sequenceExtremumEventuallyEqual",
                "sequenceExtremumShift",
                "sequenceExtremumNeg",
            ][i % 4]
        } else if i == 8 {
            "sequenceLimitFromExtrema"
        } else {
            "sequenceExtremaOrder"
        };
        assert!(out.contains(&format!("Litex.{law}")));
        if i < 8 {
            assert!(out.contains(&format!("Litex.{law} {}", i < 4)));
        }
        assert_eq!(out, c.compile_run(&run, "extrema_transport").unwrap());
    }
}
#[test]
fn sequence_extrema_transport_preserves_zero_alias_literal_and_call_owners() {
    for source in [
        include_str!("../../../lean/examples/sequence_limsup_neg_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_neg_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_limsup_shift_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_shift_closed/statement.lit"),
        include_str!(
            "../../../lean/examples/sequence_limsup_eventually_equal_aliased/statement.lit"
        ),
        include_str!(
            "../../../lean/examples/sequence_liminf_eventually_equal_aliased/statement.lit"
        ),
        include_str!("../../../lean/examples/sequence_limsup_neg_aliased/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_neg_aliased/statement.lit"),
        include_str!("../../../lean/examples/sequence_limsup_neg_literal/statement.lit"),
        include_str!("../../../lean/examples/sequence_limsup_neg_call/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_compare_call/statement.lit"),
        include_str!("../../../lean/examples/sequence_limit_from_extrema_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_extrema_order_closed/statement.lit"),
    ] {
        let (run, c) = super::execute(source);
        c.compile_run(&run, "transport_variants")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
    }
}
#[test]
fn sequence_extrema_transport_requires_original_stages_stores_wd_and_identity() {
    for source in SOURCES {
        for change in [
            "proof",
            "store",
            "wd",
            "proof_order",
            "store_order",
            "args",
            "result",
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
                "result" => p.builtin.as_mut().unwrap().conclusions.clear(),
                _ => {
                    p.theorem_derivation =
                        crate::execute::execute_by_stmt::TheoremDerivationProof::UserTheorem
                }
            }
            assert!(c.compile_run(&run, "bad_stages").is_err(), "{change}");
        }
    }
}
#[test]
fn sequence_extrema_transport_retains_both_exact_unguarded_sequence_domains() {
    for index in 0..8 {
        for seq_index in [0, 1] {
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            let Fact::AtomicFact(AtomicFact::InFact(f)) =
                &mut p.builtin.as_mut().unwrap().requirements[seq_index]
            else {
                panic!()
            };
            let Obj::FunctionSpace(FunctionSpace::FnSet(s)) = &mut f.set else {
                panic!()
            };
            s.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
            assert!(
                c.compile_run(&run, "bad_domain").is_err(),
                "{index} {seq_index}"
            );
        }
    }
}
#[test]
fn sequence_extrema_transport_requires_original_candidate_values_and_visible_citations() {
    for index in 0..8 {
        for future in [false, true] {
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            if future {
                let id = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
                let child = super::atomic_proof_mut(&mut p.dom_proofs[2]);
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut child.searched_proof
                else {
                    panic!("actual known candidate")
                };
                cite.cite_fact_id = id;
            } else {
                *value(&mut p.builtin.as_mut().unwrap().requirements[2]) =
                    super::number_object("0");
            }
            assert!(
                c.compile_run(&run, "bad_candidate").is_err(),
                "{index} {future}"
            );
        }
    }
}
#[test]
fn sequence_extrema_tail_schemas_keep_positive_cutoff_and_oriented_guard() {
    for index in [0, 1, 4, 5] {
        for change in ["carrier", "guard", "direction", "index"] {
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            let req = &mut p.builtin.as_mut().unwrap().requirements;
            let cutoff = if index % 4 == 0 { 4 } else { 3 };
            let formula = cutoff + 1;
            if change == "carrier" {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut req[cutoff] else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::N);
            } else {
                let Fact::ForallFact(f) = &mut req[formula] else {
                    panic!()
                };
                match change {
                    "guard" => f.dom_facts.clear(),
                    "index" => {
                        f.typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::N))
                    }
                    _ => {
                        let Fact::AtomicFact(AtomicFact::GreaterEqualFact(g)) = &mut f.dom_facts[0]
                        else {
                            panic!()
                        };
                        std::mem::swap(&mut g.left, &mut g.right);
                    }
                }
            }
            assert!(c.compile_run(&run, "bad_tail").is_err(), "{index} {change}");
        }
    }
}
#[test]
fn sequence_extrema_formulas_keep_exact_ordered_calls_and_operations() {
    for index in 0..8 {
        let (mut run, c) = super::execute(SOURCES[index]);
        let p = invocation(&mut run);
        let b = p.builtin.as_mut().unwrap();
        let Fact::ForallFact(f) = b.requirements.last_mut().unwrap() else {
            panic!()
        };
        match &mut f.then_facts[0] {
            ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(g)) => {
                std::mem::swap(&mut g.left, &mut g.right)
            }
            ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(g)) => {
                g.right = super::number_object("0")
            }
            _ => panic!(),
        }
        assert!(c.compile_run(&run, "bad_formula").is_err(), "{index}");
    }
}
#[test]
fn sequence_extrema_shifts_keep_natural_offset_and_unshifted_output_index() {
    for index in [2, 6] {
        for change in ["carrier", "offset", "order", "guard"] {
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            let req = &mut p.builtin.as_mut().unwrap().requirements;
            if change == "carrier" {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut req[3] else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::Z);
            } else {
                let Fact::ForallFact(f) = &mut req[4] else {
                    panic!()
                };
                if change == "guard" {
                    f.dom_facts
                        .push(Fact::AtomicFact(AtomicFact::InFact(InFact {
                            fact_id: FactId::new(u64::MAX),
                            element: super::number_object("0"),
                            set: Obj::StandardSet(StandardSet::R),
                            line_file: None,
                        })));
                } else {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(g)) =
                        &mut f.then_facts[0]
                    else {
                        panic!()
                    };
                    let Obj::FnObj(call) = &mut g.right else {
                        panic!()
                    };
                    let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) =
                        call.body[0][0].as_mut()
                    else {
                        panic!()
                    };
                    if change == "offset" {
                        sum.right = Box::new(super::number_object("1"));
                    } else {
                        std::mem::swap(&mut sum.left, &mut sum.right);
                    }
                }
            }
            assert!(
                c.compile_run(&run, "bad_shift").is_err(),
                "{index} {change}"
            );
        }
    }
}
#[test]
fn sequence_extrema_negation_retains_fixed_scalar_opposite_positive_target_and_value() {
    for index in [3, 7] {
        for change in ["scalar", "value", "polarity"] {
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            let b = p.builtin.as_mut().unwrap();
            match change {
                "scalar" => {
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[3] else {
                        panic!()
                    };
                    let Obj::ArithmeticOperator(ArithmeticOperator::Neg(x)) = &mut f.element else {
                        panic!()
                    };
                    x.arg = Box::new(super::number_object("2"));
                }
                "value" => *value(&mut b.conclusions[0]) = b.arguments[2].clone(),
                _ => {
                    let Fact::AtomicFact(g) = &b.conclusions[0] else {
                        panic!()
                    };
                    b.conclusions[0] = Fact::AtomicFact(
                        crate::ast::fact::negate_atomic_fact(g, g.fact_id()).unwrap(),
                    );
                }
            }
            assert!(
                c.compile_run(&run, "bad_negation").is_err(),
                "{index} {change}"
            );
        }
    }
}
#[test]
fn sequence_extrema_cross_links_require_coincident_values_and_distinct_original_sides() {
    for index in [8, 9] {
        for change in ["value", "order", "result"] {
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            let b = p.builtin.as_mut().unwrap();
            match change {
                "value" => *value(&mut b.requirements[2]) = super::number_object("0"),
                "order" => b.requirements.swap(1, 2),
                _ => b.conclusions[0] = b.requirements[1].clone(),
            }
            assert!(
                c.compile_run(&run, "bad_cross_link").is_err(),
                "{index} {change}"
            );
        }
    }
}
#[test]
fn sequence_extrema_call_owners_cannot_drop_original_verifications() {
    use crate::execute::execute_by_stmt::{ExecByStmtResult, ExecByThmStmtResult};
    for source in [
        include_str!("../../../lean/examples/sequence_limsup_neg_call/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_compare_call/statement.lit"),
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
        assert!(c.compile_run(&run, "bad_call").is_err());
    }
}

#[test]
fn sequence_extrema_closed_values_require_the_original_real_formation() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    for source in [
        include_str!("../../../lean/examples/sequence_limsup_neg_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_liminf_neg_closed/statement.lit"),
        include_str!("../../../lean/examples/sequence_limit_from_extrema_closed/statement.lit"),
    ] {
        for carrier in [false, true] {
            let (mut run, c) = super::execute(source);
            let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                ExecDefThmStmtResult::Success(p),
            )) = &mut run.statement_results[0]
            else {
                panic!()
            };
            let ExecDefThmBodyProof::Forall(body) = &mut p.body else {
                panic!()
            };
            let FactWellDefinedProof::AtomicExceptEquality(wd) =
                &mut body.assumed_dom_facts[0].well_defined
            else {
                panic!()
            };
            let PredicateDomainProof::SequenceLimit(p) =
                &mut wd.as_detailed_mut().unwrap().predicate_domain
            else {
                panic!("actual fresh extremum formation")
            };
            if carrier {
                p.value_real.set = StandardSet::C;
            } else {
                p.value_real.element = super::number_object("1");
            }
            assert!(c.compile_run(&run, "bad_closed_value_formation").is_err());
        }
    }
}
