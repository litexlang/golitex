use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
const SOURCES: [&str; 6] = [
    r#"# Both epsilon clauses are required for finite limsup.
thm checked_sequence_limsup_from_epsilon:
    ? forall a seq(R),L R:
        forall epsilon R+:
            exist n0 N+ st {{n N+:n>=n0} $subset preimage_set(a,{v R:v<L+epsilon})}
        forall epsilon R+,n0 N+:
            exist n N+ st {n>=n0 and L-epsilon<a(n)}
        =>:
            $has_seq_limsup(a,L)
    release thm seq_limsup_from_epsilon(a,L)
"#,
    r#"# The finite limsup candidate supplies a strict eventual epsilon bound.
thm checked_sequence_limsup_bound:
    ? forall a seq(R),L R,epsilon R+:
        $has_seq_limsup(a,L)
        =>:
            exist n0 N+ st {{n N+:n>=n0} $subset preimage_set(a,{v R:v<L+epsilon})}
    release thm seq_limsup_bound(a,L,epsilon)
"#,
    r#"# Every positive-index tail has a strict finite limsup epsilon hit.
thm checked_sequence_limsup_hit:
    ? forall a seq(R),L R,epsilon R+,n0 N+:
        $has_seq_limsup(a,L)
        =>:
            exist n N+ st {n>=n0 and L-epsilon<a(n)}
    release thm seq_limsup_hit(a,L,epsilon,n0)
"#,
    r#"# Both epsilon clauses are required for finite liminf.
thm checked_sequence_liminf_from_epsilon:
    ? forall a seq(R),L R:
        forall epsilon R+:
            exist n0 N+ st {{n N+:n>=n0} $subset preimage_set(a,{v R:L-epsilon<v})}
        forall epsilon R+,n0 N+:
            exist n N+ st {n>=n0 and a(n)<L+epsilon}
        =>:
            $has_seq_liminf(a,L)
    release thm seq_liminf_from_epsilon(a,L)
"#,
    r#"# The finite liminf candidate supplies a strict eventual epsilon bound.
thm checked_sequence_liminf_bound:
    ? forall a seq(R),L R,epsilon R+:
        $has_seq_liminf(a,L)
        =>:
            exist n0 N+ st {{n N+:n>=n0} $subset preimage_set(a,{v R:L-epsilon<v})}
    release thm seq_liminf_bound(a,L,epsilon)
"#,
    r#"# Every positive-index tail has a strict finite liminf epsilon hit.
thm checked_sequence_liminf_hit:
    ? forall a seq(R),L R,epsilon R+,n0 N+:
        $has_seq_liminf(a,L)
        =>:
            exist n N+ st {n>=n0 and a(n)<L+epsilon}
    release thm seq_liminf_hit(a,L,epsilon,n0)
"#,
];
#[test]
fn sequence_extrema_epsilon_replays_six_original_selected_schemas() {
    use crate::builtin_theorem::BuiltinTheoremId::*;
    for (i, (source, id)) in SOURCES
        .into_iter()
        .zip([
            SequenceLimsupFromEpsilon,
            SequenceLimsupBound,
            SequenceLimsupHit,
            SequenceLiminfFromEpsilon,
            SequenceLiminfBound,
            SequenceLiminfHit,
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
            .compile_run(&run, "extrema_epsilon")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        let law = [
            "sequenceExtremumOfForall",
            "sequenceExtremumBound",
            "sequenceExtremumHit",
        ][i % 3];
        assert!(out.contains(&format!("Litex.{law} {}", i < 3)));
        assert_eq!(out, c.compile_run(&run, "extrema_epsilon").unwrap());
    }
}
#[test]
fn sequence_extrema_epsilon_preserves_ordered_proofs_stores_wd_and_derivation() {
    for source in SOURCES {
        for change in [
            "proof",
            "store",
            "wd",
            "proof_order",
            "store_order",
            "args",
            "output",
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
                "output" => p.builtin.as_mut().unwrap().conclusions.clear(),
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
fn sequence_extrema_epsilon_introduction_requires_both_full_ordered_clauses() {
    for index in [0, 3] {
        for change in ["bound", "hits", "epsilon", "cutoff", "order"] {
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            let req = &mut p.builtin.as_mut().unwrap().requirements;
            match change {
                "bound" => {
                    let Fact::ForallFact(f) = &mut req[2] else {
                        panic!()
                    };
                    f.then_facts.clear();
                }
                "hits" => {
                    let Fact::ForallFact(f) = &mut req[3] else {
                        panic!()
                    };
                    f.then_facts.clear();
                }
                "epsilon" => {
                    let Fact::ForallFact(f) = &mut req[2] else {
                        panic!()
                    };
                    f.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::R));
                }
                "cutoff" => {
                    let Fact::ForallFact(f) = &mut req[3] else {
                        panic!()
                    };
                    f.typed_parameters.groups[1].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::N));
                }
                _ => req.swap(2, 3),
            }
            assert!(
                c.compile_run(&run, "bad_epsilon_clauses").is_err(),
                "{index} {change}"
            );
        }
    }
}
#[test]
fn sequence_extrema_bound_retains_exact_tail_preimage_and_strict_real_ray() {
    for index in [1, 4] {
        for change in [
            "tail_carrier",
            "cutoff",
            "ray_carrier",
            "endpoint",
            "function",
            "binder",
        ] {
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            let b = p.builtin.as_mut().unwrap();
            let zero = super::number_object("0");
            let Fact::ExistFact(f) = &mut b.conclusions[0] else {
                panic!()
            };
            if change == "binder" {
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::N));
            } else {
                let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(s)) = &mut f.facts[0]
                else {
                    panic!()
                };
                let Obj::SetFormer(SetFormer::SetBuilder(tail)) = &mut s.left else {
                    panic!()
                };
                let Obj::FunctionSpace(FunctionSpace::PreimageSet(preimage)) = &mut s.right else {
                    panic!()
                };
                let Obj::SetFormer(SetFormer::SetBuilder(ray)) = preimage.target_set.as_mut()
                else {
                    panic!()
                };
                match change {
                    "tail_carrier" => tail.param_set = Box::new(Obj::StandardSet(StandardSet::N)),
                    "cutoff" => {
                        let QuantifierFreeFact::AtomicFact(AtomicFact::GreaterEqualFact(g)) =
                            &mut tail.facts[0]
                        else {
                            panic!()
                        };
                        g.right = zero;
                    }
                    "ray_carrier" => ray.param_set = Box::new(Obj::StandardSet(StandardSet::C)),
                    "function" => preimage.function = Box::new(zero),
                    _ => {
                        let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(g)) =
                            &mut ray.facts[0]
                        else {
                            panic!()
                        };
                        if index == 1 {
                            g.right = zero;
                        } else {
                            g.left = zero;
                        }
                    }
                }
            }
            assert!(
                c.compile_run(&run, "bad_bound").is_err(),
                "{index} {change}"
            );
        }
    }
}
#[test]
fn sequence_extrema_hit_retains_positive_index_ordered_cutoff_and_strict_value() {
    for index in [2, 5] {
        for change in ["binder", "order", "missing", "cutoff", "value", "direction"] {
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            let Fact::ExistFact(f) = &mut p.builtin.as_mut().unwrap().conclusions[0] else {
                panic!()
            };
            let QuantifierFreeFact::AndFact(conj) = &mut f.facts[0] else {
                panic!()
            };
            match change {
                "binder" => {
                    f.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::N))
                }
                "order" => conj.facts.swap(0, 1),
                "missing" => {
                    conj.facts.pop();
                }
                "cutoff" => {
                    let AtomicFact::GreaterEqualFact(g) = &mut conj.facts[0] else {
                        panic!()
                    };
                    g.right = super::number_object("0");
                }
                _ => {
                    let AtomicFact::LessFact(g) = &mut conj.facts[1] else {
                        panic!()
                    };
                    if change == "direction" {
                        std::mem::swap(&mut g.left, &mut g.right);
                    } else if index == 2 {
                        g.left = super::number_object("0");
                    } else {
                        g.right = super::number_object("0");
                    }
                }
            }
            assert!(c.compile_run(&run, "bad_hit").is_err(), "{index} {change}");
        }
    }
}
#[test]
fn sequence_extrema_epsilon_requires_original_candidate_and_positive_controls() {
    for index in [1, 2, 4, 5] {
        for change in ["candidate", "epsilon", "cutoff"] {
            if change == "cutoff" && index % 3 != 2 {
                continue;
            }
            let (mut run, c) = super::execute(SOURCES[index]);
            let p = invocation(&mut run);
            let req = &mut p.builtin.as_mut().unwrap().requirements;
            if change == "candidate" {
                match &mut req[1] {
                    Fact::AtomicFact(AtomicFact::HasSequenceLimsupFact(f)) => {
                        f.value = super::number_object("0")
                    }
                    Fact::AtomicFact(AtomicFact::HasSequenceLiminfFact(f)) => {
                        f.value = super::number_object("0")
                    }
                    _ => panic!(),
                }
            } else {
                let i = if change == "epsilon" { 2 } else { 3 };
                let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut req[i] else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
            assert!(
                c.compile_run(&run, "bad_controls").is_err(),
                "{index} {change}"
            );
        }
    }
}
#[test]
fn sequence_extrema_epsilon_rejects_future_original_candidate_citations() {
    for index in [1, 2, 4, 5] {
        let (mut run, c) = super::execute(SOURCES[index]);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let child = super::atomic_proof_mut(&mut p.dom_proofs[1]);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
            &mut child.searched_proof
        else {
            panic!("actual known candidate proof")
        };
        cite.cite_fact_id = future;
        assert!(c.compile_run(&run, "future_candidate").is_err());
    }
}
