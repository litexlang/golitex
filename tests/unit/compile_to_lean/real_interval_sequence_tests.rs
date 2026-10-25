use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};

#[test]
fn real_interval_sequence_examples_replay_deterministically() {
    for (source, expected) in [
        (
            include_str!("../../../lean/examples/real_interval_endpoints/statement.lit"),
            "Litex.inRealInterval_iff",
        ),
        (
            include_str!("../../../lean/examples/real_ray_endpoints/statement.lit"),
            "Litex.inRealRay_iff",
        ),
        (
            include_str!("../../../lean/examples/real_interval_bounds/statement.lit"),
            "Litex.inRealInterval_iff",
        ),
        (
            include_str!("../../../lean/examples/real_interval_membership/statement.lit"),
            "Litex.inRealInterval_iff",
        ),
        (
            include_str!("../../../lean/examples/infinite_sequence_spaces/statement.lit"),
            "Litex.seqSet_eq_fnSet",
        ),
        (
            include_str!("../../../lean/examples/infinite_sequence_values/statement.lit"),
            "Litex.seqSignature",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "interval_sequence").unwrap();
        assert!(output.contains(expected), "{expected}");
        assert_eq!(
            output,
            compiler.compile_run(&run, "interval_sequence").unwrap()
        );
    }
}

#[test]
fn real_interval_wd_rejects_missing_swapped_or_foreign_evidence() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute("let interval = '[0, 2]\n");
        let SetFormerObjWellDefinedProofByDef::IntervalObj(p) = let_wd(&mut run) else {
            panic!()
        };
        match mutation {
            0 => p.child_obj_well_defined.clear(),
            1 => p.child_obj_well_defined.swap(0, 1),
            2 => p.requirement_fact_verified.clear(),
            3 => p.requirement_fact_verified.swap(0, 1),
            4 => {
                let AtomicFact::InFact(f) =
                    &mut super::atomic_proof_mut(&mut p.requirement_fact_verified[0]).fact
                else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::C);
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "bad_interval").is_err(),
            "{mutation}"
        );
    }
}

#[test]
fn real_ray_and_sequence_wd_reject_missing_children_or_requirements() {
    for source in ["let ray = '(0,)\n", "let sequences = seq(R)\n"] {
        for child in [false, true] {
            let (mut run, compiler) = super::execute(source);
            match let_wd(&mut run) {
                SetFormerObjWellDefinedProofByDef::OneSideInfinityIntervalObj(p) => {
                    if child {
                        p.child_obj_well_defined.clear();
                    } else {
                        p.requirement_fact_verified.clear();
                    }
                }
                SetFormerObjWellDefinedProofByDef::SeqSet(p) => {
                    if child {
                        p.child_obj_well_defined.clear();
                    } else {
                        p.requirement_fact_verified.clear();
                    }
                }
                _ => panic!(),
            }
            assert!(compiler
                .compile_run(&run, "missing_sequence_ray_wd")
                .is_err());
        }
    }
}

#[test]
fn real_interval_member_rejects_reordered_bounds() {
    let (mut run, compiler) = super::execute("1 $in '(0, 2)\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut run.statement_results[0] else {
        panic!()
    };
    let p = super::atomic_proof_mut(&mut p.verify_result);
    match &mut p.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                InFactSearchProofByBuiltinRule::IntervalMembership(p),
            ),
        ) => std::mem::swap(&mut p.lower_bound_proof, &mut p.upper_bound_proof),
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::IntervalMembership(p),
        ) => {
            p.proof_of_requirement_facts.swap(1, 2);
        }
        _ => panic!("original interval membership rule or strategy"),
    }
    assert!(compiler
        .compile_run(&run, "swapped_interval_bounds")
        .is_err());
}

#[test]
fn real_interval_inference_rejects_changed_bound_or_fact_id() {
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute("forall a, b R, x '(a, b]:\n    a < x\n");
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = p
            .introduced_params
            .defined_params
            .store_and_infer_results
            .iter_mut()
            .find_map(|s| {
                let s = std::rc::Rc::get_mut(s).unwrap();
                let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
                    &mut s.infer
                else {
                    return None;
                };
                rules.iter_mut().find_map(|r| match r {
                    InferInFactResult::RealInterval(p) => Some(p),
                    _ => None,
                })
            })
            .unwrap();
        if mutation == 0 {
            std::mem::swap(&mut p.lower_bound, &mut p.upper_bound);
        } else {
            let StoreFactResult::AtomicFact(stored) = &mut p.lower_bound.store else {
                panic!()
            };
            if mutation == 1 {
                stored.fact_id = FactId::new(u64::MAX);
            } else {
                let AtomicFact::LessFact(f) = &mut stored.fact else {
                    panic!()
                };
                std::mem::swap(&mut f.left, &mut f.right);
            }
        }
        assert!(compiler
            .compile_run(&run, "corrupt_interval_inference")
            .is_err());
    }
}

#[test]
fn infinite_sequence_expansion_keeps_original_id_and_rejects_corruption() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute("forall A set, s seq(A), n N+:\n    s(n) $in A\n");
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let p = p
            .introduced_params
            .defined_params
            .store_and_infer_results
            .iter_mut()
            .find_map(|s| {
                let s = std::rc::Rc::get_mut(s).unwrap();
                let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
                    &mut s.infer
                else {
                    return None;
                };
                rules.iter_mut().find_map(|r| match r {
                    InferInFactResult::SeqExpand(p) => Some(p),
                    _ => None,
                })
            })
            .unwrap();
        let id = p.derived.primary_fact_id();
        let StoreFactResult::AtomicFact(stored) = &mut p.derived.store else {
            panic!()
        };
        let AtomicFact::InFact(member) = &mut stored.fact else {
            panic!()
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &mut member.set else {
            panic!()
        };
        match mutation {
            0 => (),
            1 => member.element = Obj::StandardSet(StandardSet::R),
            2 => {
                signature.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::N))
            }
            3 => signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
            4 => stored.fact_id = FactId::new(u64::MAX),
            _ => unreachable!(),
        }
        let output = compiler.compile_run(&run, "sequence_inference");
        if mutation == 0 {
            let output = output.unwrap();
            assert!(output.contains(&format!(
                "let _object_h{} := (Litex.fnSet (Litex.seqSignature",
                id.value()
            )));
            assert!(output.contains(&format!("have h_{} : Litex.In", id.value())));
        } else {
            assert!(output.is_err(), "{mutation}");
        }
    }
}

#[test]
fn sequence_expansion_rejects_a_different_recorded_rule_family() {
    use crate::store_fact_and_infer::{
        InferInFactFiniteSeqExpandResult, InferInFactSeqExpandResult,
    };
    for source in [
        "forall A set, s seq(A), n N+:\n    s(n) $in A\n",
        include_str!("../../../lean/examples/finite_sequence_coordinates/statement.lit"),
    ] {
        let (mut run, compiler) = super::execute(source);
        let p = super::forall_proof_mut(&mut run.statement_results[0]);
        let mut changed = false;
        for store in &mut p.introduced_params.defined_params.store_and_infer_results {
            let store = std::rc::Rc::get_mut(store).unwrap();
            let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) =
                &mut store.infer
            else {
                continue;
            };
            let Some(index) = rules.iter().position(|rule| {
                matches!(
                    rule,
                    InferInFactResult::SeqExpand(_) | InferInFactResult::FiniteSeqExpand(_)
                )
            }) else {
                continue;
            };
            let replacement = match rules.remove(index) {
                InferInFactResult::SeqExpand(p) => {
                    InferInFactResult::FiniteSeqExpand(InferInFactFiniteSeqExpandResult {
                        derived: p.derived,
                    })
                }
                InferInFactResult::FiniteSeqExpand(p) => {
                    InferInFactResult::SeqExpand(InferInFactSeqExpandResult { derived: p.derived })
                }
                _ => unreachable!(),
            };
            rules.insert(index, replacement);
            changed = true;
            break;
        }
        assert!(changed);
        assert!(compiler.compile_run(&run, "wrong_sequence_rule").is_err());
    }
}

#[test]
fn real_interval_sequence_source_boundaries_remain_rejected() {
    for source in [
        "0 $in '(0, 2)",
        "$is_set('[i, 2])",
        "forall A set, s seq(A):\n    s(0) $in A",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime = Runtime::new(command);
        assert!(!runtime.run_litex_code(source).unwrap().success, "{source}");
    }
}

fn let_wd(run: &mut RunLitexCodeResult) -> &mut SetFormerObjWellDefinedProofByDef {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(p)),
    )) = &mut run.statement_results[0]
    else {
        panic!()
    };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetFormer(p),
        ..
    }) = &mut p.value_well_defined
    else {
        panic!()
    };
    p
}
