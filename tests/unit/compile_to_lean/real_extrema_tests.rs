use crate::execute::execute_by_stmt::ExecReleaseThmStmtResult;
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::BoundOperatorObjWellDefinedProofByDef;
use crate::execute::ExecReleaseAndExpandStmtResult;
use crate::prelude::*;

const SUP: &str = r#"# Construct and select the supremum of the real singleton {2}.
by def $is_real_upper_bound({2},2)
witness exist bound R st {$is_real_upper_bound({2},bound)} from 2
by def $is_real_bounded_above({2})
release thm real_supremum_exists({2})
release thm real_supremum_selected({2})
sup({2}) $in R
"#;
const INF: &str = r#"# Construct and select the infimum of the real singleton {2}.
by def $is_real_lower_bound({2},2)
witness exist bound R st {$is_real_lower_bound({2},bound)} from 2
by def $is_real_bounded_below({2})
release thm real_infimum_exists({2})
release thm real_infimum_selected({2})
inf({2}) $in R
"#;

#[test]
fn real_extrema_reject_changed_theorem_stages() {
    for source in [SUP, INF] {
        for statement in [3, 4] {
            for mutation in 0..6 {
                let (mut run, compiler) = super::execute(source);
                let ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                    ExecReleaseThmStmtResult::Success(p),
                )) = &mut run.statement_results[statement]
                else {
                    panic!("release")
                };
                match mutation {
                    0 => {
                        p.dom_proofs.pop();
                    }
                    1 => p.dom_proofs.swap(0, 1),
                    2 => p.conclusions_wd.clear(),
                    3 => p.builtin.as_mut().unwrap().requirements.swap(0, 1),
                    4 => p.builtin.as_mut().unwrap().conclusions.clear(),
                    _ => {
                        p.builtin.as_mut().unwrap().arguments[0] = Obj::StandardSet(StandardSet::C)
                    }
                }
                assert!(
                    compiler.compile_run(&run, "changed_extremum").is_err(),
                    "stmt {statement} mutation {mutation}"
                );
            }
        }
    }
}

#[test]
fn real_extrema_reject_swapped_wd_carrier_and_selection() {
    for (op, cert) in [("sup", "least_upper"), ("inf", "greatest_lower")] {
        let source = format!(
            "forall A set, b R:\n    A $subset R\n    $is_real_{cert}_bound(A,b)\n    =>:\n        $is_set({op}(A))"
        );
        let (mut run, compiler) = super::execute(&source);
        compiler.compile_run(&run, "valid_selector_wd").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let proof = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::BoundOperator(p),
            ..
        } = (&mut proof
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .well_defined_of_each_parameter[0])
            .as_detailed_mut()
            .unwrap()
        else {
            panic!("selector WD")
        };
        match p {
            BoundOperatorObjWellDefinedProofByDef::Supremum(p) => {
                std::mem::swap(&mut p.real_set, &mut p.selection)
            }
            BoundOperatorObjWellDefinedProofByDef::Infimum(p) => {
                std::mem::swap(&mut p.real_set, &mut p.selection)
            }
        }
        assert!(compiler.compile_run(&run, "changed_selector_wd").is_err());
    }
}

#[test]
fn real_extrema_reject_empty_unbounded_and_nonreal_selection() {
    for source in [
        "sup({}) $in R",
        "inf({}) $in R",
        "sup(R) $in R",
        "inf(R) $in R",
        "sup({i}) $in R",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_extremum")
            .is_err());
    }
}

#[test]
fn powerset_projection_rejects_changed_derived_subject_and_id() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferInFactResult, InferResult, StoreFactResult,
    };
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute("forall B set, A power_set(B):\n    A $subset B");
        compiler.compile_run(&run, "powerset_projection").unwrap();
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let store = std::rc::Rc::get_mut(
            &mut all.introduced_params.defined_params.store_and_infer_results[1],
        )
        .expect("owned parameter result");
        let seed = store.primary_fact_id();
        let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &mut store.infer
        else {
            panic!("membership inference")
        };
        let InferInFactResult::PowerSet(p) = rules
            .iter_mut()
            .find(|r| matches!(r, InferInFactResult::PowerSet(_)))
            .unwrap()
        else {
            unreachable!()
        };
        let StoreFactResult::AtomicFact(stored) = &mut p.derived.store else {
            panic!("subset store")
        };
        if mutation == 0 {
            stored.fact_id = seed;
        } else {
            let AtomicFact::SubsetFact(f) = &mut stored.fact else {
                panic!("subset")
            };
            f.right = Obj::StandardSet(StandardSet::C);
        }
        assert!(compiler
            .compile_run(&run, "bad_powerset_projection")
            .is_err());
    }
}

const CERTIFICATE_IDS: &[&str] = &[
    "real_least_upper_bound_from_definition",
    "real_greatest_lower_bound_from_definition",
    "real_least_upper_bound_upper_bound",
    "real_greatest_lower_bound_lower_bound",
    "real_least_upper_bound_unique",
    "real_greatest_lower_bound_unique",
    "real_least_upper_bound_crosses",
    "real_greatest_lower_bound_crosses",
    "real_least_upper_bound_exists",
    "real_greatest_lower_bound_exists",
    "real_member_le_least_upper_bound",
    "real_greatest_lower_bound_le_member",
    "real_least_upper_bound_le_upper_bound",
    "real_lower_bound_le_greatest_lower_bound",
];

fn certificate_source(id: &str) -> String {
    std::fs::read_to_string(format!(
        "examples/stmt_nodes/release_and_expand/builtin_thm/{id}.lit"
    ))
    .unwrap()
}

#[test]
fn real_extrema_certificate_all_native_contracts_compile() {
    for id in CERTIFICATE_IDS {
        let source = certificate_source(id);
        let (run, compiler) = super::execute(&source);
        compiler
            .compile_run(&run, "certificate_contract")
            .unwrap_or_else(|e| panic!("{id}: {e:?}"));
    }
    for source in [
        r#"# Establish the supremum of {2}, identify any other candidate, and extract a crossing member.
by def $is_real_upper_bound({2},2)
release thm real_least_upper_bound_from_definition({2},2)
sup({2}) = 2
release thm real_least_upper_bound_upper_bound({2},2)
by def $is_real_upper_bound({2},3)
release thm real_least_upper_bound_exists({2},3)
obtain upper_candidate_witness from exist u R st {$is_real_least_upper_bound({2},u)}
release thm real_least_upper_bound_unique({2},upper_candidate_witness,2)
upper_candidate_witness = 2
release thm real_member_le_least_upper_bound({2},upper_candidate_witness,2)
release thm real_least_upper_bound_le_upper_bound({2},upper_candidate_witness,3)
release thm real_least_upper_bound_crosses({2},upper_candidate_witness,1)
obtain upper_crossing_witness from exist x {2} st {1 < x}
1 < upper_crossing_witness
upper_crossing_witness = 2

thm extremal_member_upper_bound:
    ? forall A set, b R, x A:
        A $subset R
        $is_real_least_upper_bound(A,b)
        =>:
            x <= b
    release thm real_member_le_least_upper_bound(A,b,x)

by thm extremal_member_upper_bound({2},upper_candidate_witness,2) => 2 <= upper_candidate_witness
"#,
        r#"# Establish the infimum of {2}, identify any other candidate, and extract a crossing member.
by def $is_real_lower_bound({2},2)
release thm real_greatest_lower_bound_from_definition({2},2)
inf({2}) = 2
release thm real_greatest_lower_bound_lower_bound({2},2)
by def $is_real_lower_bound({2},1)
release thm real_greatest_lower_bound_exists({2},1)
obtain lower_candidate_witness from exist u R st {$is_real_greatest_lower_bound({2},u)}
release thm real_greatest_lower_bound_unique({2},lower_candidate_witness,2)
lower_candidate_witness = 2
release thm real_greatest_lower_bound_le_member({2},lower_candidate_witness,2)
release thm real_lower_bound_le_greatest_lower_bound({2},lower_candidate_witness,1)
release thm real_greatest_lower_bound_crosses({2},lower_candidate_witness,3)
obtain lower_crossing_witness from exist x {2} st {x < 3}
lower_crossing_witness < 3
lower_crossing_witness = 2

thm extremal_member_lower_bound:
    ? forall A set, b R, x A:
        A $subset R
        $is_real_greatest_lower_bound(A,b)
        =>:
            b <= x
    release thm real_greatest_lower_bound_le_member(A,b,x)

by thm extremal_member_lower_bound({2},lower_candidate_witness,2) => lower_candidate_witness <= 2
"#,
    ] {
        let (run, compiler) = super::execute(source);
        compiler.compile_run(&run, "certificate_laws").unwrap();
    }
}

#[test]
fn real_extrema_certificate_rejects_changed_stage_evidence() {
    for id in CERTIFICATE_IDS {
        let source = certificate_source(id);
        for mutation in 0..5 {
            let (mut run, compiler) = super::execute(&source);
            let p = run
                .statement_results
                .iter_mut()
                .rev()
                .find_map(|stmt| match stmt {
                    ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                        ExecReleaseThmStmtResult::Success(p),
                    )) => Some(p),
                    _ => None,
                })
                .unwrap();
            match mutation {
                0 => p.dom_proofs.swap(0, 1),
                1 => p.conclusions_wd.clear(),
                2 => {
                    p.dom_stores.pop();
                }
                3 => p.builtin.as_mut().unwrap().arguments[1] = Obj::StandardSet(StandardSet::C),
                _ => p.builtin.as_mut().unwrap().requirements.swap(0, 1),
            }
            assert!(
                compiler
                    .compile_run(&run, "bad_certificate_stages")
                    .is_err(),
                "{id}: {mutation}"
            );
        }
    }
}

#[test]
fn real_extrema_certificate_rejects_changed_quantifier_contracts() {
    for id in CERTIFICATE_IDS {
        let source = certificate_source(id);
        let (mut run, compiler) = super::execute(&source);
        let p = run
            .statement_results
            .iter_mut()
            .rev()
            .find_map(|stmt| match stmt {
                ExecStmtResult::ReleaseAndExpand(ExecReleaseAndExpandStmtResult::Thm(
                    ExecReleaseThmStmtResult::Success(p),
                )) => Some(p),
                _ => None,
            })
            .unwrap();
        let builtin = p.builtin.as_mut().unwrap();
        let fact = if id.ends_with("from_definition") {
            &mut builtin.requirements[4]
        } else {
            &mut builtin.conclusions[0]
        };
        match fact {
            Fact::ForallFact(f) => {
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::C))
            }
            Fact::ExistFact(f) => {
                f.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::C))
            }
            Fact::AtomicFact(AtomicFact::EqualFact(f)) => {
                f.right = Obj::StandardSet(StandardSet::C)
            }
            Fact::AtomicFact(AtomicFact::LessEqualFact(f)) => {
                std::mem::swap(&mut f.left, &mut f.right)
            }
            _ => panic!("unexpected contract {id}"),
        }
        assert!(
            compiler.compile_run(&run, "bad_certificate_shape").is_err(),
            "{id}"
        );
    }
}
