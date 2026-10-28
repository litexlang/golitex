use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};

const SETS: [&str; 8] = ["Q+", "Q-", "Z-", "R-", "Q*", "Z*", "R*", "C*"];

#[test]
fn signed_examples_replay_their_original_results() {
    for source in [
        include_str!("../../../lean/examples/signed_numeric_values/statement.lit"),
        include_str!("../../../lean/examples/signed_numeric_domains/statement.lit"),
        include_str!("../../../lean/examples/refined_numeric_membership/statement.lit"),
        include_str!("../../../lean/examples/signed_numeric_declarations/statement.lit"),
        include_str!("../../../lean/examples/signed_numeric_hierarchy/statement.lit"),
        include_str!("../../../lean/examples/signed_numeric_functions/statement.lit"),
        include_str!("../../../lean/examples/signed_numeric_identity_functions/statement.lit"),
        include_str!("../../../lean/examples/signed_numeric_subsets/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler.compile_run(&run, "signed_carriers").unwrap();
        assert!(
            output.contains("Litex.SetSemantics M") || output.contains("Litex.FunctionSemantics M")
        );
        assert_eq!(
            output,
            compiler.compile_run(&run, "signed_carriers").unwrap()
        );
    }
}

fn sign_mut(
    store: &mut StoreFactAndInferResult,
) -> &mut crate::store_fact_and_infer::InferInFactSignedStandardSetSignResult {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &mut store.infer
    else {
        panic!("membership stores")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferInFactResult::SignedStandardSetSign(sign) => Some(sign),
            _ => None,
        })
        .expect("recorded sign inference")
}

#[test]
fn signed_parameters_emit_every_original_inferred_fact_id() {
    for set in SETS {
        let (mut run, compiler) = super::execute(&format!("forall x {set}:\n    x / x = 1\n"));
        let body = super::forall_proof_mut(&mut run.statement_results[0]);
        let store = std::rc::Rc::get_mut(
            &mut body
                .introduced_params
                .defined_params
                .store_and_infer_results[0],
        )
        .unwrap();
        let ids: Vec<_> = sign_mut(store)
            .derived
            .iter()
            .map(|s| s.primary_fact_id())
            .collect();
        assert_eq!(ids.len(), if set.ends_with('*') { 1 } else { 3 });
        let output = compiler.compile_run(&run, "sign_ids").unwrap();
        for id in ids {
            assert!(
                output.contains(&format!("have h_{}", id.value())),
                "{set}: {id:?}"
            );
        }
        assert!(output.contains("_Host_i"));
    }
}

#[test]
fn signed_inference_rejects_missing_reordered_and_changed_stores() {
    for set in ["Q+", "Z-", "C*"] {
        for fault in 0..3 {
            let (mut run, compiler) = super::execute(&format!("forall x {set}:\n    x / x = 1\n"));
            let body = super::forall_proof_mut(&mut run.statement_results[0]);
            let store = std::rc::Rc::get_mut(
                &mut body
                    .introduced_params
                    .defined_params
                    .store_and_infer_results[0],
            )
            .unwrap();
            let sign = sign_mut(store);
            if fault == 0 {
                sign.derived.pop();
            } else if fault == 1 && sign.derived.len() > 1 {
                sign.derived.swap(0, 1);
            } else {
                let StoreFactResult::AtomicFact(store) = &mut sign.derived[0].store else {
                    panic!("atomic store")
                };
                match &mut store.fact {
                    AtomicFact::LessFact(f) => f.left = f.right.clone(),
                    AtomicFact::NotEqualFact(f) => f.left = f.right.clone(),
                    _ => panic!("sign fact"),
                }
            }
            assert!(
                compiler.compile_run(&run, "bad_sign").is_err(),
                "{set}: {fault}"
            );
        }
    }
}

#[test]
fn refinements_require_the_exact_ordered_source_children() {
    for (base, cond, target) in [
        ("Q", "0 < x", "Q+"),
        ("Z", "x < 0", "Z-"),
        ("C", "x != 0", "C*"),
    ] {
        for fault in 0..3 {
            let (mut run, compiler) = super::execute(&format!(
                "forall x {base}:\n    {cond}\n    =>:\n        x $in {target}\n"
            ));
            let body = super::forall_proof_mut(&mut run.statement_results[0]);
            let atomic = super::atomic_proof_mut(&mut body.proved_then_facts[0].verify_result);
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
                AtomicExceptEqualityFactSearchProofByBuiltinStrategy::RefinedNumericCarrier(p),
            ) = &mut atomic.searched_proof
            else {
                panic!("refinement route")
            };
            match fault {
                0 => {
                    p.proof_of_requirement_facts.pop();
                }
                1 => p.requirement_facts.swap(0, 1),
                _ => {
                    let AtomicFact::InFact(member) =
                        &mut super::atomic_proof_mut(&mut p.proof_of_requirement_facts[0]).fact
                    else {
                        panic!("base member")
                    };
                    member.set = Obj::StandardSet(StandardSet::N);
                }
            }
            assert!(compiler.compile_run(&run, "bad_refinement").is_err());
        }
    }
}

#[test]
fn closed_signed_membership_rejects_forged_scalar_and_carrier() {
    for source in ["1 / 2 $in Q+", "-2 $in Z-", "i $in C*"] {
        for change_set in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let atomic = super::atomic_proof_mut(
                &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
            );
            let AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
                ClosedAtomicExceptEqualityCalculationProof::In(
                    ClosedMembershipCalculationProof::StandardSet { value, set },
                ),
            ) = &mut atomic.searched_proof
            else {
                panic!("closed membership")
            };
            if change_set {
                *set = StandardSet::N;
            } else {
                *value = ClosedScalarValue::Decimal("0".into());
            }
            assert!(compiler.compile_run(&run, "bad_scalar").is_err());
        }
    }
}

#[test]
fn refined_domains_preserve_function_calls_and_return_observations() {
    for set in SETS {
        let source = format!("have fn identity(x {set}) {set} = x\nforall x {set}:\n    identity(x) + 0 = identity(x)\n");
        let (run, compiler) = super::execute(&source);
        let output = compiler.compile_run(&run, "refined_function").unwrap();
        assert!(output.contains("Litex.call"));
        assert!(output.contains("FunctionSignature.withGuard"));
    }
}

#[test]
fn signed_values_reject_zero_wrong_sign_and_wrong_carrier() {
    for source in [
        "0 $in Q+",
        "1 $in Z-",
        "0 $in R*",
        "0 $in C*",
        "-1 / 2 $in Z-",
        "i $in R*",
        "i $in Q+",
    ] {
        let command =
            parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
        let mut runtime =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        let run = runtime.run_litex_code(source).unwrap();
        assert!(!run.success, "{source}");
        assert!(super::LitexToLeanCompiler::new(runtime)
            .compile_run(&run, "invalid_signed")
            .is_err());
    }
}

#[test]
fn standard_subset_rejects_changed_recorded_endpoints() {
    for left in [true, false] {
        let (mut run, compiler) = super::execute("Q* $subset C*\n");
        let atomic = super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut run.statement_results[0]).verify_result,
        );
        let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(rule),
        ) = &mut atomic.searched_proof
        else {
            panic!("subset rule")
        };
        let crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::SubsetFactSearchProofByBuiltinRule::StandardSetSubset(p) = rule else { panic!("standard subset") };
        if left {
            p.left = StandardSet::C;
        } else {
            p.right = StandardSet::N;
        }
        assert!(compiler.compile_run(&run, "bad_subset").is_err());
    }
}
