use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;

const FROM: &str =
    include_str!("../../../lean/examples/function_continuous_from_pointwise/statement.lit");
const POINT: &str =
    include_str!("../../../lean/examples/function_continuous_at_point/statement.lit");

#[test]
fn global_continuity_replays_both_schemas_definition_guarded_domains_and_negative_transport() {
    for source in [
        FROM,
        POINT,
        include_str!("../../../lean/examples/function_continuous_constant/statement.lit"),
        include_str!("../../../lean/examples/function_continuous_identity/statement.lit"),
        include_str!(
            "../../../lean/examples/function_continuous_guarded_from_pointwise/statement.lit"
        ),
        include_str!("../../../lean/examples/function_continuous_guarded_at_point/statement.lit"),
        include_str!("../../../lean/examples/function_continuous_definition/statement.lit"),
        include_str!("../../../lean/examples/function_continuous_negative_transport/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "global_continuity")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains("Litex.FunctionContinuous"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "global_continuity").unwrap()
        );
    }
}

#[test]
fn global_continuity_requires_original_stages_and_output_formation() {
    for source in [FROM, POINT] {
        for change in ["proof", "store", "output_wd", "property"] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "proof" => {
                    p.dom_proofs.pop();
                }
                "store" => {
                    p.dom_stores.pop();
                }
                "output_wd" => p.conclusions_wd.clear(),
                _ => {
                    let builtin = p.builtin.as_mut().unwrap();
                    let f = if source == FROM {
                        &mut builtin.conclusions[0]
                    } else {
                        &mut builtin.requirements[3]
                    };
                    let Fact::AtomicFact(AtomicFact::FunctionContinuousFact(f)) = f else {
                        panic!()
                    };
                    f.property = FunctionContinuityProperty::UniformContinuous;
                }
            }
            compiler.compile_run(&run, change).expect_err(
                "ordered original stages and the exact continuous property are required",
            );
        }
    }
}

#[test]
fn global_continuity_forall_keeps_actual_domain_binder_and_both_sided_body() {
    for change in ["domain", "side", "function", "capture"] {
        let (mut run, compiler) = super::execute(FROM);
        let Fact::ForallFact(all) =
            &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[3]
        else {
            panic!()
        };
        if change == "domain" {
            all.typed_parameters.groups[0].param_type =
                ParamType::Obj(Obj::StandardSet(StandardSet::RPos));
        } else {
            let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::FunctionContinuousAtFact(f)) =
                &mut all.then_facts[0]
            else {
                panic!()
            };
            if change == "side" {
                f.side = RealApproachSide::Left;
            } else if change == "function" {
                f.function = super::number_object("0");
            } else {
                f.function = f.point.clone();
            }
        }
        compiler.compile_run(&run, change).expect_err("complete original forall domain, capture-free binder and both-sided continuity are required");
    }
}

#[test]
fn global_continuity_replays_exact_inference_identity_and_derived_forall() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferFunctionContinuousFactResult, InferResult,
    };
    for change in ["identity", "derived"] {
        let (mut run, compiler) = super::execute(POINT);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let Some(InferResult::AtomicFact(InferAtomicFactResult::FunctionContinuousFact(rules))) =
            &mut p.dom_stores[3].infer
        else {
            panic!()
        };
        let InferFunctionContinuousFactResult::Definition(capture) = &mut rules[0];
        if change == "identity" {
            capture.source_fact_id = future;
        } else {
            capture.derived.clear();
        }
        compiler
            .compile_run(&run, change)
            .expect_err("original source ID and its one stored forall must remain unchanged");
    }
}

#[test]
fn global_continuity_negative_transport_rejects_another_property_and_future_citation() {
    for change in ["property", "future"] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/function_continuous_negative_transport/statement.lit"
        ));
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(named),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
            panic!()
        };
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &mut body.proof_steps[0]
        else {
            panic!()
        };
        let p = super::atomic_proof_mut(&mut statement.verify_result);
        if change == "property" {
            let AtomicFact::NotFunctionContinuousFact(f) = &mut p.fact else {
                panic!()
            };
            f.property = FunctionContinuityProperty::UniformContinuous;
        } else {
            let future = p.fact.fact_id();
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                &mut p.searched_proof
            else {
                panic!()
            };
            cite.cite_fact_id = future;
        }
        compiler.compile_run(&run, change).expect_err(
            "transport retains the exact property and an earlier original source citation",
        );
    }
}

#[test]
fn global_continuity_formulas_retain_original_context_carrier_and_complete_equation() {
    for (source, constant) in [
        (
            include_str!("../../../lean/examples/function_continuous_constant/statement.lit"),
            true,
        ),
        (
            include_str!("../../../lean/examples/function_continuous_identity/statement.lit"),
            false,
        ),
    ] {
        for change in ["formula", "domain", "output_wd", "store"] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            if change == "output_wd" {
                p.conclusions_wd.clear();
            } else if change == "store" {
                p.dom_stores.pop();
            } else {
                let Fact::ForallFact(all) =
                    p.builtin.as_mut().unwrap().requirements.last_mut().unwrap()
                else {
                    panic!()
                };
                if change == "domain" {
                    all.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::RPos));
                } else {
                    let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(eq)) =
                        &mut all.then_facts[0]
                    else {
                        panic!()
                    };
                    eq.right = super::number_object("42");
                }
            }
            compiler
                .compile_run(&run, change)
                .expect_err("retain source formula, actual domain and original stages");
        }
        if constant {
            let (mut run, compiler) = super::execute(source);
            let Fact::AtomicFact(AtomicFact::InFact(m)) =
                &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[3]
            else {
                panic!()
            };
            m.set = Obj::StandardSet(StandardSet::C);
            compiler
                .compile_run(&run, "complex_constant")
                .expect_err("constant's real membership is an original requirement");
        }
    }
}
