use super::dense_order_theorem_tests::invocation;
use crate::prelude::*;
const FROM: &str =
    include_str!("../../../lean/examples/function_uniform_from_epsilon/statement.lit");
const CONTROL: &str = include_str!("../../../lean/examples/function_uniform_control/statement.lit");
const CONTINUOUS: &str =
    include_str!("../../../lean/examples/function_uniform_continuous/statement.lit");

#[test]
fn uniform_continuity_replays_schemas_definition_inferences_and_negative_transport() {
    for source in [
        FROM,
        CONTROL,
        CONTINUOUS,
        include_str!("../../../lean/examples/function_uniform_definition/statement.lit"),
        include_str!("../../../lean/examples/function_uniform_positive_from_epsilon/statement.lit"),
        include_str!("../../../lean/examples/function_uniform_positive_control/statement.lit"),
        include_str!("../../../lean/examples/function_uniform_guarded_continuous/statement.lit"),
        include_str!("../../../lean/examples/function_uniform_negative_transport/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "uniform_continuity")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains("Litex.FunctionUniformContinuous"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "uniform_continuity").unwrap()
        );
    }
}
#[test]
fn uniform_continuity_requires_all_original_stages() {
    for source in [FROM, CONTROL, CONTINUOUS] {
        for change in ["proof", "store", "wd", "property"] {
            let (mut run, compiler) = super::execute(source);
            let p = invocation(&mut run);
            match change {
                "proof" => {
                    p.dom_proofs.pop();
                }
                "store" => {
                    p.dom_stores.pop();
                }
                "wd" => p.conclusions_wd.clear(),
                _ => {
                    let b = p.builtin.as_mut().unwrap();
                    let f = if source == FROM {
                        &mut b.conclusions[0]
                    } else {
                        &mut b.requirements[3]
                    };
                    let Fact::AtomicFact(AtomicFact::FunctionContinuousFact(f)) = f else {
                        panic!()
                    };
                    f.property = FunctionContinuityProperty::Continuous;
                }
            }
            compiler
                .compile_run(&run, change)
                .expect_err("preserve every original stage and exact property");
        }
    }
}
fn control_clause(run: &mut RunLitexCodeResult) -> &mut PlainExistFact {
    let Fact::ForallFact(all) = &mut invocation(run).builtin.as_mut().unwrap().requirements[3]
    else {
        panic!()
    };
    let ExistOrAndChainAtomicFact::ExistFact(exists) = &mut all.then_facts[0] else {
        panic!()
    };
    exists
}
fn pair_builder(exists: &mut PlainExistFact, image: bool) -> &mut SetBuilder {
    let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(inclusion)) = &mut exists.facts[0]
    else {
        panic!()
    };
    let obj = if image {
        &mut inclusion.right
    } else {
        &mut inclusion.left
    };
    let Obj::SetFormer(SetFormer::SetBuilder(builder)) = obj else {
        panic!()
    };
    builder
}
#[test]
fn uniform_continuity_validates_binders_cartesian_domains_and_exact_distances() {
    for change in [
        "epsilon_carrier",
        "delta_carrier",
        "cart_arity",
        "cart_mismatch",
        "domain",
        "capture",
        "radius",
        "distance",
        "image_distance",
        "extra_clause",
    ] {
        let (mut run, compiler) = super::execute(FROM);
        if change == "epsilon_carrier" {
            let Fact::ForallFact(all) =
                &mut invocation(&mut run).builtin.as_mut().unwrap().requirements[3]
            else {
                panic!()
            };
            all.typed_parameters.groups[0].param_type =
                ParamType::Obj(Obj::StandardSet(StandardSet::R));
        } else {
            let exists = control_clause(&mut run);
            if change == "delta_carrier" {
                exists.typed_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R));
            } else {
                let delta = exists.typed_parameters.groups[0].params[0].id;
                let b = pair_builder(exists, change == "image_distance" || change == "domain");
                match change {
                    "capture" => b.param_binding.id = delta,
                    "cart_arity" | "cart_mismatch" | "domain" => {
                        let Obj::ProductShape(ProductShape::Cart(cart)) = b.param_set.as_mut()
                        else {
                            panic!()
                        };
                        if change == "cart_arity" {
                            cart.args.pop();
                        } else {
                            cart.args[0] = Box::new(Obj::StandardSet(StandardSet::RPos));
                            if change == "domain" {
                                cart.args[1] = cart.args[0].clone();
                            }
                        }
                    }
                    "extra_clause" => b.facts.push(b.facts[0].clone()),
                    _ => {
                        let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(close)) =
                            &mut b.facts[0]
                        else {
                            panic!()
                        };
                        if change == "radius" {
                            close.right = super::number_object("1");
                        } else {
                            let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) =
                                &mut close.left
                            else {
                                panic!()
                            };
                            let Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) =
                                abs.arg.as_mut()
                            else {
                                panic!()
                            };
                            std::mem::swap(&mut sub.left, &mut sub.right);
                        }
                    }
                }
            }
        }
        compiler
            .compile_run(&run, change)
            .expect_err("exact strict pair control and capture-free binders required");
    }
}
#[test]
fn uniform_continuity_inference_retains_source_and_one_original_clause() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferFunctionContinuousFactResult, InferResult,
    };
    for change in ["identity", "derived"] {
        let (mut run, compiler) = super::execute(CONTROL);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let Some(InferResult::AtomicFact(InferAtomicFactResult::FunctionContinuousFact(rules))) =
            &mut p.dom_stores[3].infer
        else {
            panic!()
        };
        let InferFunctionContinuousFactResult::Definition(proof) = &mut rules[0];
        if change == "identity" {
            proof.source_fact_id = future;
        } else {
            proof.derived.clear();
        }
        compiler
            .compile_run(&run, change)
            .expect_err("source identity and exact stored defining clause required");
    }
}
#[test]
fn uniform_continuity_negative_transport_rejects_continuity_and_future_citations() {
    for change in ["property", "future"] {
        let (mut run, compiler) = super::execute(include_str!(
            "../../../lean/examples/function_uniform_negative_transport/statement.lit"
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
            f.property = FunctionContinuityProperty::Continuous;
        } else {
            let future = p.fact.fact_id();
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                &mut p.searched_proof
            else {
                panic!()
            };
            cite.cite_fact_id = future;
        }
        compiler
            .compile_run(&run, change)
            .expect_err("negative transport preserves exact property and earlier citation");
    }
}
