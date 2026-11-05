use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::prelude::*;
const FROM: &str = r#"# A nonnegative Lipschitz estimate controls every pair on the complete domain.
thm checked_function_lipschitz_from_estimate:
    ? forall f fn(x R) R, K R:
        K>=0
        forall p cart(R,R):
            abs(f(p(1))-f(p(2)))<=K*abs(p(1)-p(2))
        =>:
            $is_lipschitz(f,K)
    release thm fn_lipschitz_from_estimate(f,K)
"#;
const UNIFORM: &str = r#"# A nonnegative Lipschitz estimate controls every pair on the complete domain.
thm checked_function_lipschitz_uniform:
    ? forall f fn(x R) R, K R:
        K>=0
        $is_lipschitz(f,K)
        =>:
            $is_uniformly_continuous(f)
    release thm fn_lipschitz_uniform(f,K)
"#;
#[test]
fn lipschitz_requires_all_original_stages_and_exact_subjects() {
    for source in [FROM, UNIFORM] {
        for change in ["proof", "store", "wd", "subject"] {
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
                    let Fact::AtomicFact(AtomicFact::FunctionLipschitzFact(f)) = f else {
                        panic!()
                    };
                    f.constant = super::number_object("-1");
                }
            }
            compiler
                .compile_run(&run, change)
                .expect_err("original stages and exact function/constant are required");
        }
    }
}
#[test]
fn lipschitz_estimate_retains_cartesian_domain_binder_coordinates_multiplier_and_closed_bound() {
    for change in [
        "domain",
        "cart_mismatch",
        "cart_arity",
        "capture",
        "multiplier",
        "image",
        "distance",
        "extra",
    ] {
        let (mut run, compiler) = super::execute(FROM);
        let p = invocation(&mut run);
        let args = &p.builtin.as_ref().unwrap().arguments;
        let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &args[1] else {
            panic!()
        };
        let constant_id = *id;
        let Fact::ForallFact(all) = &mut p.builtin.as_mut().unwrap().requirements[3] else {
            panic!()
        };
        match change {
            "domain" | "cart_mismatch" | "cart_arity" => {
                let ParamType::Obj(Obj::ProductShape(ProductShape::Cart(cart))) =
                    &mut all.typed_parameters.groups[0].param_type
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
            "capture" => all.typed_parameters.groups[0].params[0].id = constant_id,
            "extra" => all.then_facts.push(all.then_facts[0].clone()),
            _ => {
                let ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::LessEqualFact(bound)) =
                    &mut all.then_facts[0]
                else {
                    panic!()
                };
                if change == "image" {
                    bound.left = super::number_object("0");
                } else {
                    let Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) = &mut bound.right
                    else {
                        panic!()
                    };
                    if change == "multiplier" {
                        mul.left = Box::new(super::number_object("2"));
                    } else {
                        let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) =
                            mul.right.as_mut()
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
        compiler
            .compile_run(&run, change)
            .expect_err("exact original Cartesian estimate and fresh pair required");
    }
}
#[test]
fn lipschitz_original_assumption_formation_requires_real_and_nonnegative_constant() {
    for change in ["missing", "swapped", "carrier", "nonnegative"] {
        let (mut run, compiler) = super::execute(UNIFORM);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(named),
        )) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let ExecDefThmBodyProof::Forall(body) = &mut named.body else {
            panic!()
        };
        let FactWellDefinedProof::AtomicExceptEquality(wd) =
            &mut body.assumed_dom_facts.last_mut().unwrap().well_defined
        else {
            panic!()
        };
        let PredicateDomainProof::FunctionAnalysis(formation) =
            &mut wd.as_detailed_mut().unwrap().predicate_domain
        else {
            panic!("original assumption must retain formation")
        };
        match change {
            "missing" => {
                formation.requirements.pop();
            }
            "swapped" => formation.requirements.swap(0, 1),
            "carrier" => {
                let Fact::AtomicFact(AtomicFact::InFact(member)) =
                    &mut formation.requirements[0].requirement
                else {
                    panic!()
                };
                member.set = Obj::StandardSet(StandardSet::C);
            }
            _ => {
                let Fact::AtomicFact(AtomicFact::GreaterEqualFact(bound)) =
                    &mut formation.requirements[1].requirement
                else {
                    panic!()
                };
                bound.right = super::number_object("1");
            }
        }
        compiler.compile_run(&run, change).expect_err(
            "K in R and K>=0 are original WD evidence, even on repeated fact citations",
        );
    }
}
#[test]
fn lipschitz_known_formation_rejects_future_citation_and_changed_argument_equalities() {
    for change in ["future", "equalities"] {
        let (mut run, compiler) = super::execute(UNIFORM);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let success = super::atomic_proof_mut(&mut p.dom_proofs[3]);
        let PredicateDomainProof::ByKnownFact(cite) = &mut success
            .well_defined_proof
            .as_detailed_mut()
            .unwrap()
            .predicate_domain
        else {
            panic!()
        };
        if change == "future" {
            cite.cite_fact_id = future;
        } else {
            cite.why_parameters_of_known_fact_are_equal_to_givens.pop();
        }
        compiler
            .compile_run(&run, change)
            .expect_err("replay the original earlier formation and its complete equality evidence");
    }
}
#[test]
fn lipschitz_definition_inference_retains_original_source_and_one_clause() {
    use crate::store_fact_and_infer::{
        InferAtomicFactResult, InferFunctionLipschitzFactResult, InferResult,
    };
    for change in ["identity", "derived"] {
        let (mut run, compiler) = super::execute(UNIFORM);
        let p = invocation(&mut run);
        let future = p.builtin.as_ref().unwrap().conclusions[0].fact_id();
        let Some(InferResult::AtomicFact(InferAtomicFactResult::FunctionLipschitzFact(rules))) =
            &mut p.dom_stores[3].infer
        else {
            panic!()
        };
        let InferFunctionLipschitzFactResult::Definition(proof) = &mut rules[0];
        if change == "identity" {
            proof.source_fact_id = future;
        } else {
            proof.derived.clear();
        }
        compiler
            .compile_run(&run, change)
            .expect_err("original inference source and stored estimate are required");
    }
}
#[test]
fn lipschitz_negative_transport_rejects_another_constant_and_future_citation() {
    for change in ["constant", "future"] {
        let (mut run, compiler) = super::execute(
            r#"# Non-Lipschitzness transports along equal function objects and equal constants.
thm checked_function_lipschitz_negative_transport:
    ? forall f, g fn(x R) R, K, L R:
        K>=0
        L>=0
        f=g
        K=L
        not $is_lipschitz(f,K)
        =>:
            not $is_lipschitz(g,L)
    not $is_lipschitz(g,L)
"#,
        );
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
        if change == "constant" {
            let AtomicFact::NotFunctionLipschitzFact(f) = &mut p.fact else {
                panic!()
            };
            f.constant = super::number_object("1");
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
            .expect_err("exact function/constant identities and earlier citation required");
    }
}
