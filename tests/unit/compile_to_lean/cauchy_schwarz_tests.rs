use super::dense_order_theorem_tests::invocation;
use crate::execute::execute_by_stmt::BuiltinThmApplication;
use crate::prelude::*;

const SOURCE: &str =
    include_str!("../../../lean/examples/inner_product_cauchy_schwarz/statement.lit");
fn goal(b: &mut BuiltinThmApplication) -> &mut LessEqualFact {
    let Fact::AtomicFact(AtomicFact::LessEqualFact(f)) = &mut b.conclusions[0] else {
        panic!()
    };
    f
}

#[test]
fn cauchy_schwarz_replays_complex_real_empty_one_and_original_zero_formula() {
    for source in [
        SOURCE,
        include_str!("../../../lean/examples/inner_product_cauchy_schwarz_real/statement.lit"),
        include_str!("../../../lean/examples/inner_product_cauchy_schwarz_empty/statement.lit"),
        include_str!("../../../lean/examples/inner_product_cauchy_schwarz_one/statement.lit"),
        include_str!(
            "../../../lean/examples/inner_product_cauchy_schwarz_zero_formula/statement.lit"
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let output = compiler
            .compile_run(&run, "cauchy_schwarz")
            .unwrap_or_else(|e| panic!("{source}: {e}"));
        assert!(output.contains("Litex.finiteInnerProductCauchySchwarz"));
        assert_eq!(
            output,
            compiler.compile_run(&run, "cauchy_schwarz").unwrap()
        );
    }
}

#[test]
fn cauchy_schwarz_retains_four_ordered_premises_stores_and_conclusion_wd() {
    for change in [
        "proof",
        "store",
        "repeat",
        "conclusion",
        "wd",
        "proof_order",
        "store_order",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        assert_eq!(call.dom_proofs.len(), 4);
        match change {
            "proof" => {
                call.dom_proofs.pop();
            }
            "store" => {
                call.dom_stores.pop();
            }
            "repeat" => {
                call.builtin.as_mut().unwrap().requirements.remove(2);
            }
            "conclusion" => call.builtin.as_mut().unwrap().conclusions.clear(),
            "wd" => call.conclusions_wd.clear(),
            "proof_order" => call.dom_proofs.swap(1, 3),
            _ => call.dom_stores.swap(0, 2),
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_cauchy_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn cauchy_schwarz_retains_both_naturals_and_exact_complex_vector_memberships() {
    for change in [
        "natural0",
        "natural2",
        "carrier",
        "dimension",
        "subject",
        "fact_id",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let b = invocation(&mut run).builtin.as_mut().unwrap();
        let idx = match change {
            "natural0" => 0,
            "natural2" => 2,
            _ => 1,
        };
        let Fact::AtomicFact(AtomicFact::InFact(f)) = &mut b.requirements[idx] else {
            panic!()
        };
        match change {
            "natural0" | "natural2" => f.set = Obj::StandardSet(StandardSet::Z),
            "subject" => f.element = super::number_object("0"),
            "fact_id" => f.fact_id = FactId::new(u64::MAX),
            _ => {
                let Obj::SetFormer(SetFormer::FiniteSeqSet(s)) = &mut f.set else {
                    panic!()
                };
                if change == "carrier" {
                    s.set = Box::new(Obj::StandardSet(StandardSet::R));
                } else {
                    s.n = Box::new(super::number_object("99"));
                }
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_cauchy_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn cauchy_schwarz_retains_modulus_original_inner_product_order_and_dimension() {
    for change in ["modulus", "inner", "left", "right", "dimension", "order"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let f = goal(invocation(&mut run).builtin.as_mut().unwrap());
        if change == "modulus" {
            f.left = super::number_object("0");
        } else {
            let Obj::ComplexOperator(ComplexOperator::ComplexAbs(m)) = &mut f.left else {
                panic!()
            };
            if change == "inner" {
                m.arg = Box::new(super::number_object("0"));
            } else {
                let Obj::MatrixOperator(MatrixOperator::InnerProduct(p)) = m.arg.as_mut() else {
                    panic!()
                };
                match change {
                    "left" => p.left = Box::new(super::number_object("0")),
                    "right" => p.right = Box::new(super::number_object("0")),
                    "dimension" => p.dimension = Box::new(super::number_object("99")),
                    _ => std::mem::swap(&mut p.left, &mut p.right),
                }
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_cauchy_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn cauchy_schwarz_retains_orientation_and_ordered_norm_product() {
    for change in [
        "orientation",
        "product",
        "order",
        "left_vector",
        "right_vector",
        "left_dimension",
        "right_dimension",
    ] {
        let (mut run, compiler) = super::execute(SOURCE);
        let f = goal(invocation(&mut run).builtin.as_mut().unwrap());
        if change == "orientation" {
            std::mem::swap(&mut f.left, &mut f.right);
        } else if change == "product" {
            f.right = super::number_object("0");
        } else {
            let Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) = &mut f.right else {
                panic!()
            };
            if change == "order" {
                std::mem::swap(&mut p.left, &mut p.right);
            } else {
                let child = if change.starts_with("left") {
                    &mut p.left
                } else {
                    &mut p.right
                };
                let Obj::MatrixOperator(MatrixOperator::EuclideanNorm(n)) = child.as_mut() else {
                    panic!()
                };
                if change.ends_with("vector") {
                    n.vector = Box::new(super::number_object("0"));
                } else {
                    n.dimension = Box::new(super::number_object("99"));
                }
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_cauchy_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn cauchy_schwarz_retains_inequality_constructor_wd_and_subjects() {
    for change in ["missing", "order", "left", "right"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        let FactWellDefinedProof::AtomicExceptEquality(wd) = &mut call.conclusions_wd[0] else {
            panic!()
        };
        let d = wd.as_detailed_mut().unwrap();
        match change {
            "missing" => {
                d.well_defined_of_each_parameter.pop();
            }
            "order" => d.well_defined_of_each_parameter.swap(0, 1),
            _ => {
                let i = if change == "left" { 0 } else { 1 };
                let DetailedObjWellDefinedProof::ByDef { obj, .. } = d
                    .well_defined_of_each_parameter[i]
                    .as_detailed_mut()
                    .unwrap()
                else {
                    panic!()
                };
                *obj = super::number_object("0");
            }
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_cauchy_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn cauchy_schwarz_requires_original_native_rule_derivation_and_arguments() {
    use crate::execute::execute_by_stmt::TheoremDerivationProof;
    for change in ["rule", "derivation", "arguments"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let call = invocation(&mut run);
        match change {
            "rule" => {
                call.builtin.as_mut().unwrap().theorem =
                    crate::builtin_theorem::BuiltinTheoremId::EuclideanNormTriangle
            }
            "derivation" => call.theorem_derivation = TheoremDerivationProof::UserTheorem,
            _ => call.builtin.as_mut().unwrap().arguments.swap(0, 1),
        }
        assert!(
            compiler
                .compile_run(&run, &format!("bad_cauchy_{change}"))
                .is_err(),
            "{change}"
        );
    }
}

#[test]
fn cauchy_schwarz_rejects_future_conclusion_as_original_vector_evidence() {
    let (mut run, compiler) = super::execute(SOURCE);
    let call = invocation(&mut run);
    let id = call.builtin.as_ref().unwrap().conclusions[0].fact_id();
    let child = super::atomic_proof_mut(&mut call.dom_proofs[1]);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &mut child.searched_proof
    else {
        panic!("original vector assumption")
    };
    cite.cite_fact_id = id;
    assert!(compiler.compile_run(&run, "future_cauchy").is_err());
}

const ALPHA: &str =
    include_str!("../../../lean/examples/complex_modulus_bound_names/statement.lit");

#[test]
fn complex_modulus_replays_original_compound_alpha_evidence() {
    let (run, compiler) = super::execute(ALPHA);
    let output = compiler.compile_run(&run, "modulus_alpha").unwrap();
    assert!(output.contains("Litex.complexAbs"));
    assert_eq!(output, compiler.compile_run(&run, "modulus_alpha").unwrap());
}

#[test]
fn complex_modulus_alpha_rejects_changed_operator_body_domain_and_free_arguments() {
    use super::super::source_position::{SourceOwner, SourcePosition};
    let (run, compiler) = super::execute(ALPHA);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(named),
    )) = &run.statement_results[0]
    else {
        panic!()
    };
    let ExecDefThmBodyProof::Forall(body) = &named.body else {
        panic!()
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(step)) = &body.proof_steps[0] else {
        panic!()
    };
    let equality = super::equality_proof(&step.verify_result);
    let EqualFactSearchedProof::ByTheyAreTheSame(identity) = &equality.searched_proof else {
        panic!("original compound alpha")
    };
    let position = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    for change in ["operator", "body", "domain", "dimension", "vector"] {
        let mut right = equality.fact.right.clone();
        let Obj::ComplexOperator(ComplexOperator::ComplexAbs(modulus)) = &mut right else {
            panic!()
        };
        if change == "operator" {
            right = Obj::ComplexOperator(ComplexOperator::Conjugate(Conjugate {
                arg: modulus.arg.clone(),
            }));
        } else {
            let Obj::MatrixOperator(MatrixOperator::InnerProduct(inner)) = modulus.arg.as_mut()
            else {
                panic!()
            };
            match change {
                "dimension" => inner.dimension = Box::new(super::number_object("99")),
                "vector" => inner.right = Box::new(super::number_object("0")),
                _ => {
                    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = inner.left.as_mut()
                    else {
                        panic!()
                    };
                    if change == "body" {
                        f.equal_to = Box::new(super::number_object("99"));
                    } else {
                        f.body.set_bound_parameters.groups[0].param_type =
                            Box::new(Obj::StandardSet(StandardSet::R));
                    }
                }
            }
        }
        assert_eq!(
            compiler
                .compile_identity(&equality.fact.left, &right, identity, &position)
                .expect_err("only original bound parameter renaming is permitted")
                .route,
            "Equality/FiniteAggregateAlphaSubject"
        );
    }
}
