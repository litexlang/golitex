use crate::execute::execute_by_stmt::{
    ExecByDefStmtResult::Success, ExecByDefStmtSuccess, ExecByStmtResult,
};
use crate::execute::execute_def_thm_stmt::{ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    AtomicExceptEqualityFactSearchProofByDefinition as Definition,
    AtomicExceptEqualityFactSearchedProof as Search, BuiltinPropDefinitionProof as Builtin,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
use crate::execute::ExecDefinitionStmtResult;
use crate::prelude::*;
use crate::runtime::runtime_ids::IdentifierId;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferResult, InferSequenceAnalysisFactResult,
};

const CAUCHY: &str =
    include_str!("../../../lean/examples/sequence_cauchy_definition/statement.lit");
const LIMIT: &str = include_str!("../../../lean/examples/sequence_limit_definition/statement.lit");
const CONVERGENT: &str =
    include_str!("../../../lean/examples/sequence_convergence_witness/statement.lit");
const CITATIONS: &str =
    include_str!("../../../lean/examples/sequence_limit_citations/statement.lit");

fn by_def(run: &mut RunLitexCodeResult) -> &mut ExecByDefStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(p),
    )) = &mut run.statement_results[0]
    else {
        panic!("theorem")
    };
    let ExecDefThmBodyProof::Forall(p) = &mut p.body else {
        panic!("forall body")
    };
    let ExecStmtResult::By(ExecByStmtResult::Def(Success(p))) = p.proof_steps.last_mut().unwrap()
    else {
        panic!("by def")
    };
    p
}
fn epsilon_definition(
    run: &mut RunLitexCodeResult,
) -> (&mut Vec<Fact>, &mut Vec<VerifyFactResult>) {
    let p = super::atomic_proof_mut(&mut by_def(run).proof);
    let Search::ByDefinition(Definition::BuiltinProp(p)) = &mut p.searched_proof else {
        panic!("definition")
    };
    match p {
        Builtin::SequenceAnalysis(p) => {
            (&mut p.requirement_facts, &mut p.proof_of_requirement_facts)
        }
        Builtin::SequenceLimit(p) => (&mut p.requirement_facts, &mut p.proof_of_requirement_facts),
        _ => panic!("sequence epsilon definition"),
    }
}
fn exists(f: &mut ForallFact) -> &mut PlainExistFact {
    let ExistOrAndChainAtomicFact::ExistFact(p) = &mut f.then_facts[0] else {
        panic!("exists")
    };
    p
}
fn inclusion(p: &mut PlainExistFact) -> &mut SubsetFact {
    let QuantifierFreeFact::AtomicFact(AtomicFact::SubsetFact(p)) = &mut p.facts[0] else {
        panic!("subset")
    };
    p
}
fn builder(o: &mut Obj) -> &mut SetBuilder {
    let Obj::SetFormer(SetFormer::SetBuilder(p)) = o else {
        panic!("builder")
    };
    p
}

#[test]
fn sequence_epsilon_examples_replay_original_results() {
    for source in [CAUCHY, LIMIT, CONVERGENT, CITATIONS] {
        let (run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "sequence_epsilon")
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    }
}

#[test]
fn sequence_epsilon_rejects_changed_quantifiers_and_missing_children() {
    for source in [CAUCHY, LIMIT] {
        for mutation in 0..6 {
            let (mut run, compiler) = super::execute(source);
            let (facts, proofs) = epsilon_definition(&mut run);
            if mutation == 0 {
                proofs.clear();
            } else {
                let Fact::ForallFact(f) = &mut facts[0] else {
                    panic!("forall")
                };
                match mutation {
                    1 => {
                        f.typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::R))
                    }
                    2 => {
                        exists(f).typed_parameters.groups[0].param_type =
                            ParamType::Obj(Obj::StandardSet(StandardSet::N))
                    }
                    3 => {
                        exists(f).typed_parameters.groups[0].params[0].id =
                            f.typed_parameters.groups[0].params[0].id
                    }
                    4 => {
                        let p = exists(f);
                        p.facts.push(p.facts[0].clone());
                    }
                    _ => {
                        let premise = Fact::ExistFact(exists(f).clone());
                        f.dom_facts.push(premise);
                    }
                }
            }
            let e = compiler
                .compile_run(&run, "bad_epsilon_clause")
                .expect_err("changed epsilon contract");
            assert!(
                e.route.starts_with("SequenceEpsilon/") || e.route == "RealBounds/Carrier",
                "{mutation}: {e:?}"
            );
        }
    }
}

#[test]
fn sequence_limit_rejects_changed_tail_ball_and_preimage() {
    for mutation in 0..5 {
        let (mut run, compiler) = super::execute(LIMIT);
        let (facts, _) = epsilon_definition(&mut run);
        let Fact::ForallFact(f) = &mut facts[0] else {
            panic!("forall")
        };
        let p = inclusion(exists(f));
        if mutation == 0 {
            builder(&mut p.left).param_set = Box::new(Obj::StandardSet(StandardSet::N));
        } else {
            let Obj::FunctionSpace(FunctionSpace::PreimageSet(image)) = &mut p.right else {
                panic!("preimage")
            };
            match mutation {
                1 => image.function = Box::new(Obj::StandardSet(StandardSet::R)),
                2 => {
                    builder(&mut image.target_set).param_set =
                        Box::new(Obj::StandardSet(StandardSet::C))
                }
                3 => builder(&mut image.target_set).facts.clear(),
                _ => {
                    let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(p)) =
                        &mut builder(&mut image.target_set).facts[0]
                    else {
                        panic!("distance")
                    };
                    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(p)) = &mut p.left else {
                        panic!("abs")
                    };
                    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) = p.arg.as_mut() else {
                        panic!("difference")
                    };
                    std::mem::swap(&mut p.left, &mut p.right);
                }
            }
        }
        let e = compiler
            .compile_run(&run, "bad_limit_clause")
            .expect_err("changed limit contract");
        assert!(e.route.starts_with("SequenceEpsilon/"), "{mutation}: {e:?}");
    }
}

#[test]
fn sequence_cauchy_rejects_changed_pair_calls() {
    let (mut run, compiler) = super::execute(CAUCHY);
    let (facts, _) = epsilon_definition(&mut run);
    let Fact::ForallFact(f) = &mut facts[0] else {
        panic!("forall")
    };
    let b = builder(&mut inclusion(exists(f)).right);
    let QuantifierFreeFact::AtomicFact(AtomicFact::LessFact(p)) = &mut b.facts[0] else {
        panic!("comparison")
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(p)) = &mut p.left else {
        panic!("abs")
    };
    let Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) = p.arg.as_mut() else {
        panic!("difference")
    };
    p.right = p.left.clone();
    assert_eq!(
        compiler
            .compile_run(&run, "bad_cauchy_pair")
            .unwrap_err()
            .route,
        "SequenceEpsilon/PairCalls"
    );
}

#[test]
fn sequence_limit_rejects_wrong_real_value_evidence() {
    for mutation in 0..2 {
        let (mut run, compiler) = super::execute(LIMIT);
        let p = super::atomic_proof_mut(&mut by_def(&mut run).proof);
        let PredicateDomainProof::SequenceLimit(p) = &mut p.well_defined_proof.predicate_domain
        else {
            panic!("limit WD")
        };
        if mutation == 0 {
            p.value_real.set = StandardSet::C;
        } else {
            p.value_real.element = Obj::StandardSet(StandardSet::R);
        }
        assert_eq!(
            compiler
                .compile_run(&run, "bad_limit_real")
                .unwrap_err()
                .route,
            "SequenceLimit/RealValue"
        );
    }
}

#[test]
fn sequence_epsilon_rejects_missing_or_reidentified_inferences() {
    for source in [CAUCHY, CONVERGENT] {
        for mutation in 0..2 {
            let (mut run, compiler) = super::execute(source);
            let Some(InferResult::AtomicFact(InferAtomicFactResult::SequenceAnalysisFact(rules))) =
                &mut by_def(&mut run).stored.infer
            else {
                panic!("inference")
            };
            let InferSequenceAnalysisFactResult::Definition(p) = &mut rules[0];
            if mutation == 0 {
                p.source_fact_id = p.derived[0].primary_fact_id();
            } else {
                p.derived.clear();
            }
            assert!(compiler.compile_run(&run, "bad_epsilon_inference").is_err());
        }
    }
}

#[test]
fn nested_set_builder_reuse_rejects_capture_and_changed_free_references() {
    for mutation in 0..4 {
        let (mut run, compiler) = super::execute(LIMIT);
        let (_, proofs) = epsilon_definition(&mut run);
        let VerifyFactResult::ForallFact(p) = &mut proofs[0] else {
            panic!("forall proof")
        };
        let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(p)) =
            p.as_mut()
        else {
            panic!("known forall")
        };
        let cutoff = exists(&mut p.fact).typed_parameters.groups[0].params[0].id;
        let p = inclusion(exists(&mut p.fact));
        if mutation < 3 {
            let b = builder(&mut p.left);
            match mutation {
                0 => b.param_binding.id = cutoff,
                1 => b.param_set = Box::new(Obj::StandardSet(StandardSet::R)),
                _ => b.param_binding.id = IdentifierId::new(u64::MAX),
            }
        } else {
            let Obj::FunctionSpace(FunctionSpace::PreimageSet(p)) = &mut p.right else {
                panic!("preimage")
            };
            p.function = Box::new(Obj::StandardSet(StandardSet::R));
        }
        assert!(compiler.compile_run(&run, "bad_nested_reuse").is_err());
    }
}

#[test]
fn sequence_epsilon_requires_original_forall_citation_and_renaming() {
    for source in [CAUCHY, LIMIT] {
        for mutation in 0..2 {
            let (mut run, compiler) = super::execute(source);
            let (_, proofs) = epsilon_definition(&mut run);
            let VerifyFactResult::ForallFact(p) = &mut proofs[0] else {
                panic!("forall proof")
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(p)) =
                p.as_mut()
            else {
                panic!("known forall")
            };
            if mutation == 0 {
                p.cite_fact_id = crate::runtime::runtime_ids::FactId::new(u64::MAX);
            } else {
                p.parameter_renamings[0].target = IdentifierId::new(u64::MAX);
            }
            let e = compiler
                .compile_run(&run, "bad_epsilon_reference")
                .expect_err("citation and renaming must be original");
            assert_eq!(
                e.route,
                if mutation == 0 {
                    "FactId/Resolution"
                } else {
                    "KnownForall/Renaming"
                }
            );
        }
    }
}
