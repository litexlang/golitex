use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::prelude::*;
use crate::store_fact_and_infer::InferResult;

const REPEATED_CHAIN: &str = "# Select one direct equality edge from a named theorem's returned chain.\nthm repeated_chain:\n    ? forall x R:\n        x=x=x\n    x=x=x\nhave a_chain R=2\nby thm repeated_chain(a_chain) => a_chain=a_chain\n";
const REPEATED_AND: &str = "# Select one direct equality component from a named theorem's returned conjunction.\nthm repeated_and:\n    ? forall x R:\n        x=x and x=x\n    x=x and x=x\nhave a_and R=2\nby thm repeated_and(a_and) => a_and=a_and\n";
const MIXED_RETURN: &str = "# Select real membership from the second package in a mixed chain and conjunction return.\nthm mixed_return:\n    ? forall x R:\n        x=x=x\n        x $in R and x=x\n    x=x=x\n    x $in R and x=x\nhave a_mixed R=2\nby thm mixed_return(a_mixed) => a_mixed $in R\n";
const SUM_CHAIN: &str = "# Select the addition edge while preserving caller WD and a later alias.\nthm sum_chain:\n    ? forall x R:\n        x+0=x=x\n    x+0=x\n    x=x\nhave a_sum R=2\nby thm sum_chain(a_sum) => a_sum+0=a_sum\nlet later_sum=a_sum+0\n";
const QUOTIENT_PACKAGE: &str = "# A guarded quotient returns its product chain and real/complex range facts.\nhave fn quotient(x R, y R: y!=0) R = x/y\nthm quotient_package:\n    ? forall x,y R:\n        y!=0\n        =>:\n            quotient(x,y)*y=(x/y)*y=x\n            quotient(x,y) $in R and quotient(x,y) $in C\n    quotient(x,y)=x/y\n    quotient(x,y)*y=(x/y)*y\n    (x/y)*y=x\n    quotient(x,y) $in R and quotient(x,y) $in C\nhave numerator R=4\nhave denominator R=2\ndenominator!=0\nby thm quotient_package(numerator,denominator) => quotient(numerator,denominator)*denominator=(numerator/denominator)*denominator\nby thm quotient_package(numerator,denominator) => quotient(numerator,denominator) $in C\nquotient(numerator,denominator)*denominator=4\n";
const INTERVAL_PACKAGE: &str = "# Recover both orientations of real interval bounds from named chain and conjunction packages.\nthm named_compound_bounds:\n    ? forall x R:\n        0<=x<=1\n        =>:\n            0<=x<=1\n            x>=0 and x<=1\n    0<=x<=1\n    x>=0 and x<=1\nhave midpoint R=1/2\n0<=midpoint<=1\nby thm named_compound_bounds(midpoint) => 0<=midpoint\nby thm named_compound_bounds(midpoint) => midpoint>=0\nthm named_compound_lower_bound:\n    ? forall x R:\n        0<=x<=1\n        =>:\n            x>=0\n    by thm named_compound_bounds(x) => x>=0\n";
const NAMED_COMPOUND_THEOREM_RETURNS: &str = "# A real square is nonnegative and equals the product of its factors; select both returned package families explicitly.\nthm square_packages:\n    ? forall x R:\n        x*x=x^2=x*x\n        0<=x^2 and x*x=x^2\n    x*x=x^2=x*x\n    0<=x^2 and x*x=x^2\nthm nonnegative_square_from_package:\n    ? forall x R:\n        0<=x^2\n    by thm square_packages(x) => 0<=x^2\nthm square_product_from_package:\n    ? forall x R:\n        x*x=x^2\n    by thm square_packages(x) => x*x=x^2\n";
const TWO_SUM_PACKAGES: &str = "# All returned conclusion WD must complete before either package is published.\nthm two_sum_packages:\n    ? forall x C:\n        x $in C and x=x\n        x+0=x=x\n    x $in C and x=x\n    x+0=x\n    x=x\nhave a_two C=2\nby thm two_sum_packages(a_two) => a_two+0=a_two\n";

fn selected_id(proof: &ExecByThmStmtSuccess) -> FactId {
    match &proof.selected_proof {
        VerifyFactResult::Equality(result) => {
            let VerifyEqualityResult::Success(selected) = result.as_ref() else {
                panic!("successful selection")
            };
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(proof),
            ) = &selected.searched_proof
            else {
                panic!("direct unreversed return")
            };
            assert!(!proof.reversed);
            proof.cited.fact_id
        }
        VerifyFactResult::AtomicExceptEquality(result) => {
            let VerifyAtomicExceptEqualityFactResult::Success(selected) = result.as_ref() else {
                panic!("successful selection")
            };
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) =
                &selected.searched_proof
            else {
                panic!("direct returned atom")
            };
            proof.cite_fact_id
        }
        _ => panic!("source selected atomic conclusion"),
    }
}

fn quotient_scalar_child(statement: &ExecStmtResult) -> &VerifyFactResult {
    let equality = super::equality_proof(&super::fact_statement(statement).verify_result);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::ViaPeers(peer),
    ) = &equality.searched_proof
    else {
        panic!("the actual quotient proof uses its selected equality peer")
    };
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ScalarDivisionRelation(
            ScalarDivisionRelationProof::ProductFromDivision(proof),
        ),
    ) = peer.bridge.searched_proof.as_ref()
    else {
        panic!("the actual bridge consumes its checked division equation")
    };
    &proof.division_equation
}

fn quotient_scalar_child_mut(statement: &mut ExecStmtResult) -> &mut VerifyFactResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = statement else {
        panic!("the actual quotient equality statement")
    };
    let equality = super::equality_proof_mut(&mut statement.verify_result);
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::ViaPeers(peer),
    ) = &mut equality.searched_proof
    else {
        panic!("the actual quotient proof uses its selected equality peer")
    };
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::ScalarDivisionRelation(
            ScalarDivisionRelationProof::ProductFromDivision(proof),
        ),
    ) = peer.bridge.searched_proof.as_mut()
    else {
        panic!("the actual bridge consumes its checked division equation")
    };
    &mut proof.division_equation
}

#[test]
fn equality_peer_bridge_rejects_each_wrong_original_endpoint_wd() {
    for side in ["left", "right"] {
        let (mut result, compiler) = super::execute(QUOTIENT_PACKAGE);
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
            &mut result.statement_results[7]
        else {
            panic!("the actual quotient equality statement")
        };
        let equality = super::equality_proof_mut(&mut statement.verify_result);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::ViaPeers(peer),
        ) = &mut equality.searched_proof
        else {
            panic!("the actual quotient proof uses its selected equality peer")
        };
        let wd = if side == "left" {
            &mut peer.bridge.well_defined_proof.left
        } else {
            &mut peer.bridge.well_defined_proof.right
        };
        let wrong_subject = super::number_object("7");
        assert_ne!(wd.obj().ir(), wrong_subject.ir());
        super::replace_wd_subject(wd, wrong_subject);
        let error = super::compile_run(&result, &compiler, "wrong_peer_endpoint_wd")
            .expect_err("a selected peer cannot replace either original endpoint WD");
        assert_eq!(error.route, "WD/Subject", "{side}: {error:?}");
    }
}

#[test]
fn scalar_division_child_formation_is_visible_only_after_completion_without_truth_export() {
    let (result, compiler) = super::execute(QUOTIENT_PACKAGE);
    let child = quotient_scalar_child(&result.statement_results[7]);
    let equality = super::equality_proof(child);
    assert!(matches!(
        &equality.well_defined_proof.left,
        ObjWellDefinedProof::ByDef {
            obj: Obj::ArithmeticOperator(ArithmeticOperator::Div(_)),
            ..
        }
    ));
    let prior = SourcePosition::new(None, SourceOwner::Run(&result), 7);
    compiler
        .compile_verify(child, &prior)
        .expect("the selected division child is already independently replayable");
    let pending = SourcePosition::new(Some(&prior), SourceOwner::Verify(child), 0);
    for position in [&prior, &pending] {
        assert!(
            compiler
                .compile_numeric_observation(&equality.fact.left, position)
                .is_err(),
            "the child-only quotient has no preceding completed constructor"
        );
    }
    let completed = SourcePosition {
        before: usize::MAX,
        ..pending
    };
    compiler
        .compile_numeric_observation(&equality.fact.left, &completed)
        .expect("completion exposes the child's original quotient constructor");
    assert!(
        completed
            .visible_fact(equality.fact.fact_id, &compiler.runtime)
            .is_err(),
        "the formation cursor does not publish the child equation as a stored fact"
    );
    super::compile_run(&result, &compiler, "completed_division_child")
        .expect("the original quotient-package source must still compile unchanged");
}

#[test]
fn scalar_division_rejects_missing_and_wrong_original_child_formation() {
    for mutation in ["children", "requirements", "subject"] {
        let (mut result, compiler) = super::execute(QUOTIENT_PACKAGE);
        let child = quotient_scalar_child_mut(&mut result.statement_results[7]);
        let wd = &mut super::equality_proof_mut(child).well_defined_proof.left;
        if mutation == "subject" {
            super::replace_wd_subject(wd, super::number_object("7"));
        } else {
            let ObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::ArithmeticOperator(
                        ArithmeticOperatorObjWellDefinedProofByDef::Div(proof),
                    ),
                ..
            } = wd
            else {
                panic!("the original child owns this quotient construction")
            };
            if mutation == "children" {
                proof.child_obj_well_defined.clear();
            } else {
                proof.requirement_fact_verified.clear();
            }
        }
        super::compile_run(&result, &compiler, "invalid_division_child_formation")
            .expect_err("completion cannot repair a missing or wrong child constructor");
    }
}

#[test]
fn scalar_division_rejects_a_real_future_child_constructor_cache_token() {
    let source = format!(
        "{QUOTIENT_PACKAGE}\nlet later_child=4/denominator\nlet later_child_cache=4/denominator\n"
    );
    let (mut result, compiler) = super::execute(&source);
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByKnown { obj, wd_id }) =
        &super::let_definition(&result.statement_results[9]).value_well_defined
    else {
        panic!("the second later alias contains the actual future cache token")
    };
    let replacement = ObjWellDefinedProof::ByKnown {
        obj: obj.clone(),
        wd_id: *wd_id,
    };
    let child = quotient_scalar_child_mut(&mut result.statement_results[7]);
    assert_eq!(
        replacement.obj().ir(),
        super::equality_proof(child).fact.left.ir()
    );
    super::equality_proof_mut(child).well_defined_proof.left = replacement;
    super::compile_run(&result, &compiler, "future_division_child_formation")
        .expect_err("the completed child cannot borrow a constructor from a later statement");
}

fn check_calls(statements: &[ExecStmtResult], output: &str) -> usize {
    let mut count = 0;
    for statement in statements {
        match statement {
            ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))) => {
                let direct: Vec<_> = proof
                    .returned_conclusions
                    .iter()
                    .flat_map(|stored| stored.store.atomic_components())
                    .collect();
                let selected = selected_id(proof);
                assert!(direct.iter().any(|(id, _)| *id == selected));
                assert!(proof
                    .returned_conclusions
                    .iter()
                    .all(|store| store.primary_fact_id() != selected));
                for (id, _) in direct {
                    assert!(output.contains(&format!("have h_{} :", id.value())));
                }
                count += 1;
            }
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                ExecDefThmStmtResult::Success(proof),
            )) => {
                let steps = match &proof.body {
                    ExecDefThmBodyProof::Forall(body) => &body.proof_steps,
                    ExecDefThmBodyProof::NonForall(body) => &body.proof_steps,
                };
                count += check_calls(steps, output);
            }
            _ => {}
        }
    }
    count
}

#[test]
fn compound_theorem_returns_replay_direct_chain_and_conjunction_projection_ids() {
    for source in [
        REPEATED_CHAIN,
        REPEATED_AND,
        MIXED_RETURN,
        SUM_CHAIN,
        INTERVAL_PACKAGE,
        QUOTIENT_PACKAGE,
    ] {
        let (result, compiler) = super::execute(source);
        let output = super::compile_run(&result, &compiler, "compound_returns").unwrap();
        assert!(check_calls(&result.statement_results, &output) > 0);
        assert!(!output.contains("sorry") && !output.contains("admit"));
    }
}

#[test]
fn compound_square_scalar_wrappers_really_cite_the_selected_invocation_stores() {
    let (mut result, compiler) = super::execute(NAMED_COMPOUND_THEOREM_RETURNS);
    for index in [1, 2] {
        let theorem = super::named_theorem_mut(&mut result.statement_results[index]);
        let ExecDefThmBodyProof::Forall(body) = &theorem.body else {
            panic!("generic wrapper")
        };
        let ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(call))) =
            &body.proof_steps[0]
        else {
            panic!("explicit package invocation")
        };
        let selected = call.stored.primary_fact_id();
        match &body.conclusion_proofs[0] {
            VerifyFactResult::AtomicExceptEquality(proof) => {
                let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
                    panic!("nonnegative result")
                };
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) =
                    &proof.searched_proof
                else {
                    panic!("actual selected nonnegative citation")
                };
                assert_eq!(proof.cite_fact_id, selected);
            }
            VerifyFactResult::Equality(proof) => {
                let VerifyEqualityResult::Success(proof) = proof.as_ref() else {
                    panic!("product equality")
                };
                let EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(proof),
                ) = &proof.searched_proof
                else {
                    panic!("actual selected equality citation")
                };
                assert_eq!(proof.path.len(), 1);
                assert_eq!(proof.path[0].2, selected);
            }
            _ => panic!("scalar returned property"),
        }
    }
    let output = super::compile_run(&result, &compiler, "square_return_provenance").unwrap();
    assert_eq!(check_calls(&result.statement_results, &output), 2);
}

#[test]
fn compound_theorem_returns_reject_missing_wrong_and_reordered_formation() {
    for mutation in ["missing", "wrong", "reordered"] {
        let (mut result, compiler) = super::execute(MIXED_RETURN);
        let call = super::by_theorem_mut(&mut result.statement_results[2]);
        match mutation {
            "missing" => {
                call.conclusions_wd.pop();
            }
            "reordered" => call.conclusions_wd.swap(0, 1),
            "wrong" => {
                let FactWellDefinedProof::ChainFact { adjacent } = &mut call.conclusions_wd[0]
                else {
                    panic!("actual chain WD")
                };
                super::replace_wd_subject(
                    &mut adjacent[0].well_defined_of_each_parameter[0],
                    super::number_object("7"),
                );
            }
            _ => unreachable!(),
        }
        super::compile_run(&result, &compiler, "wrong_return_formation")
            .expect_err("the exact ordered WD belongs before every returned store");
    }
}

#[test]
fn compound_theorem_returns_reject_missing_wrong_and_reordered_stores() {
    for mutation in [
        "missing",
        "wrong",
        "reordered",
        "edge_index",
        "edge_id",
        "component",
    ] {
        let (mut result, compiler) = super::execute(MIXED_RETURN);
        let call = super::by_theorem_mut(&mut result.statement_results[2]);
        match mutation {
            "missing" => {
                call.returned_conclusions.pop();
            }
            "reordered" => call.returned_conclusions.swap(0, 1),
            "wrong" | "edge_index" | "edge_id" => {
                let StoreFactResult::ChainFact(store) = &mut call.returned_conclusions[0].store
                else {
                    panic!("chain package")
                };
                match mutation {
                    "wrong" => store.fact.objs[0] = super::number_object("7"),
                    "edge_index" => store.adjacent[0].edge_index = 99,
                    "edge_id" => store.adjacent[0].fact_id = FactId::new(u64::MAX),
                    _ => unreachable!(),
                }
            }
            "component" => {
                let StoreFactResult::AndFact(store) = &mut call.returned_conclusions[1].store
                else {
                    panic!("conjunction package")
                };
                store.components.swap(0, 1);
            }
            _ => unreachable!(),
        }
        super::compile_run(&result, &compiler, "wrong_return_store")
            .expect_err("the actual source package, projection order and IDs must match");
    }
}

#[test]
fn compound_theorem_returns_reject_ambient_inferred_future_and_reversed_selection() {
    for mutation in ["ambient", "inferred", "future", "wrong", "reversed"] {
        let source = REPEATED_CHAIN.replace(
            "by thm repeated_chain",
            "a_chain=a_chain\nby thm repeated_chain",
        ) + "a_chain=a_chain\n";
        let (mut result, compiler) = super::execute(&source);
        let ambient = super::fact_statement(&result.statement_results[2])
            .store_and_infer_result
            .primary_fact_id();
        let future = super::fact_statement(&result.statement_results[4])
            .store_and_infer_result
            .primary_fact_id();
        let call = super::by_theorem_mut(&mut result.statement_results[3]);
        let Some(InferResult::ChainFact(infer)) = &call.returned_conclusions[0].infer else {
            panic!("original chain inference")
        };
        let inferred = infer.transitive_closures[0].derived.store.primary_fact_id();
        let selected = super::equality_proof_mut(&mut call.selected_proof);
        let EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(proof),
        ) = &mut selected.searched_proof
        else {
            panic!("direct alpha endpoints")
        };
        match mutation {
            "ambient" => proof.cited.fact_id = ambient,
            "inferred" => proof.cited.fact_id = inferred,
            "future" => proof.cited.fact_id = future,
            "wrong" => proof.cited.fact_id = FactId::new(u64::MAX),
            "reversed" => proof.reversed = true,
            _ => unreachable!(),
        }
        let error = super::compile_run(&result, &compiler, "invalid_return_selection").unwrap_err();
        assert_eq!(error.route, "ByThm/SelectionProvenance");
    }
}

#[test]
fn compound_theorem_returns_preserve_store_publication_and_nearest_inference_ceiling() {
    let (result, compiler) = super::execute(REPEATED_CHAIN);
    let prior = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    let call = super::by_theorem(&result.statement_results[2]);
    let head = call.type_proofs.len() + call.dom_proofs.len() + call.conclusions_wd.len();
    let direct = call.returned_conclusions[0].store.atomic_components()[0].0;
    let pending = SourcePosition::new(Some(&prior), SourceOwner::Call(call), head);
    assert_eq!(
        pending
            .visible_fact(direct, &compiler.runtime)
            .unwrap_err()
            .route,
        "ByThm/FutureProducer"
    );
    let published = SourcePosition {
        before: head + 1,
        ..pending
    };
    assert_eq!(
        published.visible_fact(direct, &compiler.runtime).unwrap().1,
        format!("h_{}", direct.value())
    );
    let store = &call.returned_conclusions[0];
    let Some(InferResult::ChainFact(infer)) = &store.infer else {
        panic!("original chain infer")
    };
    let derived = infer.transitive_closures[0].derived.store.primary_fact_id();
    let nearest = SourcePosition::new(Some(&published), SourceOwner::CompoundInference(store), 0);
    assert_eq!(
        nearest
            .visible_fact(derived, &compiler.runtime)
            .unwrap_err()
            .route,
        "Inference/FutureProducer"
    );
    let complete = SourcePosition {
        before: infer.adjacent_infers.len() + infer.transitive_closures.len(),
        ..nearest
    };
    assert!(complete.visible_fact(derived, &compiler.runtime).is_ok());
}

#[test]
fn compound_theorem_returns_do_not_publish_early_packages_during_later_wd() {
    let (mut result, compiler) = super::execute(TWO_SUM_PACKAGES);
    let call = super::by_theorem_mut(&mut result.statement_results[2]);
    let member = call.returned_conclusions[0].store.atomic_components()[0].0;
    let FactWellDefinedProof::ChainFact { adjacent } = &mut call.conclusions_wd[1] else {
        panic!("second chain WD")
    };
    let ObjWellDefinedProof::ByDef {
        proof:
            ObjWellDefinedProofByDef::ArithmeticOperator(
                ArithmeticOperatorObjWellDefinedProofByDef::Add(add),
            ),
        ..
    } = &mut adjacent[0].well_defined_of_each_parameter[0]
    else {
        panic!("actual addition constructor")
    };
    let requirement = super::atomic_proof_mut(&mut add.requirement_fact_verified[0]);
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) =
        &mut requirement.searched_proof
    else {
        panic!("original complex member citation")
    };
    proof.cite_fact_id = member;
    let error = super::compile_run(&result, &compiler, "future_return_in_wd").unwrap_err();
    assert_eq!(error.route, "ByThm/FutureProducer");
}

#[test]
fn compound_theorem_returns_keep_caller_wd_outside_closed_and_future_stores() {
    // Selected equality left WD for `by thm sum_chain` is now a ByDef
    // reconstruction of `a_sum+0` (no ByKnown cache token on that package).
    // The future-store attack still applies: a later `let` ByKnown for the same
    // add must not replace the caller construction.
    let (mut result, compiler) = super::execute(SUM_CHAIN);
    let call = super::by_theorem(&result.statement_results[2]);
    assert!(
        matches!(
            &super::equality_proof(&call.selected_proof)
                .well_defined_proof
                .left,
            ObjWellDefinedProof::ByDef { .. }
        ),
        "selected proof left is reconstructed by definition"
    );
    let VerifyObjWellDefinedResult::Success(wd) =
        &super::let_definition(&result.statement_results[3]).value_well_defined
    else {
        panic!("later alias WD")
    };
    let ObjWellDefinedProof::ByKnown { obj, wd_id } = wd else {
        panic!("actual completed caller cache token")
    };
    let replacement = (obj.clone(), *wd_id);
    let call = super::by_theorem_mut(&mut result.statement_results[2]);
    let FactWellDefinedProof::Equality(wd) = &mut call.selected_wd else {
        panic!("actual caller equality WD")
    };
    wd.left = ObjWellDefinedProof::ByKnown {
        obj: replacement.0,
        wd_id: replacement.1,
    };
    super::compile_run(&result, &compiler, "wrong_caller_package_wd")
        .expect_err("later cache records cannot replace the caller construction");
}

#[test]
fn compound_theorem_domain_capture_retains_the_projection_used_by_returned_wd() {
    let (result, compiler) = super::execute(INTERVAL_PACKAGE);
    let call = super::by_theorem(&result.statement_results[3]);
    assert_eq!(call.dom_stores.len(), call.dom_proofs.len());
    let StoreFactResult::ChainFact(domain) = &call.dom_stores[0].store else {
        panic!("the actual interval domain store")
    };
    let FactWellDefinedProof::ChainFact { adjacent } = &call.conclusions_wd[0] else {
        panic!("returned interval WD")
    };
    let PredicateDomainProof::ByKnownFact(cite) = &adjacent[0].predicate_domain else {
        panic!("the original return domain certificate cites the stored domain projection")
    };
    assert_eq!(cite.cite_fact_id, domain.adjacent[0].fact_id);
    let json = crate::json_output::project_run_detailed(&result, &compiler.runtime, "eval", None)
        .stringify_pretty();
    assert!(json.contains("\"dom_stores\""));
    assert!(json.contains(&format!("\"fact_id\": \"f{}\"", cite.cite_fact_id.value())));
    let output = super::compile_run(&result, &compiler, "captured_interval_domain").unwrap();
    assert!(output.contains(&format!("have h_{} :", cite.cite_fact_id.value())));
}

#[test]
fn compound_theorem_domain_capture_rejects_missing_wrong_and_reordered_store_evidence() {
    for mutation in ["missing", "subject", "order", "id"] {
        let (mut result, compiler) = super::execute(INTERVAL_PACKAGE);
        let call = super::by_theorem_mut(&mut result.statement_results[3]);
        if mutation == "missing" {
            call.dom_stores.clear();
        } else {
            let StoreFactResult::ChainFact(domain) = &mut call.dom_stores[0].store else {
                panic!("interval domain store")
            };
            match mutation {
                "subject" => domain.fact.objs[0] = super::number_object("7"),
                "order" => domain.adjacent.swap(0, 1),
                "id" => domain.adjacent[0].fact_id = FactId::new(u64::MAX),
                _ => unreachable!(),
            }
        }
        super::compile_run(&result, &compiler, "wrong_interval_domain_store").expect_err(
            "the exact original ordered domain store is part of the invocation evidence",
        );
    }
}

#[test]
fn compound_theorem_domain_capture_keeps_pending_projections_and_inference_closed() {
    let (result, compiler) = super::execute(INTERVAL_PACKAGE);
    let call = super::by_theorem(&result.statement_results[3]);
    let prior = SourcePosition::new(None, SourceOwner::Run(&result), 3);
    let pending = SourcePosition::new(
        Some(&prior),
        SourceOwner::Call(call),
        call.type_proofs.len(),
    );
    let store = &call.dom_stores[0];
    let edge = store.store.atomic_components()[0].0;
    assert_eq!(
        pending
            .visible_fact(edge, &compiler.runtime)
            .unwrap_err()
            .route,
        "ByThm/FutureDomainProducer"
    );
    let published = SourcePosition {
        before: call.type_proofs.len() + 1,
        ..pending
    };
    assert_eq!(
        published.visible_fact(edge, &compiler.runtime).unwrap().1,
        format!("h_{}", edge.value())
    );
    let Some(InferResult::ChainFact(infer)) = &store.infer else {
        panic!("actual domain chain inference")
    };
    let closure = infer.transitive_closures[0].derived.store.primary_fact_id();
    let nearest = SourcePosition::new(Some(&published), SourceOwner::CompoundInference(store), 0);
    assert_eq!(
        nearest
            .visible_fact(closure, &compiler.runtime)
            .unwrap_err()
            .route,
        "Inference/FutureProducer"
    );
    let complete = SourcePosition {
        before: infer.adjacent_infers.len() + infer.transitive_closures.len(),
        ..nearest
    };
    assert!(complete.visible_fact(closure, &compiler.runtime).is_ok());
    let after_call = SourcePosition::new(None, SourceOwner::Run(&result), 4);
    assert!(
        after_call.visible_fact(edge, &compiler.runtime).is_err(),
        "the local domain projection is not an exported caller fact"
    );
}
