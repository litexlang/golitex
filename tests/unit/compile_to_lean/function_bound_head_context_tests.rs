use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    DetailedForallConclusionArgMatchProof, ForallConclusionArgMatchProof,
};
use crate::prelude::*;
pub(super) const SOURCES61:&[(&str,&str)]=&[
("ternary_bound_head","forall sc61a_a,sc61a_b,sc61a_c R,sc61a_f fn(sc61a_u,sc61a_v,sc61a_w R) R,sc61a_P fn(sc61a_h fn(sc61a_p,sc61a_q,sc61a_r R) R,sc61a_x,sc61a_y,sc61a_z R) R:\n    forall sc61a_g fn(sc61a_s,sc61a_t,sc61a_o R) R,sc61a_d,sc61a_e,sc61a_k R:\n        sc61a_g(sc61a_d,sc61a_e,sc61a_k)=sc61a_P(sc61a_g,sc61a_d,sc61a_e,sc61a_k)\n    =>:\n        sc61a_f(sc61a_a,sc61a_b,sc61a_c)=sc61a_P(sc61a_f,sc61a_a,sc61a_b,sc61a_c)\n"),
("guarded_ternary_bound_head","forall sc61b_a,sc61b_b,sc61b_c R,sc61b_f fn(sc61b_u,sc61b_v,sc61b_w R:sc61b_u+sc61b_v>sc61b_w) R,sc61b_P fn(sc61b_h fn(sc61b_p,sc61b_q,sc61b_r R:sc61b_p+sc61b_q>sc61b_r) R,sc61b_x,sc61b_y,sc61b_z R:sc61b_x+sc61b_y>sc61b_z) R:\n    sc61b_a+sc61b_b>sc61b_c\n    forall sc61b_g fn(sc61b_s,sc61b_t,sc61b_o R:sc61b_s+sc61b_t>sc61b_o) R,sc61b_d,sc61b_e,sc61b_k R:\n        sc61b_d+sc61b_e>sc61b_k\n        =>:\n            sc61b_g(sc61b_d,sc61b_e,sc61b_k)=sc61b_P(sc61b_g,sc61b_d,sc61b_e,sc61b_k)\n    =>:\n        sc61b_f(sc61b_a,sc61b_b,sc61b_c)=sc61b_P(sc61b_f,sc61b_a,sc61b_b,sc61b_c)\n"),
("generic_ternary_bound_head","forall sc61c_A,sc61c_B,sc61c_C,sc61c_D set,sc61c_a sc61c_A,sc61c_b sc61c_B,sc61c_c sc61c_C,sc61c_f fn(sc61c_u sc61c_A,sc61c_v sc61c_B,sc61c_w sc61c_C) sc61c_D,sc61c_P fn(sc61c_h fn(sc61c_p sc61c_A,sc61c_q sc61c_B,sc61c_r sc61c_C) sc61c_D,sc61c_x sc61c_A,sc61c_y sc61c_B,sc61c_z sc61c_C) sc61c_D:\n    forall sc61c_g fn(sc61c_s sc61c_A,sc61c_t sc61c_B,sc61c_o sc61c_C) sc61c_D,sc61c_d sc61c_A,sc61c_e sc61c_B,sc61c_k sc61c_C:\n        sc61c_g(sc61c_d,sc61c_e,sc61c_k)=sc61c_P(sc61c_g,sc61c_d,sc61c_e,sc61c_k)\n    =>:\n        sc61c_f(sc61c_a,sc61c_b,sc61c_c)=sc61c_P(sc61c_f,sc61c_a,sc61c_b,sc61c_c)\n")];
fn head61(head: &FnObjHead) -> Obj {
    let FnObjHead::Identifier(identifier) = head else {
        panic!("original identifier function head")
    };
    Obj::Identifier(identifier.clone())
}
fn call61(
    proof: &ForallConclusionArgMatchProof,
) -> (&FnObj, &FnObj, &[ForallConclusionArgMatchProof]) {
    let DetailedForallConclusionArgMatchProof::ByStructure {
        pattern,
        goal_arg,
        child_matches,
    } = proof.as_detailed().unwrap()
    else {
        panic!("original call structure")
    };
    let (Obj::FnObj(pattern), Obj::FnObj(goal)) = (pattern, goal_arg) else {
        panic!("original call objects")
    };
    assert_eq!(pattern.body.len(), 1);
    assert_eq!(goal.body.len(), 1);
    assert_eq!(pattern.body[0].len(), goal.body[0].len());
    (pattern, goal, child_matches)
}
#[test]
fn function_bound_head_original_ordered_match_trees() {
    for (name, source) in SOURCES61 {
        let (run, _compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByKnownForallFact(p) = &equal.searched_proof else {
            panic!("original known forall:{name}")
        };
        let p = p.as_detailed().unwrap();
        let Fact::ForallFact(cited) = outer
            .fact
            .dom_facts
            .iter()
            .find(|f| f.fact_id() == p.cite.fact_id)
            .unwrap()
        else {
            panic!()
        };
        let ids: Vec<_> = cited
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect();
        assert_eq!(ids.len(), 4);
        assert_eq!(p.forall_parameters_match_what_args.len(), 4);
        assert_eq!(p.arg_match_proofs.len(), 2);
        let (pattern, goal, children) = call61(&p.arg_match_proofs[0]);
        assert_eq!(children.len(), 4);
        assert_eq!(pattern.body[0].len(), 3);
        for (i, child) in children.iter().enumerate() {
            let DetailedForallConclusionArgMatchProof::BoundParam {
                param_id,
                pattern: captured,
                goal_arg,
            } = child.as_detailed().unwrap()
            else {
                panic!("original bound function/args:{name}:{i}")
            };
            let parameter = if i == 3 { 0 } else { i + 1 };
            assert_eq!(*param_id, ids[parameter]);
            let (a, b) = if i == 3 {
                (head61(pattern.head.as_ref()), head61(goal.head.as_ref()))
            } else {
                (
                    pattern.body[0][i].as_ref().clone(),
                    goal.body[0][i].as_ref().clone(),
                )
            };
            assert_eq!(captured.ir(), a.ir());
            assert_eq!(goal_arg.ir(), b.ir());
            assert_eq!(p.forall_parameters_match_what_args[parameter].ir(), b.ir());
            eprintln!("ORIGINAL61 {name} left_match:{i} source_parameter:{parameter} id:{} pattern:{} goal:{}",param_id.value(),a.ir(),b.ir());
        }
        let (pattern, goal, children) = call61(&p.arg_match_proofs[1]);
        assert_eq!(children.len(), 5);
        assert_eq!(pattern.body[0].len(), 4);
        for (i, child) in children[..4].iter().enumerate() {
            let DetailedForallConclusionArgMatchProof::ReboundParamEqual {
                param_id,
                previous,
                goal_arg,
                equal,
            } = child.as_detailed().unwrap()
            else {
                panic!("original evaluator rebound:{name}:{i}")
            };
            assert_eq!(*param_id, ids[i]);
            assert_eq!(previous.ir(), p.forall_parameters_match_what_args[i].ir());
            assert_eq!(goal_arg.ir(), goal.body[0][i].ir());
            assert_eq!(equal.equal_fact.left.ir(), previous.ir());
            assert_eq!(equal.equal_fact.right.ir(), goal_arg.ir());
            eprintln!(
                "ORIGINAL61 {name} right_rebound:{i} id:{} previous:{} goal:{}",
                param_id.value(),
                previous.ir(),
                goal_arg.ir()
            );
        }
        let DetailedForallConclusionArgMatchProof::NonParamEqual {
            pattern: captured,
            pattern_after_subst,
            goal_arg,
            equal: head_equal,
        } = children[4].as_detailed().unwrap()
        else {
            panic!("original fixed evaluator head:{name}")
        };
        let a = head61(pattern.head.as_ref());
        let b = head61(goal.head.as_ref());
        assert_eq!(captured.ir(), a.ir());
        assert_eq!(pattern_after_subst.ir(), a.ir());
        assert_eq!(goal_arg.ir(), b.ir());
        assert_eq!(head_equal.equal_fact.left.ir(), a.ir());
        assert_eq!(head_equal.equal_fact.right.ir(), b.ir());
        eprintln!("ORIGINAL61 {name} fixed_evaluator:{}", a.ir());
        let wd = equal.well_defined_proof.as_detailed().unwrap();
        assert_eq!(wd.left.obj().ir(), equal.fact.left.ir());
        assert_eq!(wd.right.obj().ir(), equal.fact.right.ir());
        eprintln!(
            "ORIGINAL61 {name} cite:{} binder_order:1,2,3,0 rebound_order:0,1,2,3",
            p.cite.fact_id.value()
        );
    }
}
#[test]
fn function_bound_head_original_types_guard_and_compilation() {
    for (name, source) in SOURCES61 {
        let (run, compiler) = super::execute(source);
        let outer = super::forall_proof(&run.statement_results[0]);
        let equal = super::equality_proof(&outer.proved_then_facts[0].verify_result);
        let EqualFactSearchedProof::ByKnownForallFact(p) = &equal.searched_proof else {
            panic!()
        };
        let p = p.as_detailed().unwrap();
        let Fact::ForallFact(cited) = outer
            .fact
            .dom_facts
            .iter()
            .find(|f| f.fact_id() == p.cite.fact_id)
            .unwrap()
        else {
            panic!()
        };
        let ids: Vec<_> = cited
            .typed_parameters
            .groups
            .iter()
            .flat_map(|g| g.params.iter().map(|p| p.id))
            .collect();
        let req = p.instantiation_requirements.as_detailed().unwrap();
        assert_eq!(req.param_type_requirements.len(), 4);
        for (i, ty) in req.param_type_requirements.iter().enumerate() {
            assert_eq!(ty.param_id, ids[i]);
            eprintln!(
                "ORIGINAL61 {name} type:{i} parameter:{}",
                ty.param_id.value()
            );
        }
        let guards = usize::from(*name == "guarded_ternary_bound_head");
        assert_eq!(req.dom_facts.len(), guards);
        assert_eq!(req.proof_of_dom_facts.len(), guards);
        for (fact, proof) in req.dom_facts.iter().zip(&req.proof_of_dom_facts) {
            assert_eq!(
                crate::compile_to_lean::helper::source_subject(proof).unwrap(),
                *fact
            );
            assert_eq!(fact.ir(), outer.fact.dom_facts[0].ir());
            let VerifyFactResult::AtomicExceptEquality(proof) = proof else {
                panic!()
            };
            let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_ref() else {
                panic!()
            };
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                &proof.searched_proof
            else {
                panic!("original guarded source route:{name}")
            };
            assert_eq!(known.cite_fact_id, outer.fact.dom_facts[0].fact_id());
            assert_eq!(
                known.why_parameters_of_known_fact_are_equal_to_givens.len(),
                2
            );
            eprintln!(
                "ORIGINAL61 {name} guard:{} cite:{} equal_args:2",
                fact.ir(),
                known.cite_fact_id.value()
            );
        }
        let compiled = compiler.compile_run(&run, "Function61Original").unwrap();
        assert!(compiled.starts_with("import Litex\n"));
        eprintln!("ORIGINAL61 {name} compilation_passed guards:{guards}");
    }
}

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::DetailedSearchProofByKnownForallFact;
fn equal61(run: &mut RunLitexCodeResult) -> &mut VerifyEqualitySuccess {
    let outer = super::forall_proof_mut(&mut run.statement_results[0]);
    super::equality_proof_mut(&mut outer.proved_then_facts[0].verify_result)
}
fn app61(run: &mut RunLitexCodeResult) -> &mut DetailedSearchProofByKnownForallFact {
    let EqualFactSearchedProof::ByKnownForallFact(p) = &mut equal61(run).searched_proof else {
        panic!()
    };
    p.as_detailed_mut().unwrap()
}
fn side61(run: &mut RunLitexCodeResult, index: usize) -> &mut Vec<ForallConclusionArgMatchProof> {
    let DetailedForallConclusionArgMatchProof::ByStructure { child_matches, .. } = app61(run)
        .arg_match_proofs[index]
        .as_detailed_mut()
        .unwrap()
    else {
        panic!()
    };
    child_matches
}
fn guard61(run: &mut RunLitexCodeResult) -> &mut AtomicExceptEqualityFactSearchedProof {
    let VerifyFactResult::AtomicExceptEquality(p) = &mut app61(run)
        .instantiation_requirements
        .as_detailed_mut()
        .unwrap()
        .proof_of_dom_facts[0]
    else {
        panic!()
    };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = p.as_mut() else {
        panic!()
    };
    &mut p.searched_proof
}
fn reject61(run: &RunLitexCodeResult, compiler: &crate::compile_to_lean::LitexToLeanCompiler) {
    compiler
        .compile_run(run, "Function61ChangedEvidence")
        .expect_err("changed original evidence must reject");
}

#[test]
fn function_bound_head_requires_complete_left_call_tree() {
    for (_, source) in SOURCES61 {
        for extra in [false, true] {
            let (mut run, compiler) = super::execute(source);
            if extra {
                let (mut donor, _) = super::execute(source);
                side61(&mut run, 0).push(side61(&mut donor, 0).pop().unwrap());
            } else {
                side61(&mut run, 0).pop();
            }
            assert_eq!(
                compiler
                    .compile_run(&run, "Function61LeftArity")
                    .unwrap_err()
                    .route,
                "KnownApplication/FunctionArity"
            );
        }
    }
}
#[test]
fn function_bound_head_requires_complete_right_call_tree() {
    for (_, source) in SOURCES61 {
        for extra in [false, true] {
            let (mut run, compiler) = super::execute(source);
            if extra {
                let (mut donor, _) = super::execute(source);
                side61(&mut run, 1).push(side61(&mut donor, 1).pop().unwrap());
            } else {
                side61(&mut run, 1).pop();
            }
            assert_eq!(
                compiler
                    .compile_run(&run, "Function61RightArity")
                    .unwrap_err()
                    .route,
                "KnownApplication/FunctionArity"
            );
        }
    }
}
#[test]
fn function_bound_head_preserves_arguments_then_head_order() {
    for (_, source) in SOURCES61 {
        let (mut run, compiler) = super::execute(source);
        side61(&mut run, 0).swap(0, 3);
        reject61(&run, &compiler);
    }
}
#[test]
fn function_bound_head_requires_each_original_binder() {
    for (_, source) in SOURCES61 {
        for index in 0..4 {
            let (mut run, compiler) = super::execute(source);
            let DetailedForallConclusionArgMatchProof::BoundParam { param_id, .. } =
                side61(&mut run, 0)[index].as_detailed_mut().unwrap()
            else {
                panic!()
            };
            *param_id = IdentifierId::new(u64::MAX);
            reject61(&run, &compiler);
        }
    }
}
#[test]
fn function_bound_head_preserves_source_type_and_captured_argument_ids() {
    for (_, source) in SOURCES61 {
        for change in ["source", "first_type", "last_type", "argument"] {
            let (mut run, compiler) = super::execute(source);
            match change {
                "source" => app61(&mut run).cite.fact_id = FactId::new(u64::MAX),
                "first_type" => {
                    app61(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[0]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                "last_type" => {
                    app61(&mut run)
                        .instantiation_requirements
                        .as_detailed_mut()
                        .unwrap()
                        .param_type_requirements[3]
                        .param_id = IdentifierId::new(u64::MAX)
                }
                _ => app61(&mut run).forall_parameters_match_what_args.swap(0, 1),
            }
            reject61(&run, &compiler);
        }
    }
}
#[test]
fn function_bound_head_requires_each_original_rebound() {
    for (_, source) in SOURCES61 {
        for index in 0..4 {
            for change in ["binder", "previous", "subject"] {
                let (mut run, compiler) = super::execute(source);
                let wrong = equal61(&mut run).fact.left.clone();
                let DetailedForallConclusionArgMatchProof::ReboundParamEqual {
                    param_id,
                    previous,
                    equal,
                    ..
                } = side61(&mut run, 1)[index].as_detailed_mut().unwrap()
                else {
                    panic!()
                };
                match change {
                    "binder" => *param_id = IdentifierId::new(u64::MAX),
                    "previous" => {
                        assert_ne!(previous.ir(), wrong.ir());
                        *previous = wrong;
                    }
                    _ => {
                        assert_ne!(equal.equal_fact.left.ir(), wrong.ir());
                        equal.equal_fact.left = wrong;
                    }
                }
                reject61(&run, &compiler);
            }
        }
    }
}
#[test]
fn function_bound_head_requires_original_fixed_evaluator() {
    for (_, source) in SOURCES61 {
        let (mut run, compiler) = super::execute(source);
        let wrong = app61(&mut run).forall_parameters_match_what_args[0].clone();
        let DetailedForallConclusionArgMatchProof::NonParamEqual {
            pattern_after_subst,
            ..
        } = side61(&mut run, 1)[4].as_detailed_mut().unwrap()
        else {
            panic!()
        };
        assert_ne!(pattern_after_subst.ir(), wrong.ir());
        *pattern_after_subst = wrong;
        reject61(&run, &compiler);
    }
}
#[test]
fn function_bound_head_rejects_enclosing_unfinished_forall_citation() {
    for (_, source) in SOURCES61 {
        let (mut run, compiler) = super::execute(source);
        compiler
            .compile_run(&run, "Function61EnclosingPristine")
            .unwrap();
        let id = super::forall_proof(&run.statement_results[0]).fact.fact_id;
        assert_ne!(app61(&mut run).cite.fact_id, id);
        app61(&mut run).cite.fact_id = id;
        reject61(&run, &compiler);
    }
}

#[test]
fn function_bound_head_rejects_sibling_forall_citation() {
    for (_, source) in SOURCES61 {
        let sibling = source.replace("sc61", "sc61s");
        let (mut run, compiler) = super::execute(&format!("{source}{sibling}"));
        compiler
            .compile_run(&run, "Function61SiblingPristine")
            .unwrap();
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(sibling)) = &run.statement_results[1]
        else {
            panic!()
        };
        let Fact::ForallFact(sibling) =
            crate::compile_to_lean::helper::source_subject(&sibling.verify_result).unwrap()
        else {
            panic!()
        };
        let id = sibling
            .dom_facts
            .iter()
            .find(|fact| matches!(fact, Fact::ForallFact(_)))
            .unwrap()
            .fact_id();
        app61(&mut run).cite.fact_id = id;
        reject61(&run, &compiler);
    }
}
#[test]
fn function_bound_head_requires_full_parent_and_call_formation() {
    for (_, source) in SOURCES61 {
        for missing in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let wd = equal61(&mut run)
                .well_defined_proof
                .as_detailed_mut()
                .unwrap();
            if missing {
                let DetailedObjWellDefinedProof::ByDef {
                    proof: ObjWellDefinedProofByDef::FnObj(p),
                    ..
                } = wd.right.as_detailed_mut().unwrap()
                else {
                    panic!("original evaluator call WD")
                };
                p.requirement_fact_verified.pop();
            } else {
                std::mem::swap(&mut wd.left, &mut wd.right);
            }
            reject61(&run, &compiler);
        }
    }
}
#[test]
fn function_bound_head_requires_all_ordered_type_certificates() {
    for (_, source) in SOURCES61 {
        for order in [false, true] {
            let (mut run, compiler) = super::execute(source);
            let types = &mut app61(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .param_type_requirements;
            if order {
                types.swap(0, 3);
            } else {
                types.pop();
            }
            reject61(&run, &compiler);
        }
    }
}
#[test]
fn function_bound_head_requires_original_guard_lists_and_subject() {
    for change in ["facts", "proofs", "extra", "subject"] {
        let (mut run, compiler) = super::execute(SOURCES61[1].1);
        if change == "subject" {
            let (mut donor, _) = super::execute(SOURCES61[0].1);
            let wrong = super::forall_proof_mut(&mut donor.statement_results[0])
                .proved_then_facts
                .pop()
                .unwrap()
                .verify_result;
            app61(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0] = wrong;
        } else {
            let req = app61(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap();
            match change {
                "facts" => req.dom_facts.clear(),
                "proofs" => req.proof_of_dom_facts.clear(),
                _ => req.dom_facts.push(req.dom_facts[0].clone()),
            }
        }
        reject61(&run, &compiler);
    }
}
#[test]
fn function_bound_head_rejects_foreign_and_self_guard_citations() {
    for own in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES61[1].1);
        let id = crate::compile_to_lean::helper::source_subject(
            &app61(&mut run)
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts[0],
        )
        .unwrap()
        .fact_id();
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard61(&mut run)
        else {
            panic!()
        };
        assert_ne!(known.cite_fact_id, id);
        known.cite_fact_id = if own { id } else { FactId::new(u64::MAX) };
        reject61(&run, &compiler);
    }
}
#[test]
fn function_bound_head_rejects_future_and_sibling_guard_citations() {
    let source = SOURCES61[1].1;
    let later = "sc61b_a+sc61b_b>sc61b_c";
    let (mut run, compiler) = super::execute(&format!("{source}        {later}\n"));
    compiler
        .compile_run(&run, "Function61FutureGuardPristine")
        .unwrap();
    let outer = super::forall_proof(&run.statement_results[0]);
    assert_eq!(outer.proved_then_facts.len(), 2);
    let future =
        crate::compile_to_lean::helper::source_subject(&outer.proved_then_facts[1].verify_result)
            .unwrap();
    assert_eq!(future.ir(), outer.fact.dom_facts[0].ir());
    let id = future.fact_id();
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard61(&mut run) else {
        panic!()
    };
    known.cite_fact_id = id;
    reject61(&run, &compiler);
    let sibling = source.replace("sc61", "sc61s");
    let (mut run, compiler) = super::execute(&format!("{source}{sibling}"));
    compiler
        .compile_run(&run, "Function61SiblingGuardPristine")
        .unwrap();
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(sibling)) = &run.statement_results[1]
    else {
        panic!()
    };
    let Fact::ForallFact(sibling) =
        crate::compile_to_lean::helper::source_subject(&sibling.verify_result).unwrap()
    else {
        panic!()
    };
    let id = sibling.dom_facts[0].fact_id();
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard61(&mut run) else {
        panic!()
    };
    known.cite_fact_id = id;
    reject61(&run, &compiler);
}
#[test]
fn function_bound_head_requires_original_guard_argument_proofs() {
    for count in [false, true] {
        let (mut run, compiler) = super::execute(SOURCES61[1].1);
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) = guard61(&mut run)
        else {
            panic!()
        };
        if count {
            known.why_parameters_of_known_fact_are_equal_to_givens.pop();
        } else {
            let (mut donor, _) = super::execute(SOURCES61[0].1);
            std::mem::swap(
                &mut known.why_parameters_of_known_fact_are_equal_to_givens[0],
                &mut equal61(&mut donor).searched_proof,
            );
        }
        reject61(&run, &compiler);
    }
}
