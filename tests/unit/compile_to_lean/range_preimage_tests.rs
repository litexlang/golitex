use crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection;
use crate::execute::{ExecHaveByFnPreimageStmtResult, ExecHaveByFnPreimageStmtSuccessResult};
use crate::prelude::*;

const SHIFT: &str = include_str!("../../../lean/examples/shift_range_preimage/statement.lit");

fn preimage(run: &mut RunLitexCodeResult) -> &mut ExecHaveByFnPreimageStmtSuccessResult {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveByFnPreimage(ExecHaveByFnPreimageStmtResult::Success(p)),
    )) = &mut run.statement_results[2]
    else {
        panic!("preimage declaration")
    };
    p
}

#[test]
fn range_preimage_replays_selected_signature_and_reuses_choices() {
    let (mut run, compiler) = super::execute(SHIFT);
    let p = preimage(&mut run);
    assert!(matches!(
        &p.signature_selection,
        FunctionSignatureSelection::Property { .. }
    ));
    assert_eq!(p.preimage_parameters.ordered_param_ids().len(), 1);
    let lean = compiler.compile_run(&run, "shift_range_preimage").unwrap();
    assert!(lean.contains("Litex.callInFnRange"));
    assert!(lean.contains("Litex.inFnRange_iff"));
    assert_eq!(lean.matches("theorem _preimage_h_").count(), 1);
    assert!(lean.len() < 30_000);
    assert_eq!(
        lean,
        compiler.compile_run(&run, "shift_range_preimage").unwrap()
    );
}

#[test]
fn preimage_rejects_changed_selection_names_and_stores() {
    for mutation in 0..6 {
        let (mut run, compiler) = super::execute(SHIFT);
        let p = preimage(&mut run);
        match mutation {
            0 => {
                let FunctionSignatureSelection::Property { fact_id, .. } =
                    &mut p.signature_selection
                else {
                    panic!()
                };
                *fact_id = p.statement.range_membership.fact_id;
            }
            1 => {
                let FunctionSignatureSelection::Property { signature, .. } =
                    &mut p.signature_selection
                else {
                    panic!()
                };
                signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
            }
            2 => {
                p.preimage_parameters.groups.clear();
            }
            3 => {
                p.store_and_infer_result.store_and_infer_results.pop();
            }
            4 => {
                p.store_and_infer_result.store_and_infer_results.swap(0, 1);
            }
            5 => {
                p.statement.range_membership.element = Obj::StandardSet(StandardSet::R);
            }
            _ => unreachable!(),
        }
        assert!(
            compiler.compile_run(&run, "corrupted_preimage").is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn preimage_choices_and_facts_follow_source_publication() {
    use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
    let (mut run, compiler) = super::execute(SHIFT);
    let p = preimage(&mut run);
    let id = p.statement.preimage_names[0].id;
    let facts = p.store_and_infer_result.stored_fact_ids.clone();
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    let after = SourcePosition::new(None, SourceOwner::Run(&run), 3);
    assert!(compiler.compile_parameter_reference(id, &before).is_err());
    assert!(compiler.compile_parameter_reference(id, &after).is_ok());
    for fact in facts {
        assert!(compiler.cited_fact_reference(fact, &before).is_err());
        assert!(compiler.cited_fact_reference(fact, &after).is_ok());
    }
}

#[test]
fn range_rejects_missing_original_domain_formation() {
    let (mut run, compiler) = super::execute(SHIFT);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(s)) = &mut run.statement_results[1] else {
        panic!()
    };
    let VerifyFactResult::AtomicExceptEquality(v) = &mut s.verify_result else {
        panic!()
    };
    let VerifyAtomicExceptEqualityFactResult::Success(p) = v.as_mut() else {
        panic!()
    };
    let ObjWellDefinedProof::ByDef {proof:ObjWellDefinedProofByDef::FunctionSpace(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FunctionSpaceObjWellDefinedProofByDef::FnRange(wd)),..}=&mut p.well_defined_proof.well_defined_of_each_parameter[1] else {panic!()};
    wd.function_domains.clear();
    assert!(compiler.compile_run(&run, "missing_range_domain").is_err());
}

#[test]
fn range_supports_generic_membership_guarded_and_paired_preimages() {
    for source in [
        include_str!("../../../lean/examples/function_range_members/statement.lit"),
        include_str!("../../../lean/examples/reciprocal_range_preimage/statement.lit"),
        include_str!("../../../lean/examples/sum_range_preimage/statement.lit"),
        "$is_set(fn_range(fn(x R) R {x}))\n",
        "have fn f(x R) R = x\nlet image = fn_range(f)\n$is_set(image)\n",
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "range_uses").unwrap();
        assert!(!lean.contains("sorry"));
    }
}

#[test]
fn anonymous_range_application_replays_function_equality() {
    let (run, compiler) = super::execute("fn(x R) R {x}(2) $in fn_range(fn(y R) R {y})\n");
    let lean = compiler
        .compile_run(&run, "anonymous_range_application")
        .unwrap();
    assert!(lean.contains("Litex.callInFnRange"));
}

#[test]
fn positive_input_preimage_restores_membership_from_guard() {
    let (run, compiler) = super::execute(
        "have fn f(x R+) R+ = x\nhave by fn_preimage: a from f(2) $in fn_range(f)\n",
    );
    let lean = compiler
        .compile_run(&run, "positive_range_preimage")
        .unwrap();
    assert!(lean.contains("_range_positive_i"));
    assert!(lean.contains("Litex.positiveReal_members"));
}

#[test]
fn range_projection_retains_exact_signature_citations() {
    let (mut run, compiler) = super::execute(SHIFT);
    let p = preimage(&mut run);
    let FunctionSignatureSelection::Property { fact_id, .. } = &p.signature_selection else {
        panic!()
    };
    let selected = fact_id.to_string();
    let json =
        crate::json_output::project_stmt_detailed(&run.statement_results[2], &compiler.runtime);
    let fields = json.as_object().unwrap();
    assert_eq!(
        fields.get("kind").unwrap().as_str().unwrap(),
        "have_by_fn_preimage"
    );
    let selection = fields
        .get("signature_selection")
        .unwrap()
        .as_object()
        .unwrap();
    let source = selection.get("source").unwrap().as_object().unwrap();
    assert_eq!(source.get("fact_id").unwrap().as_str().unwrap(), selected);
    assert!(fields.get("source_membership").unwrap().as_object().is_ok());
    assert!(fields
        .get("preimage_parameters")
        .unwrap()
        .as_str()
        .unwrap()
        .contains("R"));
}

#[test]
fn anonymous_range_rejects_wrong_equality_and_missing_call_evidence() {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::InFactSearchProofByBuiltinRule;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRule;
    use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::SameIrProof;
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute("fn(x R) R {x}(2) $in fn_range(fn(y R) R {y})\n");
        let ExecStmtResult::Fact(ExecFactStmtResult::Success(stmt)) = &mut run.statement_results[0]
        else {
            panic!()
        };
        let VerifyFactResult::AtomicExceptEquality(v) = &mut stmt.verify_result else {
            panic!()
        };
        let VerifyAtomicExceptEqualityFactResult::Success(p) = v.as_mut() else {
            panic!()
        };
        if mutation == 0 {
            let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact(
                    InFactSearchProofByBuiltinRule::AnonymousFnApplicationInFnRange(rule),
                ),
            ) = &mut p.searched_proof
            else {
                panic!("actual literal range builtin")
            };
            rule.function_equal = EqualFactSearchedProof::ByTheyAreTheSame(
                TheyAreTheSameProof::SameIr(SameIrProof::new()),
            );
        } else {
            let ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::FnObj(wd),
                ..
            } = &mut p.well_defined_proof.well_defined_of_each_parameter[0]
            else {
                panic!("original literal application WD")
            };
            if mutation == 1 {
                wd.child_obj_well_defined.clear();
            } else {
                wd.domain_fn_set = None;
            }
        }
        assert!(
            compiler
                .compile_run(&run, "corrupted_literal_range")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn positive_preimage_rejects_changed_carrier_and_guard_order() {
    let source = include_str!("../../../lean/examples/guarded_positive_preimage/statement.lit");
    for mutation in 0..3 {
        let (mut run, compiler) = super::execute(source);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveByFnPreimage(ExecHaveByFnPreimageStmtResult::Success(p)),
        )) = &mut run.statement_results[1]
        else {
            panic!()
        };
        match mutation {
            0 => {
                p.preimage_parameters.groups[0].param_type =
                    ParamType::Obj(Obj::StandardSet(StandardSet::R))
            }
            1 => p.store_and_infer_result.store_and_infer_results.swap(1, 2),
            2 => {
                p.store_and_infer_result.store_and_infer_results.remove(1);
            }
            _ => unreachable!(),
        }
        assert!(
            compiler
                .compile_run(&run, "corrupted_positive_preimage")
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn range_followup_examples_replay_deterministically() {
    for source in [
        include_str!("../../../lean/examples/anonymous_function_ranges/statement.lit"),
        include_str!("../../../lean/examples/positive_range_preimage/statement.lit"),
        include_str!("../../../lean/examples/positive_pair_preimage/statement.lit"),
        include_str!("../../../lean/examples/guarded_positive_preimage/statement.lit"),
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "range_followup").unwrap();
        assert_eq!(lean, compiler.compile_run(&run, "range_followup").unwrap());
        assert!(lean.len() < 150_000);
    }
}

#[test]
fn raw_anonymous_capture_replays_its_original_instantiation() {
    let (run, compiler) = super::execute("have fn outer(x R) R = fn(y R) R {x + y}(1)\n");
    compiler.compile_run(&run, "bound_literal").unwrap();
}
