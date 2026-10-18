use super::LitexToLeanCompiler;
use crate::prelude::*;

fn execute(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    let result = runtime.run_litex_code(source).unwrap();
    assert!(result.success, "phase-4 source must verify first");
    (result, LitexToLeanCompiler::new(runtime))
}

#[test]
fn union_and_power_set_membership_replay_the_selected_premises() {
    let (result, compiler) = execute("1 $in union(R, C)\nR $in power_set(R)\n");
    let lean = compiler.compile_run(&result, "set_operators").unwrap();
    assert!(lean.contains("Litex.inUnion_iff"));
    assert!(lean.contains("Litex.inPowerSet_iff"));
    assert!(!lean.contains("sorry"));
}

#[test]
fn union_formation_rejects_a_missing_original_operand() {
    let (mut result, compiler) = execute("have U set = union(R, C)\n");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
    )) = &mut result.statement_results[0]
    else {
        panic!("set alias");
    };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::SetOperator(
            crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef::Union(wd)
        ), ..
    }) = &mut proof.equal_to_well_defined[0] else {
        panic!("union constructor");
    };
    wd.child_obj_well_defined.pop();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_union_child")
            .unwrap_err()
            .route,
        "SetOperator/Stages"
    );
}

#[test]
fn arbitrary_set_preserves_its_generic_carrier_and_exact_store() {
    let (result, compiler) = execute("have A set\n$is_set(A)\nA = A\n");
    let lean = compiler.compile_run(&result, "arbitrary_set").unwrap();
    assert!(lean.contains("Litex.Representation M _Host_i"));
    assert!(lean.contains("Litex.IsSet _value_i"));
    assert!(!lean.contains("Litex.In _value_i"));
    assert!(!lean.contains("axiom "));
}

#[test]
fn quantified_set_kind_does_not_introduce_a_universal_carrier_set() {
    let (result, compiler) = execute("forall A set:\n    $is_set(A)\n    A = A\n");
    let lean = compiler.compile_run(&result, "forall_set").unwrap();
    assert!(lean.contains("Litex.IsSet _value_i"));
    assert!(!lean.contains("Litex.In _value_i"));
}

#[test]
fn empty_enumeration_subset_uses_the_recorded_vacuous_forall_route() {
    let (result, compiler) = execute("have A set = {}\nA $subset R\n");
    let lean = compiler.compile_run(&result, "empty_subset").unwrap();
    assert!(lean.contains("False.elim"));
    assert!(lean.contains("Litex.notInEmpty"));
}

#[test]
fn empty_forall_rejects_an_out_of_bounds_selected_input_group() {
    let (mut result, compiler) = execute("forall x {}:\n    x = x\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut result.statement_results[0]
    else {
        panic!("forall source")
    };
    let VerifyFactResult::ForallFact(p) = &mut p.verify_result else {
        panic!("forall result")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByEmptyParameterDomain(p)) =
        p.as_mut()
    else {
        panic!("selected empty domain")
    };
    p.parameter_group_index = 1;
    assert_eq!(
        compiler
            .compile_run(&result, "invalid_empty_group")
            .unwrap_err()
            .route,
        "EmptyForall/Group"
    );
}

#[test]
fn arbitrary_set_cannot_recover_a_deleted_introduction_from_runtime() {
    let (mut result, compiler) = execute("have A set\nA = A\n");
    result.statement_results.remove(0);
    assert_eq!(
        compiler
            .compile_run(&result, "deleted_set")
            .unwrap_err()
            .route,
        "Identifier/Producer"
    );
}

#[test]
fn arbitrary_set_rejects_a_numeric_nonempty_stage() {
    let (mut set_result, compiler) = execute("have A set\n");
    let (mut numeric_result, _) = execute("have a R\n");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtResult::Success(
            numeric,
        )),
    )) = numeric_result.statement_results.remove(0)
    else {
        panic!("numeric have")
    };
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjInNonemptySet(ExecHaveObjInNonemptySetStmtResult::Success(
            set,
        )),
    )) = &mut set_result.statement_results[0]
    else {
        panic!("set have")
    };
    set.groups[0].nonempty_check = numeric.groups.into_iter().next().unwrap().nonempty_check;
    assert_eq!(
        compiler
            .compile_run(&set_result, "wrong_set_stage")
            .unwrap_err()
            .route,
        "Have/SetStages"
    );
}

#[test]
fn finite_sets_and_bounded_predicates_replay_their_formation() {
    for source in [
        "have A set = {}\n$is_set(A)\n",
        "have A set = {1, 2}\n$is_set(A)\n",
        "have A set = {x Q: x >= 0}\n$is_set(A)\n",
        "have A set = {x R: x != 0, 1 / x > 0}\n$is_set(A)\n",
    ] {
        let (result, compiler) = execute(source);
        compiler.compile_run(&result, "set_formation").unwrap();
    }
}

#[test]
fn finite_membership_and_numeric_subset_use_the_selected_source_children() {
    let (result, compiler) = execute("have A set = {1, 2}\n1 $in A\n2 $in A\nA $subset N\n");
    compiler.compile_run(&result, "finite_membership").unwrap();
}

#[test]
fn nonnegative_rational_builder_subset_replays_universal_definition_and_projections() {
    let source = "have A set = {x Q: x >= 0}\nhave B set = {x R: x >= 0}\nA $subset B\n";
    let (result, compiler) = execute(source);
    let lean = compiler.compile_run(&result, "nonnegative_subset").unwrap();
    assert!(lean.contains("Litex.subsetOfForall"));
    assert!(lean.contains("Litex.inSetBuilder_iff"));
}

#[test]
fn finite_formation_cannot_drop_its_distinctness_evidence() {
    for change in ["missing", "reversed"] {
        let (mut result, compiler) = execute("have A set = {1, 2}\n");
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
        )) = &mut result.statement_results[0]
        else {
            panic!("set equality")
        };
        let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::SetFormer(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef::ListSet(wd)), .. }) = &mut p.equal_to_well_defined[0] else { panic!("finite WD") };
        assert_eq!(wd.requirement_fact_verified.len(), 1);
        let expected_route = if change == "missing" {
            wd.requirement_fact_verified.clear();
            "ListSet/Stages"
        } else {
            let VerifyFactResult::AtomicExceptEquality(proof) =
                &mut wd.requirement_fact_verified[0]
            else {
                panic!("original pairwise inequality");
            };
            let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
                panic!("successful pairwise inequality");
            };
            let AtomicFact::NotEqualFact(fact) = &mut proof.fact else {
                panic!("actual distinctness subject");
            };
            std::mem::swap(&mut fact.left, &mut fact.right);
            "ListSet/DistinctSubject"
        };
        assert_eq!(
            compiler
                .compile_run(&result, "missing_distinctness")
                .unwrap_err()
                .route,
            expected_route
        );
    }
}

#[test]
fn builder_formation_cannot_recover_a_missing_binder_from_local_env() {
    let (mut result, compiler) = execute("have A set = {x Q: x >= 0}\n");
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(p)),
    )) = &mut result.statement_results[0]
    else {
        panic!("set equality")
    };
    let VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef { proof: ObjWellDefinedProofByDef::SetFormer(crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetFormerObjWellDefinedProofByDef::SetBuilder(wd)), .. }) = &mut p.equal_to_well_defined[0] else { panic!("builder WD") };
    wd.defined_params.store_and_infer_results.clear();
    wd.defined_params.stored_fact_ids.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_binder")
            .unwrap_err()
            .route,
        "SetBuilder/Stages"
    );
}

#[test]
fn builder_projection_cannot_omit_its_recorded_alias_resolution() {
    let (mut result, compiler) = execute("have A set = {x R: x >= 0}\nforall y A:\n    y >= 0\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut result.statement_results[1]
    else {
        panic!("forall statement")
    };
    let VerifyFactResult::ForallFact(p) = &mut p.verify_result else {
        panic!("forall result")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) = p.as_mut()
    else {
        panic!("forall introduction")
    };
    let store =
        std::rc::Rc::get_mut(&mut p.introduced_params.defined_params.store_and_infer_results[0])
            .expect("owned source introduction");
    let Some(crate::store_fact_and_infer::InferResult::AtomicFact(
        crate::store_fact_and_infer::InferAtomicFactResult::InFact(rules),
    )) = &mut store.infer
    else {
        panic!("inference")
    };
    let captured = rules
        .iter_mut()
        .find_map(|rule| match rule {
            crate::store_fact_and_infer::InferInFactResult::SetBuilder(p) => Some(p),
            _ => None,
        })
        .expect("builder inference");
    captured.steps[0].equality_path.clear();
    assert_eq!(
        compiler
            .compile_run(&result, "missing_projection_path")
            .unwrap_err()
            .route,
        "SetBuilder/ProjectionEndpoint"
    );
}

#[test]
fn builder_projection_cannot_replace_its_selected_builder() {
    let (mut result, compiler) = execute("forall y {x R: x >= 0}:\n    y >= 0\n");
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = &mut result.statement_results[0]
    else {
        panic!("forall statement")
    };
    let VerifyFactResult::ForallFact(p) = &mut p.verify_result else {
        panic!("forall result")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) = p.as_mut()
    else {
        panic!("forall introduction")
    };
    let store =
        std::rc::Rc::get_mut(&mut p.introduced_params.defined_params.store_and_infer_results[0])
            .expect("owned source introduction");
    let Some(crate::store_fact_and_infer::InferResult::AtomicFact(
        crate::store_fact_and_infer::InferAtomicFactResult::InFact(rules),
    )) = &mut store.infer
    else {
        panic!("inference")
    };
    let captured = rules
        .iter_mut()
        .find_map(|rule| match rule {
            crate::store_fact_and_infer::InferInFactResult::SetBuilder(p) => Some(p),
            _ => None,
        })
        .expect("builder inference");
    captured.steps[0].builder.facts.clear();
    assert!(compiler
        .compile_run(&result, "wrong_projection_builder")
        .is_err());
}
