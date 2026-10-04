use super::by_they_are_the_same::{SameFreeParamShapeProof, TheyAreTheSameProof};
use super::result::*;
use crate::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::execute::ExecStmtResult;
use crate::json_output::{project_stmt_detailed, project_stmt_normal};
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

#[path = "known_tuple.rs"]
mod known_tuple;

#[path = "stored_known_first.rs"]
mod stored_known_first;

#[test]
fn identity_and_alpha_work_without_builtin_entry() {
    for (code, shape) in [
        ("1 = 1", "ir"),
        ("fn(x R) R = fn(y R) R", "fn"),
        ("fn(x R) R {x} = fn(y R) R {y}", "anon"),
        ("{x R: x > 0} = {y R: y > 0}", "set"),
    ] {
        let mut runtime = runtime();
        let fact = equal(&mut runtime, code);
        assert!(!runtime
            .verify_equal_fact_well_definedness(&fact, VerifyState::top_level())
            .unwrap()
            .is_failed());
        let proof = runtime
            .search_equal_fact_proof(
                &fact,
                VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::Direct),
            )
            .unwrap()
            .expect("identity truth proof");
        let EqualFactSearchedProof::ByTheyAreTheSame(proof) = proof else {
            panic!("identity must own its route: {code}");
        };
        assert!(matches!(
            (shape, proof),
            ("ir", TheyAreTheSameProof::SameIr(_))
                | (
                    "fn",
                    TheyAreTheSameProof::SameFreeParamShape(SameFreeParamShapeProof::FnSet(_))
                )
                | (
                    "anon",
                    TheyAreTheSameProof::SameFreeParamShape(SameFreeParamShapeProof::AnonymousFn(
                        _
                    ))
                )
                | (
                    "set",
                    TheyAreTheSameProof::SameFreeParamShape(SameFreeParamShapeProof::SetBuilder(_))
                )
        ));
    }
}

#[test]
fn alpha_preserves_free_ids_carriers_conditions_and_binder_dependencies() {
    let mut runtime = runtime();
    exec_ok(&mut runtime, "have a R, b R");
    for code in [
        "fn(x R) R = fn(y R) N",
        "fn(x R) R {x + a} = fn(y R) R {y + b}",
        "{x R: x > 0} = {y R: y > 1}",
    ] {
        let result = verify(
            &mut runtime,
            code,
            VerifyState::top_level().capped_at(
                crate::execute::execute_fact_stmt::VerifyStateLevel::KnownSpecialProperty,
            ),
        );
        assert!(result.is_failed(), "must reject {code}");
    }
    // Source dependencies now fail in parse. Construct the forbidden AST
    // explicitly to keep the alpha leaf and WD boundary independently tested.
    for code in [
        "fn(u R, v {u}) R = fn(w R, z {w}) R",
        "fn(u R, v {u}) R = fn(w R, z {0}) R",
    ] {
        let blocks = Tokenizer::new()
            .tokenize(code, runtime.current_file.clone())
            .unwrap();
        assert!(runtime.parse(&blocks).is_err(), "{code}");
    }
    let mut dependent = equal(&mut runtime, "fn(u R, v R) R = fn(w R, z R) R");
    for endpoint in [&mut dependent.left, &mut dependent.right] {
        let crate::ast::obj::Obj::FunctionSpace(crate::ast::obj::FunctionSpace::FnSet(signature)) =
            endpoint
        else {
            panic!("fn set")
        };
        let binder = &signature.set_bound_parameters.groups[0].params[0];
        signature.set_bound_parameters.groups[1].param_type =
            Box::new(crate::ast::obj::Obj::SetFormer(
                crate::ast::obj::SetFormer::ListSet(crate::ast::obj::ListSet {
                    list: vec![Box::new(crate::ast::obj::Obj::Identifier(
                        crate::ast::obj::IdentifierObj::plain(binder.id, binder.name.clone()),
                    ))],
                }),
            ));
    }
    assert!(
        super::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same(&dependent)
            .is_some()
    );
    let VerifyFactResult::Equality(result) = runtime
        .verify_equal_fact(&dependent, VerifyState::top_level())
        .unwrap()
    else {
        panic!("equality")
    };
    assert!(matches!(
        *result,
        VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToVerifyWellDefined(_))
    ));
    let mut wrong = equal(&mut runtime, "fn(u R, v R) R = fn(w R, z {0}) R");
    wrong.left = dependent.left;
    assert!(
        super::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same(&wrong).is_none()
    );
    assert!(verify(
        &mut runtime,
        "fn(u R, v R) R {u} = fn(w R, z R) R {z}",
        VerifyState::top_level()
            .capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::KnownSpecialProperty)
    )
    .is_failed());
}

#[test]
fn same_ir_never_bypasses_well_definedness() {
    let mut runtime = runtime();
    let result = verify(&mut runtime, "1 / 0 = 1 / 0", VerifyState::top_level());
    assert!(matches!(
        result,
        VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToVerifyWellDefined(_))
    ));
}

#[test]
fn known_path_keeps_oriented_fact_ids_and_needs_no_peer_search() {
    let mut runtime = runtime();
    for code in ["have a R", "let b = a", "let c = b"] {
        exec_ok(&mut runtime, code);
    }
    let goal = equal(&mut runtime, "a = c");
    let proof = runtime
        .search_equal_fact_proof_by_equivalence_class(
            &goal,
            VerifyState::top_level()
                .capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule),
        )
        .unwrap()
        .unwrap();
    let EqualFactSearchedProofByEquivalenceClass::KnownPath(path) = proof else {
        panic!("stored path")
    };
    assert_eq!(path.path.len(), 2);
    check_path(&runtime, &path, &goal.left, &goal.right);
}

#[test]
fn stored_alpha_paths_are_available_at_level_zero_without_peer_search() {
    let mut runtime = runtime();
    for code in [
        "let a = fn(x R) R",
        "let b = a",
        "let c = fn(y R) R",
        "let d = c",
    ] {
        exec_ok(&mut runtime, code);
    }
    let goal = equal(&mut runtime, "b = d");
    let before = store_sizes(&runtime);
    let proof = runtime
        .lookup_known_obj_equality(&goal.left, &goal.right)
        .unwrap();
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::AlphaPaths(proof),
    ) = proof
    else {
        panic!("finite alpha path")
    };
    assert_eq!(proof.left_path.path.len(), 2);
    assert_eq!(proof.right_path.path.len(), 2);
    check_path(&runtime, &proof.left_path, &goal.left, &proof.left);
    check_path(&runtime, &proof.right_path, &proof.right, &goal.right);
    assert!(matches!(
        proof.identity,
        TheyAreTheSameProof::SameFreeParamShape(_)
    ));
    assert_eq!(
        store_sizes(&runtime),
        before,
        "search must not store bridge or WD"
    );
    assert!(runtime
        .equivalence_class_path(&goal.left, &goal.right)
        .is_none());
}

#[test]
fn peer_builtin_inherits_permission_and_handles_both_orientations() {
    for code in ["a = x^2-1", "x^2-1 = a"] {
        let mut runtime = runtime();
        exec_ok(&mut runtime, "have x R");
        exec_ok(&mut runtime, "let a = (x+1)*(x-1)");
        let goal = equal(&mut runtime, code);
        let before = store_sizes(&runtime);
        assert!(
            runtime
                .search_equal_fact_proof_by_equivalence_class(
                    &goal,
                    VerifyState::top_level().capped_at(
                        crate::execute::execute_fact_stmt::VerifyStateLevel::KnownSpecialProperty
                    ),
                )
                .unwrap()
                .is_none(),
            "known-only must not enable builtin entry"
        );
        let proof = runtime
            .search_equal_fact_proof_by_equivalence_class(&goal, VerifyState::top_level())
            .unwrap()
            .unwrap();
        let EqualFactSearchedProofByEquivalenceClass::ViaPeers(proof) = proof else {
            panic!("peer bridge")
        };
        assert!(matches!(
            *proof.bridge.searched_proof,
            EqualFactSearchedProof::ByBuiltinRule(_)
        ));
        check_path(
            &runtime,
            &proof.left_path,
            &goal.left,
            &proof.bridge.fact.left,
        );
        check_path(
            &runtime,
            &proof.right_path,
            &proof.bridge.fact.right,
            &goal.right,
        );
        assert_eq!(store_sizes(&runtime), before);
    }
}

#[test]
fn matching_inside_a_bridge_cannot_expand_another_peer() {
    let mut runtime = runtime();
    for code in [
        "have f fn(t R) R",
        "let x = 1 + 1",
        "let y = 2",
        "let a = f(x)",
        "let b = f(y)",
    ] {
        exec_ok(&mut runtime, code);
    }
    let goal = equal(&mut runtime, "a = b");
    let before = store_sizes(&runtime);
    assert!(runtime
        .search_equal_fact_proof_by_equivalence_class(&goal, VerifyState::top_level())
        .unwrap()
        .is_none());
    assert_eq!(store_sizes(&runtime), before);
    // Explicitly storing the missing child equality now permits constructor
    // matching, without teaching the bridge to recurse through another class.
    exec_ok(&mut runtime, "x = y");
    let proof = runtime
        .search_equal_fact_proof_by_equivalence_class(&goal, VerifyState::top_level())
        .unwrap()
        .unwrap();
    let EqualFactSearchedProofByEquivalenceClass::ViaPeers(proof) = proof else {
        panic!("peer")
    };
    assert!(matches!(
        *proof.bridge.searched_proof,
        EqualFactSearchedProof::ByMatchingOneArgByOne(_)
    ));
}

#[test]
fn peer_child_permissions_cannot_reenter_the_peer_stage() {
    use crate::execute::execute_fact_stmt::VerifyStateLevel::*;
    let state = VerifyState::top_level().for_premises(Strategy).unwrap();
    for child in [
        state,
        state.for_premises(BuiltinRule).unwrap(),
        state.capped_at(Direct),
    ] {
        assert!(!child.allows(Strategy));
        assert!(child.after_rewrite().is_none());
        assert!(child.level() <= state.level());
    }
}

#[test]
fn membership_cites_finite_alpha_endpoints_in_both_wd_and_truth() {
    let mut runtime = runtime();
    exec_ok(&mut runtime, "let g = fn(x R) R");
    exec_ok(&mut runtime, "have fn f(t R) R = t");
    let result = exec_ok(&mut runtime, "f $in g");
    let json = project_stmt_detailed(&result, &runtime).stringify();
    for marker in [
        "by_equivalence_class",
        "alpha_endpoints",
        "by_they_are_the_same",
        "same_free_param_shape",
        "fn_set",
        "cite_fact_id",
        "right_identity",
        "well_defined",
    ] {
        assert!(json.contains(marker), "missing {marker} in {json}");
    }
    assert!(!json.contains("ByEqualToObjWithFreeParamsLookup"));
    assert!(!json.contains("via_peers"));
    assert!(exec(&mut runtime, "f $in fn(t R) N").is_failed());
}

#[test]
fn normal_identity_output_is_not_a_builtin_in_either_language() {
    for language in [OutputLanguage::English, OutputLanguage::Chinese] {
        let mut runtime = Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language,
        });
        let result = exec_ok(&mut runtime, "fn(x R) R = fn(y R) R");
        let json = project_stmt_normal(&result, &runtime).stringify();
        let expected = match language {
            OutputLanguage::English => "they_are_the_same",
            OutputLanguage::Chinese => "同一对象",
            _ => unreachable!("this regression checks the original English and Chinese outputs"),
        };
        assert!(json.contains(expected), "{json}");
        assert!(!json.contains("builtin_rule") && !json.contains("内置规则"));
    }
}

#[test]
fn builtin_ceiling_keeps_identity_calculation_and_stored_alpha_paths() {
    use crate::execute::execute_fact_stmt::VerifyStateLevel;
    for (code, expected) in [
        ("fn(x R) R = fn(y R) R", "identity"),
        ("1 + 1 = 2", "calculation"),
        ("g = h", "class"),
    ] {
        let mut runtime = runtime();
        exec_ok(&mut runtime, "let g = fn(x R) R");
        exec_ok(&mut runtime, "let h = fn(y R) R");
        let goal = Fact::AtomicFact(AtomicFact::EqualFact(equal(&mut runtime, code)));
        let VerifyFactResult::Equality(result) = runtime
            .verify_fact(
                &goal,
                VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule),
            )
            .unwrap()
        else {
            panic!("equality")
        };
        let VerifyEqualityResult::Success(success) = *result else {
            panic!("{code}")
        };
        assert!(matches!(
            (expected, success.searched_proof),
            ("identity", EqualFactSearchedProof::ByTheyAreTheSame(_))
                | (
                    "calculation",
                    EqualFactSearchedProof::ByClosedCalculation(_)
                )
                | ("class", EqualFactSearchedProof::ByEquivalenceClass(_))
        ));
    }
}

#[test]
fn explicit_definition_chain_stores_endpoint_before_later_verification() {
    let mut runtime = runtime();
    exec_ok(&mut runtime, "have x R = 2");
    exec_ok(&mut runtime, "have y R = x + 1");
    // Even with builtin entry enabled, definition residuals must keep rewrite disabled.
    let mut state = VerifyState::top_level();
    state = VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule);
    assert!(verify(&mut runtime, "y = 3", state).is_failed());

    exec_ok(&mut runtime, "y = x + 1 = 3");
    for code in ["y = 3", "3 = y"] {
        let goal = equal(&mut runtime, code);
        let path = runtime
            .equivalence_class_path(&goal.left, &goal.right)
            .unwrap();
        assert_eq!(
            path.len(),
            1,
            "chain must store its endpoint equality directly"
        );
        let stored = KnownEqualityPathProof::new(path);
        check_path(&runtime, &stored, &goal.left, &goal.right);
        let before = store_sizes(&runtime);
        let state = VerifyState::top_level()
            .capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::KnownSpecialProperty)
            .capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule);
        let VerifyEqualityResult::Success(success) = verify(&mut runtime, code, state) else {
            panic!("stored endpoint must need no calculation or rewrite");
        };
        assert!(matches!(
            success.searched_proof,
            EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(_)
            )
        ));
        assert_eq!(store_sizes(&runtime), before);
    }
    exec_ok(&mut runtime, "y^2 = 9");
    exec_ok(&mut runtime, "x + y = 5");
}

#[test]
fn failed_definition_chain_does_not_store_its_endpoint() {
    let mut runtime = runtime();
    exec_ok(&mut runtime, "have x R = 2");
    exec_ok(&mut runtime, "have y R = x + 1");
    let before = store_sizes(&runtime);
    assert!(exec(&mut runtime, "y = x + 1 = 4").is_failed());
    assert_eq!(store_sizes(&runtime), before, "failed chain must roll back");
    let goal = equal(&mut runtime, "y = 4");
    assert!(runtime
        .equivalence_class_path(&goal.left, &goal.right)
        .is_none());
    assert!(verify(&mut runtime, "y = 4", VerifyState::top_level()).is_failed());
}

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn parse(runtime: &mut Runtime, code: &str) -> Stmt {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .unwrap();
    let mut stmts = runtime.parse(&tokens).unwrap();
    assert_eq!(stmts.len(), 1, "{code}");
    stmts.remove(0)
}

fn exec(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let stmt = parse(runtime, code);
    runtime.exec_stmt(&stmt).unwrap()
}

fn exec_ok(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let result = exec(runtime, code);
    assert!(!result.is_failed(), "setup/goal failed: {code}");
    result
}

fn equal(runtime: &mut Runtime, code: &str) -> EqualFact {
    let Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(fact))) = parse(runtime, code) else {
        panic!("equality: {code}")
    };
    fact
}

fn verify(runtime: &mut Runtime, code: &str, state: VerifyState) -> VerifyEqualityResult {
    let goal = equal(runtime, code);
    let VerifyFactResult::Equality(result) = runtime.verify_equal_fact(&goal, state).unwrap()
    else {
        panic!("equality result")
    };
    *result
}

fn store_sizes(runtime: &Runtime) -> Vec<(usize, usize, usize)> {
    runtime
        .execution_environments_stack
        .iter()
        .map(|env| {
            (
                env.facts.facts_by_id.len(),
                env.facts
                    .known_equivalence_classes
                    .generating_edges
                    .values()
                    .map(Vec::len)
                    .sum(),
                env.well_defined_objects.object_to_wd_id.len(),
            )
        })
        .collect()
}

fn check_path(
    runtime: &Runtime,
    proof: &KnownEqualityPathProof,
    from: &crate::ast::obj::Obj,
    to: &crate::ast::obj::Obj,
) {
    let mut cursor = from.ir();
    for (left, right, id) in &proof.path {
        assert_eq!(cursor, left.ir());
        let Some(Fact::AtomicFact(AtomicFact::EqualFact(cited))) = runtime.fact_by_id_in_stack(*id)
        else {
            panic!("missing equality cite")
        };
        assert!(
            (cited.left.ir() == left.ir() && cited.right.ir() == right.ir())
                || (cited.left.ir() == right.ir() && cited.right.ir() == left.ir())
        );
        cursor = right.ir();
    }
    assert_eq!(cursor, to.ir());
}

#[test]
fn compound_alpha_identity_preserves_ranges_bodies_and_free_ids_at_builtin_disabled() {
    let mut rt = runtime();
    let state =
        VerifyState::new(crate::execute::execute_fact_stmt::VerifyStateLevel::KnownSpecialProperty);
    let fact = equal(
        &mut rt,
        "sum(1, 2, fn(x Z) R {x}) = sum(1, 2, fn(y Z) R {y})",
    );
    assert!(rt
        .search_equal_fact_proof(&fact, state.clone())
        .unwrap()
        .is_some());
    exec_ok(&mut rt, "have a R, b R");
    for code in [
        "sum(1, 2, fn(x Z) R {x}) = sum(1, 3, fn(y Z) R {y})",
        "sum(1, 2, fn(x Z) R {x}) = sum(1, 2, fn(y Z) R {y + 1})",
        "sum(1, 2, fn(x Z) R {x}) = sum(1, 2, fn(y N) R {y})",
        "sum(1, 2, fn(x Z) R {x + a}) = sum(1, 2, fn(y Z) R {y + b})",
    ] {
        let fact = equal(&mut rt, code);
        assert!(
            rt.search_equal_fact_proof(&fact, state.clone())
                .unwrap()
                .is_none(),
            "{code}"
        );
    }
}

#[test]
fn stored_sum_equality_is_reused_with_alpha_renamed_endpoints() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have a R, b R");
    exec_ok(&mut rt, "axiom stored:\n    ? forall u, v R:\n        sum(1, 2, fn(x Z) R {x + u}) = sum(1, 2, fn(y Z) R {y + v})");
    exec_ok(&mut rt, "release thm stored(a, b)");
    let goal = "sum(1, 2, fn(k Z) R {k + a}) = sum(1, 2, fn(t Z) R {t + b})";
    let VerifyEqualityResult::Success(success) = verify(&mut rt, goal, VerifyState::top_level())
    else {
        panic!("stored alpha endpoints");
    };
    let EqualFactSearchedProof::ByEquivalenceClass(
        EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(p),
    ) = success.searched_proof
    else {
        panic!("must cite checked equality");
    };
    assert!(rt.fact_by_id_in_stack(p.cited.fact_id).is_some());
    assert!(!verify(
        &mut rt,
        "sum(1, 2, fn(k Z) R {k + b}) = sum(1, 2, fn(t Z) R {t + a})",
        VerifyState::top_level()
    )
    .is_failed());
    for goal in [
        "sum(1, 3, fn(k Z) R {k + a}) = sum(1, 2, fn(t Z) R {t + b})",
        "sum(1, 2, fn(k Z) R {k + a}) = sum(1, 2, fn(t Z) R {t + a + 1})",
    ] {
        assert!(
            verify(&mut rt, goal, VerifyState::top_level()).is_failed(),
            "{goal}"
        );
    }
}
