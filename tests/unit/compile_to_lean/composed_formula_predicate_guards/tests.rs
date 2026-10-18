use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    AnonymousFnBodyInReturnSetProof, AnonymousFnObjWellDefinedProof, FnObjDomainFnSetEvidence,
    FnObjObjWellDefinedProof,
};
use crate::execute::execute_by_stmt::ExecByDefStmtResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rewrite::{
    AtomicExceptEqualityFactSearchProofByBuiltinRewrite,
    AtomicExceptEqualityFactSearchProofByClosedNumericEqualSubstitution,
    AtomicExceptEqualityFactSearchProofByFnApplicationUnfoldSubstitution,
};
use crate::execute::{
    ExecDefPropStmtResult, ExecHaveFnEqualStmtResult, ExecHaveFnEqualStmtSuccessResult,
};
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::{
    EqualitySearchProofByFnApplicationObjectDefinition,
    by_parent_checked_beta::{ByParentCheckedBetaObjectDefinitionProof, ParentCheckedBetaFunctionBody, ParentCheckedBetaOneSideProof, ParentEqualitySide},
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::EqualitySearchProofByObjectDefinition;

const COMPOSED: &str = "have fn shift(x R) R = x + 1\nhave fn pair_sum(x,y R) R = x + y\nhave fn composed(x R) R = pair_sum(shift(x),shift(x))\ncomposed(2) = 6\n";
const GUARDED: &str = "prop Pnonzero(x R):\n    x != 0\nhave fn reciprocal_guard(x R: $Pnonzero(x)) R = 1 / x\n$Pnonzero(2)\nreciprocal_guard(2) = 1 / 2\n";
const NESTED_GUARD: &str = "have fn shift(x R) R = x + 1\nprop Pnonzero(x R):\n    x != 0\nhave fn guarded_pair(a,b R: $Pnonzero(shift(b))) R = a / shift(b)\n$Pnonzero(shift(1))\nguarded_pair(6,1) = 3\n";
const ALIASES: &str = "have NumericDomain set = R\nlet NumericRange = NumericDomain\nhave fn alias_identity(x NumericDomain) NumericRange = x\nalias_identity(2) = 2\nprop alias_nonzero(x NumericDomain):\n    x != 0\nhave fn alias_reciprocal(x NumericRange: $alias_nonzero(x)) NumericDomain = 1 / x\nby def $alias_nonzero(2)\nalias_reciprocal(2) = 1 / 2\n";
const CHAIN_PREDICATE: &str = "prop bounded(x R):\n    0 < x < 1\nhave fn bounded_inv(x R: $bounded(x)) R = 1 / x\nby def $bounded(1 / 2)\nbounded_inv(1 / 2) = 2\n";
const AND_PREDICATE: &str = "prop conjunction_guard(x R):\n    x != 0 and x = x\nhave fn conjunction_inv(x R: $conjunction_guard(x)) R = 1 / x\nby def $conjunction_guard(2)\nconjunction_inv(2) = 1 / 2\n";

fn function(statement: &mut ExecStmtResult) -> &mut ExecHaveFnEqualStmtSuccessResult {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::HaveFnEqual(
            ExecHaveFnEqualStmtResult::Success(proof),
        )) => proof,
        _ => panic!("actual successful formula declaration"),
    }
}

fn anonymous(statement: &mut ExecStmtResult) -> &mut AnonymousFnObjWellDefinedProof {
    match &mut function(statement).anonymous_fn_well_defined {
        VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::FunctionSpace(
                    FunctionSpaceObjWellDefinedProofByDef::AnonymousFn(proof),
                ),
            ..
        }) => proof,
        _ => panic!("actual defining formula WD"),
    }
}

fn body_call(statement: &mut ExecStmtResult) -> &mut FnObjObjWellDefinedProof {
    match anonymous(statement).body_well_defined.as_mut() {
        ObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(proof),
            ..
        } => proof,
        _ => panic!("actual outer call in the composed formula body"),
    }
}

fn nested_guard_unfold(
    statement: &mut ExecStmtResult,
) -> &mut AtomicExceptEqualityFactSearchProofByFnApplicationUnfoldSubstitution {
    let proof = super::fact_statement_mut(statement);
    let checked = super::atomic_proof_mut(&mut proof.verify_result);
    assert!(matches!(checked.fact, AtomicFact::NormalAtomicFact(_)));
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::FnApplicationUnfoldSubstitution(
            unfold,
        ),
    ) = &mut checked.searched_proof
    else {
        panic!("actual selected outer concrete-predicate function-unfold route")
    };
    unfold
}

fn parent_checked_beta(statement: &mut ExecStmtResult) -> &mut ParentCheckedBetaOneSideProof {
    let proof = super::fact_statement_mut(statement);
    let EqualFactSearchedProof::ByObjectDefinition(
        EqualitySearchProofByObjectDefinition::ByFnApplication(
            EqualitySearchProofByFnApplicationObjectDefinition::ParentCheckedBeta(
                ByParentCheckedBetaObjectDefinitionProof::OneSide(beta),
            ),
        ),
    ) = &mut super::equality_proof_mut(&mut proof.verify_result).searched_proof
    else {
        panic!("actual selected parent-checked beta result")
    };
    beta
}

#[test]
fn composed_formula_predicate_guards_replay_the_original_parent_checked_beta() {
    let (mut result, compiler) = super::execute(ALIASES);
    let beta = parent_checked_beta(&mut result.statement_results[3]);
    assert!(matches!(
        beta.function_body,
        ParentCheckedBetaFunctionBody::KnownAnonymousFunction { .. }
    ));
    assert_eq!(beta.residual_equal.left.ir(), beta.expanded_body.ir());
    let output = super::compile_run(&result, &compiler, "actual_parent_beta").unwrap();
    assert!(output.contains("Litex.FunctionSemantics.call_graphValue"));
}

#[test]
fn composed_formula_predicate_guards_reject_corrupted_parent_checked_beta_evidence() {
    for change in [
        "side", "expanded", "residual", "domain", "body", "path", "citation",
    ] {
        let (mut result, compiler) = super::execute(ALIASES);
        let beta = parent_checked_beta(&mut result.statement_results[3]);
        match change {
            "side" => beta.parent_well_defined_side = ParentEqualitySide::Right,
            "expanded" => beta.expanded_body = super::number_object("7"),
            "residual" => beta.residual_equal.right = super::number_object("7"),
            _ => {
                let ParentCheckedBetaFunctionBody::KnownAnonymousFunction {
                    function,
                    function_equal,
                    checked_domain,
                } = &mut beta.function_body
                else {
                    panic!("actual selected named body")
                };
                match change {
                    "domain" => checked_domain.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
                    "body" => function.equal_to = Box::new(super::number_object("7")),
                    "path" => function_equal.path.clear(),
                    "citation" => function_equal.path[0].2 = FactId::new(u64::MAX),
                    _ => unreachable!(),
                }
            }
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["FunctionDefinition/", "Equality/", "FactId/"],
        );
    }
}

#[test]
fn composed_formula_predicate_guards_replay_owned_calls_and_closed_evaluations() {
    for source in [COMPOSED, GUARDED, NESTED_GUARD, ALIASES] {
        let (result, compiler) = super::execute(source);
        let output = super::compile_run(&result, &compiler, "composed_formula")
            .expect("the original formula/guard/alias evidence replays completely");
        assert!(output.contains("Litex.formulaFn"));
        assert!(!output.contains("sorry") && !output.contains("admit"));
    }
}

#[test]
fn composed_formula_predicate_guards_keep_the_original_constructor_shapes() {
    let (mut result, compiler) = super::execute(COMPOSED);
    let proof = body_call(&mut result.statement_results[2]);
    assert_eq!(proof.child_obj_well_defined.len(), 2);
    assert_eq!(proof.requirement_fact_verified.len(), 2);
    assert!(matches!(
        proof.domain_fn_set,
        Some(FnObjDomainFnSetEvidence::InFunctionSet { .. })
    ));
    let output = super::compile_run(&result, &compiler, "owned_composed_shape").unwrap();
    assert!(output.contains("Litex.formulaFn2 (M := M)"));
    assert!(output.contains("Litex.FunctionSignature.two (M := M)"));
    assert!(output.contains("Litex.FunctionSemantics.callValue"));
    // Multiple source arguments form a complete indexed tuple; pairValue is
    // reserved for graph edges, not the observable function input.
    assert!(output.contains("Litex.FiniteFunction.tupleValue (M := M) !["));
    assert!(!output.contains("Litex.FunctionSemantics.pairValue"));
    assert!(output.contains("Litex.call2"));
}

#[test]
fn composed_formula_predicate_guards_reject_missing_wrong_or_reordered_body_call_evidence() {
    for change in ["domain", "members", "children", "wrong_child", "wrong_id"] {
        let (mut result, compiler) = super::execute(COMPOSED);
        let proof = body_call(&mut result.statement_results[2]);
        match change {
            "domain" => proof.domain_fn_set = None,
            "members" => proof.requirement_fact_verified.clear(),
            "children" => proof.child_obj_well_defined.clear(),
            "wrong_child" => super::replace_wd_subject(
                &mut proof.child_obj_well_defined[0],
                super::number_object("7"),
            ),
            "wrong_id" => match proof.domain_fn_set.as_mut().unwrap() {
                FnObjDomainFnSetEvidence::InFunctionSet { fact_id, .. } => {
                    *fact_id = FactId::new(u64::MAX)
                }
                _ => panic!("actual preceding function-set citation"),
            },
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["WD/", "FactId/", "Function/"]);
    }
}

#[test]
fn composed_formula_predicate_guards_reject_a_removed_or_future_function_declaration() {
    for change in ["removed", "future"] {
        let (mut result, compiler) = super::execute(COMPOSED);
        if change == "removed" {
            result.statement_results.remove(0);
        } else {
            let declaration = result.statement_results.remove(0);
            result.statement_results.insert(2, declaration);
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["Function/", "Identifier/", "FactId/", "WD/"],
        );
    }
}

#[test]
fn composed_formula_predicate_guards_reject_a_removed_or_future_predicate_definition() {
    for change in ["removed", "future"] {
        let (mut result, compiler) = super::execute(GUARDED);
        if change == "removed" {
            result.statement_results.remove(0);
        } else {
            let declaration = result.statement_results.remove(0);
            result.statement_results.insert(1, declaration);
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["Prop/", "WD/", "FactId/", "Function/"],
        );
    }
}

#[test]
fn composed_formula_predicate_guards_reject_missing_or_wrong_assumed_guard_subjects() {
    for change in ["missing", "wrong_argument", "wrong_predicate"] {
        let (mut result, compiler) = super::execute(GUARDED);
        let proof = anonymous(&mut result.statement_results[1]);
        match change {
            "missing" => proof.assumed_dom_facts.clear(),
            "wrong_argument" | "wrong_predicate" => {
                match &mut proof.assumed_dom_facts[0].store_and_infer.store {
                    StoreFactResult::AtomicFact(stored) => match &mut stored.fact {
                        AtomicFact::NormalAtomicFact(normal) => {
                            if change == "wrong_argument" {
                                normal.body[0] = super::number_object("7");
                            } else {
                                normal.predicate = AtomicName::Plain {
                                    name: "another_predicate".to_string(),
                                };
                            }
                        }
                        _ => panic!("actual predicate guard assumption"),
                    },
                    _ => panic!("actual atomic guard store"),
                }
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["Function/", "Store/", "WD/", "Prop/"],
        );
    }
}

#[test]
fn composed_formula_predicate_guards_reject_a_wrong_nested_call_domain_requirement() {
    let (mut result, compiler) = super::execute(COMPOSED);
    let proof = body_call(&mut result.statement_results[2]);
    let membership = super::atomic_proof_mut(&mut proof.requirement_fact_verified[0]);
    match &mut membership.fact {
        AtomicFact::InFact(member) => member.set = Obj::StandardSet(StandardSet::N),
        _ => panic!("actual nested result membership"),
    }
    super::phase2_rejected(
        &result,
        &compiler,
        "wrong_nested_member",
        &["WD/FnObj/ParameterMembership"],
    );
}

#[test]
fn composed_formula_predicate_guards_reject_a_wrong_recorded_return_membership() {
    let (mut result, compiler) = super::execute(COMPOSED);
    let AnonymousFnBodyInReturnSetProof::CheckedMembership(member) =
        &mut anonymous(&mut result.statement_results[2]).body_in_ret_set
    else {
        panic!("actual checked formula return membership")
    };
    match &mut super::atomic_proof_mut(member).fact {
        AtomicFact::InFact(member) => member.set = Obj::StandardSet(StandardSet::N),
        _ => panic!("actual return fact"),
    }
    super::phase2_rejected(
        &result,
        &compiler,
        "wrong_return",
        &["Function/ReturnSubject"],
    );
}

#[test]
fn composed_formula_predicate_guards_reject_a_removed_or_future_numeric_alias() {
    for change in ["removed", "future"] {
        let (mut result, compiler) = super::execute(ALIASES);
        if change == "removed" {
            result.statement_results.remove(0);
        } else {
            let declaration = result.statement_results.remove(0);
            result.statement_results.insert(2, declaration);
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["Function/", "Identifier/", "WD/", "FactId/", "WdId/"],
        );
    }
}

#[test]
fn composed_formula_predicate_guards_reject_wrong_alias_constructor_capture() {
    let (mut result, compiler) = super::execute(ALIASES);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
        ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(alias)),
    )) = &mut result.statement_results[0]
    else {
        panic!("actual numeric carrier alias declaration")
    };
    match &mut alias.equal_to_well_defined[0] {
        VerifyObjWellDefinedResult::Success(wd) => {
            super::replace_wd_subject(wd, Obj::StandardSet(StandardSet::N))
        }
        _ => panic!("actual numeric carrier RHS formation"),
    }
    super::phase2_rejected(&result, &compiler, "wrong_alias_wd", &["WD/"]);
}

#[test]
fn composed_formula_predicate_guards_reject_wrong_predicate_signature_identity() {
    let (mut result, compiler) = super::execute(GUARDED);
    let proof = anonymous(&mut result.statement_results[1]);
    let FactWellDefinedProof::AtomicExceptEquality(guard) =
        &mut proof.assumed_dom_facts[0].well_defined
    else {
        panic!("actual predicate guard WD")
    };
    match &mut guard.predicate_signature {
        PredicateSignatureWellDefinedProof::Prop { predicate, .. } => {
            *predicate = AtomicName::Plain {
                name: "other".to_string(),
            }
        }
        _ => panic!("actual concrete predicate signature"),
    }
    super::phase2_rejected(
        &result,
        &compiler,
        "wrong_predicate_id",
        &["Prop/Signature"],
    );
}

#[test]
fn composed_formula_predicate_guards_reject_changed_function_binder_identity() {
    // Only the binder identity changes. Original parameter stores, carrier WD,
    // body WD, memberships and every captured FactId remain intact.
    for align_wd_subject in [false, true] {
        let (mut result, compiler) = super::execute(COMPOSED);
        let proof = function(&mut result.statement_results[0]);
        proof
            .statement
            .equal_to_anonymous_fn
            .body
            .set_bound_parameters
            .groups[0]
            .params[0]
            .id = IdentifierId::new(u64::MAX);
        if align_wd_subject {
            // Keep the three captured signature copies equal to reach the
            // original parameter-store subject check instead of WD/Subject.
            let anonymous_source = proof.statement.equal_to_anonymous_fn.clone();
            let signature_source = anonymous_source.body.clone();
            let VerifyObjWellDefinedResult::Success(anonymous_wd) =
                &mut proof.anonymous_fn_well_defined
            else {
                panic!("actual anonymous function formation")
            };
            super::replace_wd_subject(
                anonymous_wd,
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(anonymous_source)),
            );
            let VerifyObjWellDefinedResult::Success(signature_wd) = &mut proof.fn_set_well_defined
            else {
                panic!("actual function signature formation")
            };
            super::replace_wd_subject(
                signature_wd,
                Obj::FunctionSpace(FunctionSpace::FnSet(signature_source)),
            );
        }
        let error = super::compile_run(&result, &compiler, "wrong_function_binder")
            .expect_err("changed declaration binder must reject unchanged original evidence");
        assert_eq!(
            error.route,
            if align_wd_subject {
                "Function/ParameterSubject"
            } else {
                "WD/Subject"
            },
        );
    }
}

#[test]
fn composed_formula_predicate_guards_reject_changed_concrete_prop_binder_identity() {
    let (mut result, compiler) = super::execute(GUARDED);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        ExecDefPropStmtResult::Success(proof),
    )) = &mut result.statement_results[0]
    else {
        panic!("actual concrete predicate declaration")
    };
    // Preserve original member stores and all body WD/evidence; only the
    // source declaration binder differs from its recorded introduction.
    proof.statement.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX);
    let error = super::compile_run(&result, &compiler, "wrong_concrete_prop_binder")
        .expect_err("changed declaration binder must reject unchanged original evidence");
    assert_eq!(error.route, "Prop/ParameterSubject");
}

#[test]
fn composed_formula_predicate_guards_keep_false_guards_rejected_by_the_source() {
    for source in [
        "prop Pnonzero(x R):\n    x != 0\nhave fn reciprocal_guard(x R: $Pnonzero(x)) R = 1 / x\nreciprocal_guard(0) = 0\n",
        "have fn recursive_formula(x R) R=recursive_formula(x)\n",
    ] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.to_string()])
                .unwrap();
        let mut runtime = Runtime::new(command);
        let result = runtime.run_litex_code(source).unwrap();
        assert!(!result.success && result.session_error.is_none(), "{source}");
        let compiler = super::LitexToLeanCompiler::new(runtime);
        assert_eq!(
            super::compile_run(&result, &compiler, "false_guard")
                .unwrap_err()
                .route,
            "source_failed"
        );
    }
}

#[test]
fn composed_formula_predicate_guards_replay_flat_chain_and_conjunction_clauses() {
    for source in [
        CHAIN_PREDICATE,
        AND_PREDICATE,
        "have fn direct_range(x R: 0 < x < 1) R = 1 / x\ndirect_range(1 / 2) = 2\n",
        "have fn direct_conjunction(x R: x != 0 and x = x) R = 1 / x\ndirect_conjunction(2) = 1 / 2\n",
    ] {
        let (result, compiler) = super::execute(source);
        let output = super::compile_run(&result, &compiler, "flat_predicate_clauses")
            .expect("the original compound clauses, guards and projected facts replay in order");
        assert!(!output.contains("sorry") && !output.contains("admit"));
    }
}

#[test]
fn composed_formula_predicate_guards_reject_wrong_or_reordered_compound_definition_stores() {
    for source in [CHAIN_PREDICATE, AND_PREDICATE] {
        let (mut result, compiler) = super::execute(source);
        let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
            ExecDefPropStmtResult::Success(proof),
        )) = &mut result.statement_results[0]
        else {
            panic!("actual concrete compound definition")
        };
        match &mut proof.assumed_iff_facts[0].store_and_infer.store {
            StoreFactResult::ChainFact(stored) => stored.adjacent.swap(0, 1),
            StoreFactResult::AndFact(stored) => stored.components.swap(0, 1),
            _ => panic!("actual compound defining-clause store"),
        }
        super::phase2_rejected(
            &result,
            &compiler,
            "reordered_compound_definition",
            &["Store/", "Chain/", "And/", "Compound/"],
        );
    }
}

#[test]
fn composed_formula_predicate_guards_reject_missing_compound_guard_capture() {
    let source = "have fn direct_range(x R: 0 < x < 1) R = 1 / x\n";
    let (mut result, compiler) = super::execute(source);
    let proof = anonymous(&mut result.statement_results[0]);
    match &mut proof.assumed_dom_facts[0].well_defined {
        FactWellDefinedProof::ChainFact { adjacent } => adjacent.clear(),
        _ => panic!("actual chain guard formation"),
    }
    super::phase2_rejected(
        &result,
        &compiler,
        "deleted_chain_guard_formation",
        &["WD/", "Chain/"],
    );
}

#[test]
fn composed_formula_predicate_guards_keep_the_original_compound_clause_ids() {
    let (result, compiler) = super::execute(CHAIN_PREDICATE);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
        ExecDefPropStmtResult::Success(proof),
    )) = &result.statement_results[0]
    else {
        panic!("actual chain predicate definition")
    };
    let clause = &proof.statement.iff_facts[0];
    let clause_id = clause.fact_id();
    let assumed = &proof.assumed_iff_facts[0].store_and_infer;
    assert_eq!(assumed.primary_fact_id(), clause_id);
    let StoreFactResult::ChainFact(stored) = &assumed.store else {
        panic!("actual defining-clause chain store")
    };
    assert_eq!(Fact::ChainFact(stored.fact.clone()), *clause);
    assert_eq!(stored.whole_fact_id, clause_id);
    assert_eq!(stored.adjacent.len(), stored.fact.prop_names.len());
    for component in &stored.adjacent {
        assert_eq!(component.fact_id, component.fact.fact_id());
        assert_eq!(
            component.fact,
            crate::compile_to_lean::compile_compound_fact::chain_edge(
                &stored.fact,
                component.edge_index,
                component.fact_id,
            )
            .unwrap(),
        );
    }
    // The final defining clause is the proposition itself, not a published
    // assumption theorem. Inspect the original caller's completed producers.
    let ExecStmtResult::By(ExecByStmtResult::Def(ExecByDefStmtResult::Success(caller))) =
        &result.statement_results[2]
    else {
        panic!("actual explicit predicate invocation")
    };
    let ids = caller.stored.stored_fact_ids();
    let Some(crate::store_fact_and_infer::InferResult::AtomicFact(
        crate::store_fact_and_infer::InferAtomicFactResult::NormalAtomicFact(rules),
    )) = &caller.stored.infer
    else {
        panic!("actual caller predicate inference")
    };
    let derived = rules
        .iter()
        .find_map(|rule| match rule {
            crate::store_fact_and_infer::InferNormalAtomicFactResult::ExpandDefinition(proof) => {
                Some(&proof.derived)
            }
            _ => None,
        })
        .expect("actual defining-clause projection at the caller");
    assert_eq!(derived.len(), proof.statement.iff_facts.len());
    let StoreFactResult::ChainFact(published) = &derived[0].store else {
        panic!("actual caller chain projection")
    };
    let StoreFactResult::AtomicFact(predicate_store) = &caller.stored.store else {
        panic!("actual caller predicate store")
    };
    let AtomicFact::NormalAtomicFact(predicate) = &predicate_store.fact else {
        panic!("actual caller concrete predicate")
    };
    let parameters = proof
        .statement
        .typed_parameters
        .groups
        .iter()
        .flat_map(|group| &group.params)
        .collect::<Vec<_>>();
    assert_eq!(parameters.len(), predicate.body.len());
    let substitution = parameters
        .iter()
        .zip(&predicate.body)
        .map(|(parameter, argument)| (parameter.id, argument.clone()))
        .collect::<std::collections::HashMap<IdentifierId, Obj>>();
    assert!(crate::compile_to_lean::helper::instantiated_fact_matches(
        clause,
        &Fact::ChainFact(published.fact.clone()),
        &substitution,
    ));
    assert!(ids.contains(&published.whole_fact_id));
    for component in &published.adjacent {
        assert_eq!(component.fact_id, component.fact.fact_id());
        assert!(ids.contains(&component.fact_id));
    }
    let output = super::compile_run(&result, &compiler, "original_compound_ids").unwrap();
    for id in ids {
        let name = format!("h_{}", id.value());
        assert!(
            output.lines().any(|line| {
                let mut tokens = line.split_whitespace();
                matches!(tokens.next(), Some("theorem" | "have"))
                    && tokens.next() == Some(name.as_str())
            }),
            "the original completed caller producer {name} is emitted"
        );
    }
}

#[test]
fn composed_formula_predicate_guards_accept_a_long_strictly_prior_numeric_alias_chain() {
    let mut source = String::from("have Domain0 set = R\n");
    for index in 1..=70 {
        source.push_str(&format!("let Domain{index} = Domain{}\n", index - 1));
    }
    source.push_str("have fn identity(x Domain70) Domain70 = x\nidentity(2) = 2\n");
    let (result, compiler) = super::execute(&source);
    super::compile_run(&result, &compiler, "prior_numeric_aliases")
        .expect("a finite source-prefix alias chain has no additional arbitrary depth limit");
}

#[test]
fn composed_formula_predicate_guards_keep_chain_and_conjunction_guard_boundaries() {
    for source in [
        "prop bounded(x R):\n    0 < x < 1\nhave fn bounded_inv(x R: $bounded(x)) R = 1 / x\nbounded_inv(1) = 1\n",
        "prop conjunction_guard(x R):\n    x != 0 and x = x\nhave fn conjunction_inv(x R: $conjunction_guard(x)) R = 1 / x\nconjunction_inv(0) = 0\n",
    ] {
        let command = parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.to_string()]).unwrap();
        let mut runtime = Runtime::new(command);
        let result = runtime.run_litex_code(source).unwrap();
        assert!(!result.success && result.session_error.is_none());
        assert!(result.statement_results[..2].iter().all(|statement| !statement.is_failed()));
        assert!(result.statement_results[2].is_failed());
        let compiler = super::LitexToLeanCompiler::new(runtime);
        assert_eq!(super::compile_run(&result, &compiler, "invalid_compound_guard").unwrap_err().route, "source_failed");
    }
}

#[test]
fn composed_formula_predicate_guards_replay_the_actual_atomic_function_unfold() {
    let (mut result, compiler) = super::execute(NESTED_GUARD);
    let proof = nested_guard_unfold(&mut result.statement_results[3]);
    assert_eq!(proof.unfold_equal_proofs.len(), 1);
    assert_eq!(
        source_fact_id(&proof.proof_of_rewritten_fact),
        proof.rewritten_fact.fact_id()
    );
    super::compile_run(&result, &compiler, "actual_atomic_fn_unfold").unwrap();
}

fn source_fact_id(result: &VerifyFactResult) -> FactId {
    match result {
        VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof.fact.fact_id(),
            _ => panic!("actual successful residual"),
        },
        _ => panic!("actual atomic residual"),
    }
}

fn closed_order_rewrite(
    statement: &mut ExecStmtResult,
) -> &mut AtomicExceptEqualityFactSearchProofByClosedNumericEqualSubstitution {
    let proof = super::fact_statement_mut(statement);
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(proof),
    ) = &mut super::atomic_proof_mut(&mut proof.verify_result).searched_proof
    else {
        panic!("actual original x>=0 closed-numeric rewrite")
    };
    proof
}

#[test]
fn composed_formula_predicate_guards_replay_actual_order_equality_rewrite_winners() {
    let mut selected = Vec::new();
    for (goal, transport) in [
        ("x>=0", "Litex.leOfSame"),
        ("x>0", "Litex.ltOfSame"),
        ("x<=3", "Litex.leOfSame"),
        ("x<3", "Litex.ltOfSame"),
    ] {
        let source = format!("have x R=2\n{goal}\n");
        let (mut result, compiler) = super::execute(&source);
        let actual = &super::atomic_proof_mut(
            &mut super::fact_statement_mut(&mut result.statement_results[1]).verify_result,
        )
        .searched_proof;
        if matches!(
            actual,
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(
                AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(
                    _
                ) | AtomicExceptEqualityFactSearchProofByBuiltinRewrite::KnownEqualObjSubstitution(
                    _
                )
            )
        ) {
            let output = super::compile_run(&result, &compiler, "actual_order_rewrite").unwrap();
            assert!(output.contains(transport));
            selected.push(goal);
        }
    }
    assert!(
        selected.contains(&"x>=0"),
        "the original retained failing profile is exercised"
    );
}

#[test]
fn composed_formula_predicate_guards_reject_missing_wrong_order_rewrite_evidence() {
    for change in [
        "deleted_citations",
        "wrong_citation",
        "wrong_residual",
        "wrong_child",
    ] {
        let (mut result, compiler) = super::execute("have x R=2\nx>=0\n");
        let proof = closed_order_rewrite(&mut result.statement_results[1]);
        match change {
            "deleted_citations" => proof.cited_equal_fact_ids.clear(),
            "wrong_citation" => proof.cited_equal_fact_ids[0] = FactId::new(u64::MAX),
            "wrong_residual" => match &mut proof.rewritten_fact {
                Fact::AtomicFact(AtomicFact::GreaterEqualFact(fact)) => {
                    fact.left = super::number_object("7")
                }
                _ => panic!("actual same-family ordered residual"),
            },
            "wrong_child" => {
                match &mut super::atomic_proof_mut(&mut proof.proof_of_rewritten_fact).fact {
                    AtomicFact::GreaterEqualFact(fact) => fact.left = super::number_object("7"),
                    _ => panic!("actual checked order child"),
                }
            }
            _ => unreachable!(),
        }
        super::phase2_rejected(
            &result,
            &compiler,
            change,
            &["AtomicRewrite/", "FactId/", "WD/"],
        );
    }
}

#[test]
fn composed_formula_predicate_guards_reject_missing_wrong_or_extra_atomic_unfold_evidence() {
    for change in ["deleted", "wrong_endpoint", "wrong_residual"] {
        let (mut result, compiler) = super::execute(NESTED_GUARD);
        let proof = nested_guard_unfold(&mut result.statement_results[3]);
        match change {
            "deleted" => proof.unfold_equal_proofs.clear(),
            "wrong_endpoint" => {
                super::equality_proof_mut(&mut proof.unfold_equal_proofs[0])
                    .fact
                    .right = super::number_object("7")
            }
            "wrong_residual" => match &mut proof.rewritten_fact {
                Fact::AtomicFact(AtomicFact::NormalAtomicFact(fact)) => {
                    let identity = fact.fact_id;
                    let predicate = fact.predicate.clone();
                    fact.body[0] = super::number_object("7");
                    assert_eq!(fact.fact_id, identity);
                    assert_eq!(fact.predicate, predicate);
                }
                _ => panic!("actual same-predicate normal residual"),
            },
            _ => unreachable!(),
        }
        super::phase2_rejected(&result, &compiler, change, &["AtomicFnUnfold/"]);
    }
}

#[test]
fn composed_formula_predicate_guards_cannot_use_a_future_atomic_unfold_constructor_cache() {
    let source =
        format!("{NESTED_GUARD}let future_expansion = 1 + 1\nlet cached_expansion = 1 + 1\n");
    let (mut result, compiler) = super::execute(&source);
    super::compile_run(&result, &compiler, "atomic_unfold_future_wd").unwrap();
    let (object, wd_id) =
        match &super::let_definition(&result.statement_results[6]).value_well_defined {
            VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByKnown { obj, wd_id }) => {
                (obj.clone(), *wd_id)
            }
            _ => panic!("the later alias cites the future stored expansion constructor"),
        };
    let proof = nested_guard_unfold(&mut result.statement_results[3]);
    let equality = super::equality_proof_mut(&mut proof.unfold_equal_proofs[0]);
    assert_eq!(equality.fact.right.ir(), object.ir());
    let constructor = std::mem::replace(
        &mut equality.well_defined_proof.right,
        ObjWellDefinedProof::ByKnown {
            obj: object.clone(),
            wd_id,
        },
    );
    assert!(
        matches!(&constructor, ObjWellDefinedProof::ByDef { obj, .. } if obj.ir() == object.ir()),
        "the original selected equality owns this expansion constructor"
    );
    // Move that actual constructor to the later alias result. The earlier
    // unfolding now cites a real cache token whose remaining producer is future.
    super::let_definition_mut(&mut result.statement_results[5]).value_well_defined =
        VerifyObjWellDefinedResult::Success(constructor);
    super::phase2_rejected(
        &result,
        &compiler,
        "future_atomic_unfold_wd",
        &["WD/", "WdId/"],
    );
}
