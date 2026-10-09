use super::compile_run;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::AtomicExceptEqualityFactSearchProofByBuiltinRewrite;
use crate::prelude::*;

fn execute(source: &str) -> (RunLitexCodeResult, Runtime) {
    let command =
        parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.to_string()])
            .expect("strict command");
    let mut runtime = Runtime::new(command);
    let result = runtime.run_litex_code(source).expect("execute source");
    assert!(
        result.success,
        "test input must already be successfully verified"
    );
    (result, runtime)
}

#[test]
fn combined_unit_preserves_only_legal_scope_dependencies() {
    let source = "1 = 1\n$is_set(1)\n1 $in R\nforall a C:\n    a = a\nforall a R:\n    a $in C\nforall a C, b C:\n    b != 0\n    =>:\n        a / b = a / b\n";
    let (result, runtime) = execute(source);
    assert_eq!(result.statement_results.len(), 6);
    assert!(compile_run(&result, &runtime, "combined_scope").is_ok());
}

#[test]
fn selected_rational_route_uses_normalization_adapter() {
    let (result, runtime) = execute("1 = 1\nforall a C:\n    a + 0 = a\n");
    let success = forall_proof(&result.statement_results[1]);
    assert!(matches!(
        &equality_proof(&success.proved_then_facts[0].verify_result).searched_proof,
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
            EqualitySearchProofByCalculation::Rational {}
        ))
    ));
    let output = compile_run(&result, &runtime, "add_zero").expect("selected Rational adapter");
    assert!(output.contains("NativeBridge.sameOfDenoteNumber"));
    assert!(output.contains("(by ring)"));
    assert!(!output.contains("Litex.addZero"));
}

#[test]
fn unsupported_constructor_after_supported_prefix_rejects_complete_artifact() {
    let (result, runtime) = execute("1 = 1\nforall a R:\n    sin(a) + 0 = sin(a)\n");
    let error = compile_run(&result, &runtime, "unsupported_trig")
        .expect_err("trig denotation is outside the integer arithmetic adapter");
    assert_eq!(error.statement_index, Some(2));
    assert_eq!(error.route, "WD/TrigOperator");
}

#[test]
fn known_wd_requires_the_exact_recorded_subject() {
    let (mut result, runtime) = execute("1 = 1\n2 = 2\n$is_set(1)\n");
    let two = match &result.statement_results[1] {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => {
            match &success.verify_result {
                VerifyFactResult::Equality(proof) => match proof.as_ref() {
                    VerifyEqualityResult::Success(proof) => proof.fact.left.clone(),
                    VerifyEqualityResult::Failed(_) => panic!("verified equality"),
                },
                _ => panic!("equality result"),
            }
        }
        _ => panic!("successful fact"),
    };
    let other_id = runtime
        .top_exec_env()
        .well_defined_objects
        .lookup(&two)
        .expect("two's WD record");
    let success = match &mut result.statement_results[2] {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => success,
        _ => panic!("successful fact"),
    };
    let atomic = match &mut success.verify_result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_mut() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof,
            VerifyAtomicExceptEqualityFactResult::Failed(_) => panic!("verified sethood"),
        },
        _ => panic!("atomic result"),
    };
    match &mut atomic.well_defined_proof.well_defined_of_each_parameter[0] {
        ObjWellDefinedProof::ByKnown { wd_id, .. } => *wd_id = other_id,
        ObjWellDefinedProof::ByDef { .. } => panic!("sethood should reuse one's WD"),
    }
    let error = compile_run(&result, &runtime, "wrong_wd_subject")
        .expect_err("another object's cache is not this certificate");
    assert_eq!(error.route, "WD/ByKnown");
}

#[test]
fn a_missing_wd_id_is_not_recovered_from_a_true_goal() {
    let (mut result, runtime) = execute("1 = 1\n$is_set(1)\n");
    let success = match &mut result.statement_results[1] {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => success,
        _ => panic!("successful fact"),
    };
    let atomic = match &mut success.verify_result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_mut() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof,
            VerifyAtomicExceptEqualityFactResult::Failed(_) => panic!("verified sethood"),
        },
        _ => panic!("atomic result"),
    };
    match &mut atomic.well_defined_proof.well_defined_of_each_parameter[0] {
        ObjWellDefinedProof::ByKnown { wd_id, .. } => *wd_id = WellDefinednessId::new(u64::MAX),
        ObjWellDefinedProof::ByDef { .. } => panic!("sethood should reuse one's WD"),
    }
    let error = compile_run(&result, &runtime, "missing_wd_id")
        .expect_err("the cited WD identity must resolve");
    assert_eq!(error.route, "WdId/Resolution");
}

#[test]
fn closed_forall_assumptions_do_not_escape_into_the_next_forall() {
    let (mut result, runtime) = execute("forall a R:\n    a = a\nforall b R:\n    b $in C\n");
    assert!(compile_run(&result, &runtime, "valid_scopes").is_ok());
    let old_id = forall_proof_mut(&mut result.statement_results[0])
        .introduced_params
        .defined_params
        .stored_fact_ids[0];
    let second = forall_proof_mut(&mut result.statement_results[1]);
    let atomic = match &mut second.proved_then_facts[0].verify_result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_mut() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof,
            VerifyAtomicExceptEqualityFactResult::Failed(_) => panic!("verified membership"),
        },
        _ => panic!("atomic result"),
    };
    let member = match &mut atomic.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) => {
            match &mut proof.reason {
                StructuralMembershipReason::StandardSuperset(child) => child,
                _ => panic!("standard-superset route"),
            }
        }
        _ => panic!("structural membership"),
    };
    match &mut member.reason {
        StructuralMembershipReason::Known(proof) => proof.cite_fact_id = old_id,
        _ => panic!("R-membership citation"),
    }
    let error = compile_run(&result, &runtime, "escaped_scope")
        .expect_err("the earlier binder assumption is closed");
    assert_eq!(error.route, "FactId/Resolution");
}

#[test]
fn division_reflexivity_replays_nonzero_evidence_before_reflexivity() {
    let (mut result, runtime) =
        execute("forall a C, b C:\n    b != 0\n    =>:\n        a / b = a / b\n");
    assert!(compile_run(&result, &runtime, "valid_division").is_ok());
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let equality = match &mut forall.proved_then_facts[0].verify_result {
        VerifyFactResult::Equality(proof) => match proof.as_mut() {
            VerifyEqualityResult::Success(proof) => proof,
            VerifyEqualityResult::Failed(_) => panic!("verified equality"),
        },
        _ => panic!("equality result"),
    };
    match &mut equality.well_defined_proof.left {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Div(proof),
                ),
            ..
        } => {
            proof.requirement_fact_verified.remove(0);
        }
        _ => panic!("division WD by construction"),
    }
    let error = compile_run(&result, &runtime, "missing_division_requirement")
        .expect_err("reflexivity cannot skip construction legality");
    assert_eq!(error.route, "WD/Arithmetic");
}

#[test]
fn presentation_strings_do_not_determine_the_generated_proof() {
    let (mut result, runtime) = execute("1 = 1\n$is_set(1)\n");
    let original = compile_run(&result, &runtime, "presentation_independence")
        .expect("supported typed results");
    result.statement_texts = vec!["trust 1 = 2".to_string(), "unrelated display".to_string()];
    result.normal_json = Some("not a proof or even valid JSON".to_string());
    let altered = compile_run(&result, &runtime, "presentation_independence")
        .expect("presentation has no proof role");
    assert_eq!(original, altered);
}

#[test]
fn live_wd_cache_does_not_replace_a_missing_replayed_producer() {
    let (mut result, runtime) = execute("1 = 1\n$is_set(1)\n");
    assert!(compile_run(&result, &runtime, "complete_producers").is_ok());
    result.statement_results.remove(0);
    let error = compile_run(&result, &runtime, "missing_constructor")
        .expect_err("the live cache contains a subject, not an emitted proof");
    assert_eq!(error.route, "WD/Producer");
}

#[test]
fn known_membership_replays_all_argument_identity_evidence() {
    let (mut result, runtime) = execute("forall a R:\n    a $in C\n");
    assert!(compile_run(&result, &runtime, "complete_argument_evidence").is_ok());
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let atomic = match &mut forall.proved_then_facts[0].verify_result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_mut() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof,
            VerifyAtomicExceptEqualityFactResult::Failed(_) => panic!("verified membership"),
        },
        _ => panic!("atomic result"),
    };
    let child = match &mut atomic.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) => {
            match &mut proof.reason {
                StructuralMembershipReason::StandardSuperset(child) => child,
                _ => panic!("standard-superset route"),
            }
        }
        _ => panic!("structural membership"),
    };
    match &mut child.reason {
        StructuralMembershipReason::Known(proof) => {
            proof.why_parameters_of_known_fact_are_equal_to_givens.pop();
        }
        _ => panic!("membership citation"),
    }
    let error = compile_run(&result, &runtime, "missing_argument_evidence")
        .expect_err("a citation must not discard its transport evidence");
    assert_eq!(error.route, "KnownAtomic");
}

#[test]
fn arithmetic_family_preserves_owned_constructors_and_generic_carriers() {
    let cases = [
        (
            "forall a C, b C, c C:\n    a * (b + c) = a * b + a * c\n",
            "Litex.mul",
        ),
        ("forall a C, b C:\n    -(a + b) = -a - b\n", "Litex.neg"),
        (
            "forall a C:\n    (a + 1) * (a - 1) = a^2 - 1\n",
            "Litex.powNat",
        ),
        (
            "forall a R:\n    (a + 1) * (a - 1) = a^2 - 1\n",
            "Litex.powNatReal",
        ),
        (
            "forall a C:\n    0.125 * a + 0.125 * a = 0.25 * a\n",
            "(0.125 : ℂ)",
        ),
    ];
    for (source, constructor) in cases {
        let (result, runtime) = execute(source);
        let output = compile_run(&result, &runtime, "arithmetic_family").expect(source);
        assert!(output.contains(constructor), "{source}");
        assert!(output.contains("Litex.Obj (M := M) _Host_"));
        assert!(output.contains("NativeBridge.sameOfDenoteNumber"));
    }
}

#[test]
fn guarded_rational_replays_exact_strategy_and_child_guards() {
    let source = "forall a C, b C, c C:\n    b != 0\n    c != 0\n    =>:\n        (a / b) / c = a / (b * c)\n";
    let (result, runtime) = execute(source);
    let success = forall_proof(&result.statement_results[0]);
    assert!(matches!(
        &equality_proof(&success.proved_then_facts[0].verify_result).searched_proof,
        EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(_)
        )
    ));
    let output = compile_run(&result, &runtime, "guarded_rational").expect("guarded rational");
    assert!(output.contains("litex_normalize_rational (disch :="));
    assert!(output.contains("exact _litex_nz_0 | exact _litex_nz_1"));
    assert!(!output.contains("field_simp"));
    assert!(!output.contains("only [_litex_nz_"));
    assert!(output.contains("nativeNonzeroOfDenote"));
}

#[test]
fn guarded_requirements_cannot_be_deleted_or_reordered() {
    let source = "forall a C, b C, c C:\n    b != 0\n    c != 0\n    =>:\n        (a / b) / c = a / (b * c)\n";
    for delete in [true, false] {
        let (mut result, runtime) = execute(source);
        assert!(compile_run(&result, &runtime, "complete_guards").is_ok());
        let forall = forall_proof_mut(&mut result.statement_results[0]);
        let equality = equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
        match &mut equality.searched_proof {
            EqualFactSearchedProof::ByBuiltinStrategy(
                EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
            ) => {
                if delete {
                    proof.requirement_facts.pop();
                    proof.proof_of_requirement_facts.pop();
                } else {
                    proof.requirement_facts.swap(0, 1);
                    proof.proof_of_requirement_facts.swap(0, 1);
                }
            }
            _ => panic!("selected guarded normalization"),
        }
        let error = compile_run(&result, &runtime, "tampered_guards")
            .expect_err("guard order and arity are source evidence");
        assert_eq!(
            error.route,
            if delete {
                "Rational/Requirements"
            } else {
                "Arithmetic/NonzeroSubject"
            }
        );
    }
}

#[test]
fn guarded_route_cannot_be_retagged_as_zero_premise_rational() {
    let (mut result, runtime) = execute("forall a C:\n    a != 0\n    =>:\n        a / a = 1\n");
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let equality = equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    equality.searched_proof =
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
            EqualitySearchProofByCalculation::Rational {},
        ));
    let error = compile_run(&result, &runtime, "forged_zero_premise")
        .expect_err("cancellation has recorded obligations");
    assert_eq!(error.route, "Rational/Requirements");
}

#[test]
fn nonzero_product_guard_replays_actual_factor_children() {
    let source = "forall a C, b C, c C:\n    b != 0\n    c != 0\n    =>:\n        (a / b) / c = a / (b * c)\n";
    let (mut result, runtime) = execute(source);
    let output =
        compile_run(&result, &runtime, "product_guard").expect("guarded denominator product");
    assert!(output.contains("mul_ne_zero"));
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let equality = equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let div = match &mut equality.well_defined_proof.right {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Div(p),
                ),
            ..
        } => p,
        _ => panic!("right division WD"),
    };
    let guard = atomic_proof_mut(&mut div.requirement_fact_verified[0]);
    match &mut guard.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::NonzeroProduct(p),
        ) => {
            p.proof_of_requirement_facts.pop();
        }
        _ => panic!("actual product nonzero route"),
    }
    let error = compile_run(&result, &runtime, "missing_factor_guard")
        .expect_err("a product guard has two proven factors");
    assert_eq!(error.route, "NonzeroProduct/Requirements");
}

#[test]
fn closed_integer_power_keeps_exponent_object_and_source_domain() {
    for exponent in ["-2", "-(1 + 1)", "-4 / 2"] {
        let source = format!("forall a C:\n    a != 0\n    =>:\n        a^({exponent}) + a^({exponent}) = 2 * a^({exponent})\n");
        let (result, runtime) = execute(&source);
        let output = compile_run(&result, &runtime, "integer_power").expect(&source);
        assert!(output.contains("Litex.powInt"));
        assert!(output.contains("Litex.neg"));
        assert!(output.contains("(-2 : ℤ)"));
        assert!(output.contains("(by norm_num)"));
    }
}

#[test]
fn existing_large_integer_literal_profile_does_not_inherit_i128_limits() {
    let numeral = "123456789012345678901234567890123456789012345678901234567890";
    let source =
        format!("{numeral} = {numeral}\n$is_set({numeral})\n{numeral} $in R\n{numeral} $in C\n");
    let (result, runtime) = execute(&source);
    assert!(compile_run(&result, &runtime, "large_literal").is_ok());
}

#[test]
fn rational_guard_replays_its_actual_fact_id() {
    let (mut result, runtime) =
        execute("forall a C, b C, c C:\n    b != 0\n    c != 0\n    =>:\n        (a / b) / c = a / (b * c)\n");
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let equality = equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let child = match &mut equality.searched_proof {
        EqualFactSearchedProof::ByBuiltinStrategy(
            EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(p),
        ) => &mut p.proof_of_requirement_facts[0],
        _ => panic!("guarded normalization"),
    };
    match &mut atomic_proof_mut(child).searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) => {
            p.cite_fact_id = FactId::new(u64::MAX)
        }
        _ => panic!("actual guard citation"),
    }
    let error = compile_run(&result, &runtime, "missing_guard_citation")
        .expect_err("matching guard subjects cannot repair a missing source citation");
    assert_eq!(error.route, "FactId/Resolution");
}

#[test]
fn integer_value_does_not_override_a_changed_power_domain() {
    let (mut result, runtime) = execute("forall a C:\n    (a + 1) * (a - 1) = a^2 - 1\n");
    let (external, _) = execute("2 $in C\n");
    let truthful_c = match external
        .statement_results
        .into_iter()
        .next()
        .expect("membership")
    {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) => p.verify_result,
        _ => panic!("successful membership"),
    };
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let equality = equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let subtraction = match &mut equality.well_defined_proof.right {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Sub(p),
                ),
            ..
        } => p,
        _ => panic!("right subtraction WD"),
    };
    let power = match subtraction.child_obj_well_defined[0].as_mut() {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Pow(p),
                ),
            ..
        } => p,
        _ => panic!("power WD"),
    };
    power.requirement_fact_verified[1] = truthful_c;
    let error = compile_run(&result, &runtime, "changed_power_domain")
        .expect_err("an integer payload cannot invent the recorded natural-domain proof");
    assert_eq!(error.route, "WD/Pow/Domain");
}

#[test]
fn numeric_child_congruence_replays_children_and_closed_value_pair() {
    let (result, runtime) = execute("forall a C:\n    a + 0.125 = a + 1 / 8\n");
    let success = forall_proof(&result.statement_results[0]);
    assert!(matches!(
        &equality_proof(&success.proved_then_facts[0].verify_result).searched_proof,
        EqualFactSearchedProof::ByMatchingOneArgByOne(_)
    ));
    let output = compile_run(&result, &runtime, "numeric_child_congruence")
        .expect("owned arithmetic congruence");
    assert!(output.contains("congrArg₂ M.addValue"));
    assert!(output.contains("(by norm_num)"));
    assert!(!output.contains("(by ring)"));
}

#[test]
fn arithmetic_congruence_requires_its_exact_children() {
    let (mut result, runtime) = execute("forall a C:\n    a + 0.125 = a + 1 / 8\n");
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let equality = equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    match &mut equality.searched_proof {
        EqualFactSearchedProof::ByMatchingOneArgByOne(p) => {
            p.corresponding_arg_equal_proofs.pop();
        }
        _ => panic!("actual congruence route"),
    }
    let error = compile_run(&result, &runtime, "missing_congruence_child")
        .expect_err("the selected parent constructor cannot replace a missing child proof");
    assert_eq!(error.route, "ArithmeticCongruence/Children");
}

#[test]
fn closed_numeric_congruence_leaf_rejects_a_changed_scalar_certificate() {
    let (mut result, runtime) = execute("forall a C:\n    a + 0.125 = a + 1 / 8\n");
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let equality = equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let child = match &mut equality.searched_proof {
        EqualFactSearchedProof::ByMatchingOneArgByOne(p) => {
            equality_proof_mut(&mut p.corresponding_arg_equal_proofs[1])
        }
        _ => panic!("actual congruence route"),
    };
    match &mut child.searched_proof {
        EqualFactSearchedProof::ByClosedCalculation(p) => match &mut p.values {
            ClosedValuePair::Decimal { left, .. } => *left = "0.25".to_string(),
            _ => panic!("actual exact decimal pair"),
        },
        _ => panic!("actual closed calculation leaf"),
    }
    let error = compile_run(&result, &runtime, "changed_closed_leaf")
        .expect_err("a scalar payload must match the actual endpoint");
    assert_eq!(error.route, "ClosedEquality/Values");
}

#[test]
fn scalar_division_relations_replay_their_actual_child_equations() {
    let cases = [
        (
            "forall a C, b C:\n    b != 0\n    =>:\n        a / b * b = a\n",
            true,
        ),
        (
            "forall a C, b C:\n    b != 0\n    =>:\n        (a * b) / b = a\n",
            false,
        ),
    ];
    for (source, product) in cases {
        let (result, runtime) = execute(source);
        let success = forall_proof(&result.statement_results[0]);
        match &equality_proof(&success.proved_then_facts[0].verify_result).searched_proof {
            EqualFactSearchedProof::ByBuiltinRule(
                EqualitySearchProofByBuiltinRule::ScalarDivisionRelation(p),
            ) => assert_eq!(
                matches!(p, ScalarDivisionRelationProof::ProductFromDivision(_)),
                product
            ),
            _ => panic!("actual scalar division relation"),
        }
        let output = compile_run(&result, &runtime, "scalar_division_relation").expect(source);
        assert!(output.contains("NativeBridge.nativeEqOfDenoteNumber"));
        assert!(output.contains("div_eq_iff"));
        assert!(!output.contains("field_simp"));
        assert!(!output.contains("litex_normalize_rational"));
    }
}

#[test]
fn scalar_division_relation_checks_its_child_subject() {
    let (mut result, runtime) =
        execute("forall a C, b C:\n    b != 0\n    =>:\n        a / b * b = a\n");
    let forall = forall_proof_mut(&mut result.statement_results[0]);
    let equality = equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let child = match &mut equality.searched_proof {
        EqualFactSearchedProof::ByBuiltinRule(
            EqualitySearchProofByBuiltinRule::ScalarDivisionRelation(
                ScalarDivisionRelationProof::ProductFromDivision(p),
            ),
        ) => equality_proof_mut(&mut p.division_equation),
        _ => panic!("actual product from division route"),
    };
    // A syntactically successful child from another endpoint cannot certify
    // the parent relation. Changing only the endpoint first fails exact WD.
    child.fact.right = Obj::Literal(Literal::Number(Number::new("1".to_string())));
    let error = compile_run(&result, &runtime, "changed_division_child")
        .expect_err("the source child must have its own certified endpoints");
    assert_eq!(error.route, "WD/Subject");
}

#[test]
fn forged_false_rational_claim_requires_kernel_validation() {
    let (mut result, runtime) = execute("forall a C:\n    a + 1 = a + 1\n");
    let success = match &mut result.statement_results[0] {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) => p,
        _ => panic!("authentic successful statement"),
    };
    let forall = match &mut success.verify_result {
        VerifyFactResult::ForallFact(p) => match p.as_mut() {
            VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) => p,
            _ => panic!("authentic local introduction"),
        },
        _ => panic!("forall result"),
    };
    let parameter = Obj::Identifier(IdentifierObj::from_bound_name(
        &forall.fact.typed_parameters.groups[0].params[0],
    ));
    let equality = equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    assert!(matches!(
        &equality.searched_proof,
        EqualFactSearchedProof::ByTheyAreTheSame(TheyAreTheSameProof::SameIr(_))
    ));
    // Counterfeit only the test's result values. Keep valid source constructor
    // WD, binder/citation identities, and all primary store subjects aligned.
    equality.fact.right = parameter.clone();
    match &equality.well_defined_proof.left {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Add(p),
                ),
            ..
        } => assert!(matches!(
            p.child_obj_well_defined[0].as_ref(),
            ObjWellDefinedProof::ByDef {
                proof: ObjWellDefinedProofByDef::Identifier(_),
                ..
            }
        )),
        _ => panic!("the authentic left constructor contains the parameter's definition WD"),
    }
    // Plain identifier WD is a definition leaf, not a memoized WdId in the
    // current producer. Reproduce that actual empty leaf for the same binder.
    equality.well_defined_proof.right = ObjWellDefinedProof::ByDef {
        obj: parameter,
        proof: ObjWellDefinedProofByDef::Identifier(
            crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IdentifierObjWellDefinedProof::new(),
        ),
    };
    equality.searched_proof =
        EqualFactSearchedProof::ByBuiltinRule(EqualitySearchProofByBuiltinRule::Calculation(
            EqualitySearchProofByCalculation::Rational {},
        ));
    let forged_equal = AtomicFact::EqualFact(equality.fact.clone());
    forall.fact.then_facts[0] = ExistOrAndChainAtomicFact::AtomicFact(forged_equal.clone());
    match &mut forall.proved_then_facts[0].store_and_infer.store {
        StoreFactResult::AtomicFact(stored) => {
            assert_eq!(stored.fact_id, forged_equal.fact_id());
            stored.fact = forged_equal;
        }
        _ => panic!("atomic primary store"),
    }
    let forged_forall = forall.fact.clone();
    match &mut success.store_and_infer_result.store {
        StoreFactResult::ForallFact(stored) => {
            assert_eq!(stored.fact_id, forged_forall.fact_id);
            stored.fact = forged_forall;
        }
        _ => panic!("forall primary store"),
    }
    let output = compile_run(&result, &runtime, "forged_false_rational")
        .expect("Rational's empty tag is not a Rust mathematical certificate");
    assert!(output.contains("NativeBridge.sameOfDenoteNumber"));
    assert!(output.contains("(by ring)"));
    assert!(!output.contains("sorry"));
    // A caller can ask the real Lean gate to reject this compiler-generated
    // counterfeit. Default unit runs have no filesystem side effect.
    if let Some(path) = std::env::var_os("LITEX_LEAN_NEGATIVE_OUTPUT") {
        let path = std::path::PathBuf::from(path);
        assert!(
            path.is_absolute(),
            "the explicit gate output path must be absolute"
        );
        std::fs::write(path, output).expect("write requested negative kernel fixture");
    }
}

const PHASE1_ADD_ZERO: &str = "thm add_zero:\n    ? forall x R:\n        x + 0 = x\n";
const PHASE1_NAMED_ALIAS: &str = "thm add_zero:\n    ? forall x R:\n        x + 0 = x\nhave offset R = 2\nlet shifted = offset + 0\nby thm add_zero(offset) => offset + 0 = offset\nshifted = offset\nlet actual_argument_alias = offset\nby thm add_zero(actual_argument_alias) => actual_argument_alias + 0 = actual_argument_alias\n";
const PHASE1_GUARDED_THEOREM: &str = "thm guarded_self:\n    ? forall x C:\n        x != 0\n        =>:\n            x / x = x / x\n";
const PHASE1_TRANSITIVITY: &str = "forall a,b,c R:\n    a = b\n    b = c\n    =>:\n        a = c\n        c = a\n        a + 1 = c + 1\n";

#[test]
fn phase1_numeric_and_typed_aliases_replay_actual_definition_evidence() {
    let sources = [
        ("let numeric_alias = 2 + 3\nnumeric_alias = 5\n5 = numeric_alias\n", 1),
        ("have typed_offset R = 2\nlet typed_alias = typed_offset\ntyped_alias = 2\ntyped_alias $in R\n", 2),
    ];
    for (source, equality_index) in sources {
        let (result, runtime) = execute(source);
        let output = compile_run(&result, &runtime, "phase1_aliases").expect(source);
        assert!(output.contains("noncomputable def _object_i"));
        assert!(output.contains("Litex.sameRefl"));
        assert!(matches!(
            &equality_proof(
                &fact_statement(&result.statement_results[equality_index]).verify_result
            )
            .searched_proof,
            EqualFactSearchedProof::ByEquivalenceClass(_)
        ));
    }
}

#[test]
fn phase1_named_theorem_uses_the_actual_alias_argument_and_returned_citation() {
    let (result, runtime) = execute(PHASE1_NAMED_ALIAS);
    if let Ok(path) = std::env::var("LITEX_LEAN_PHASE1_TRACE") {
        std::fs::write(
            path,
            crate::json_output::emit_run_detailed(&result, &runtime, "phase1", None),
        )
        .expect("write selected-result audit");
    }
    let call = by_theorem(&result.statement_results[6]);
    let returned_id = call.returned_conclusions[0].primary_fact_id();
    match &equality_proof(&call.selected_proof).searched_proof {
        EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(proof),
        ) => {
            assert!(!proof.reversed);
            assert_eq!(proof.cited.fact_id, returned_id);
        }
        _ => panic!("source theorem selection must directly cite its returned equality"),
    }
    let output = compile_run(&result, &runtime, "phase1_named_alias").expect("named alias tracer");
    assert!(output.contains("theorem named_thm_1"));
    assert!(output.contains("named_thm_1 (M := M)"));
    let alias = &let_definition(&result.statement_results[5]).statement.name;
    assert!(output.contains(&format!("(_object_i{} (M := M))", alias.id.value())));
}

#[test]
fn phase1_equality_paths_preserve_orientation_and_transport() {
    let (result, runtime) = execute(PHASE1_TRANSITIVITY);
    let proof = forall_proof(&result.statement_results[0]);
    for conclusion in &proof.proved_then_facts[..2] {
        assert!(matches!(
            &equality_proof(&conclusion.verify_result).searched_proof,
            EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(_)
            )
        ));
    }
    let output = compile_run(&result, &runtime, "phase1_paths").expect("oriented equality paths");
    assert!(output.contains(".trans"));
    assert!(output.contains(".symm"));
    assert!(output.contains("congrArg₂ M.addValue"));
}

#[test]
fn phase1_membership_and_nonzero_transport_consume_cited_argument_equalities() {
    let cases = [
        (
            "forall u,v C:\n    u = v\n    u $in R\n    =>:\n        v $in R\n",
            "Litex.inOfSame",
        ),
        (
            "forall x,y C:\n    x = y\n    x != 0\n    =>:\n        y != 0\n",
            "Litex.notSameOfSame",
        ),
    ];
    for (source, bridge) in cases {
        let (result, runtime) = execute(source);
        let output = compile_run(&result, &runtime, "phase1_predicate_transport").expect(source);
        assert!(output.contains(bridge));
    }
}

#[test]
fn phase1_theorem_body_replays_local_alias_and_typed_definition() {
    let source = "thm alias_in_body:\n    ? forall x R:\n        x + 0 = x\n    let temporary = x + 0\n    have body_zero R = 0\n    temporary = x\n";
    let (result, runtime) = execute(source);
    let output =
        compile_run(&result, &runtime, "phase1_local_definitions").expect("local body definitions");
    assert!(output.contains("let _object_i"));
    assert!(output.contains("have _fact_f"));
    assert!(!output.contains("noncomputable def _object_i"));
}

#[test]
fn phase1_missing_alias_producer_is_not_recovered_from_runtime_definitions() {
    let (mut result, runtime) = execute("let alias = 2\nalias = alias\n");
    result.statement_results.remove(0);
    let error = compile_run(&result, &runtime, "phase1_missing_alias")
        .expect_err("source alias needs a compiled producer");
    assert_eq!(error.route, "Identifier/Producer");
}

#[test]
fn phase1_local_theorem_alias_cannot_escape_into_a_later_statement() {
    let source = "thm alias_in_body:\n    ? forall x R:\n        x + 0 = x\n    let temporary = x + 0\n    have body_zero R = 0\n    temporary = x\n1 = 1\n";
    let (mut result, runtime) = execute(source);
    let temporary = match &named_theorem_mut(&mut result.statement_results[0]).body {
        ExecDefThmBodyProof::Forall(body) => Obj::Identifier(IdentifierObj::from_bound_name(
            &let_definition(&body.proof_steps[0]).statement.name,
        )),
        _ => panic!("forall theorem body"),
    };
    let later = match &mut result.statement_results[1] {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => proof,
        _ => panic!("later successful fact"),
    };
    let equality = equality_proof_mut(&mut later.verify_result);
    equality.fact.left = temporary.clone();
    equality.well_defined_proof.left = ObjWellDefinedProof::ByDef {
        obj: temporary,
        proof: ObjWellDefinedProofByDef::Identifier(
            crate::execute::execute_fact_stmt::well_defined_results::verify_obj::IdentifierObjWellDefinedProof::new(),
        ),
    };
    let changed = equality.fact.clone();
    match &mut later.store_and_infer_result.store {
        StoreFactResult::AtomicFact(stored) => stored.fact = AtomicFact::EqualFact(changed),
        _ => panic!("atomic later store"),
    }
    let error = compile_run(&result, &runtime, "phase1_escaped_body_alias")
        .expect_err("the theorem's local alias producer was closed before this statement");
    assert_eq!(error.route, "Identifier/Producer");
}

#[test]
fn phase1_alias_statement_identity_and_value_must_match_its_stored_equality() {
    let (mut result, runtime) = execute("let alias = 2\n");
    let_definition_mut(&mut result.statement_results[0])
        .statement
        .name
        .id = IdentifierId::new(u64::MAX);
    let error = compile_run(&result, &runtime, "phase1_wrong_alias_id")
        .expect_err("stored alias identity must be exact");
    assert_eq!(error.route, "Declaration/StoreSubject");

    let (mut result, runtime) = execute("let alias = 2\n");
    let_definition_mut(&mut result.statement_results[0])
        .statement
        .value = number_object("3");
    let error = compile_run(&result, &runtime, "phase1_wrong_alias_value")
        .expect_err("literal WD cannot certify another value");
    assert_eq!(error.route, "WD/Subject");
}

#[test]
fn phase1_alias_requires_its_own_store_and_source_orientation() {
    let (mut result, runtime) = execute("let alias = 2\n2 = alias\n");
    let reversed = fact_statement(&result.statement_results[1])
        .store_and_infer_result
        .primary_fact_id();
    let_definition_mut(&mut result.statement_results[0]).stored_fact_ids[0] = reversed;
    let error = compile_run(&result, &runtime, "phase1_reversed_alias_store")
        .expect_err("alias storage requires name equals value");
    assert_eq!(error.route, "Declaration/StoreSubject");

    let (mut result, runtime) = execute("let alias = 2\n");
    let_definition_mut(&mut result.statement_results[0])
        .stored_fact_ids
        .clear();
    let error = compile_run(&result, &runtime, "phase1_missing_alias_store")
        .expect_err("alias storage stage cannot disappear");
    assert_eq!(error.route, "Let/Inference");
}

#[test]
fn phase1_typed_alias_requires_all_membership_stages() {
    let (mut result, runtime) = execute("have offset R = 2\n");
    have_equal_mut(&mut result.statement_results[0])
        .membership_checks
        .clear();
    let error = compile_run(&result, &runtime, "phase1_missing_have_member")
        .expect_err("typed definition cannot skip its carrier proof");
    assert_eq!(error.route, "HaveEqual/Stages");
}

#[test]
fn phase1_missing_and_wrong_equality_edges_are_not_repaired_by_search() {
    let (mut result, runtime) = execute(PHASE1_TRANSITIVITY);
    equality_path_mut(
        &mut forall_proof_mut(&mut result.statement_results[0]).proved_then_facts[0].verify_result,
    )
    .path
    .pop();
    let error = compile_run(&result, &runtime, "phase1_missing_path_edge")
        .expect_err("ordered path must reach its source endpoint");
    assert_eq!(error.route, "Equality/PathEndpoint");

    let (mut result, runtime) = execute(PHASE1_TRANSITIVITY);
    let path = equality_path_mut(
        &mut forall_proof_mut(&mut result.statement_results[0]).proved_then_facts[0].verify_result,
    );
    assert_eq!(path.path.len(), 2);
    path.path[1].2 = path.path[0].2;
    let error = compile_run(&result, &runtime, "phase1_wrong_path_citation")
        .expect_err("first equality does not prove the second edge");
    assert_eq!(error.route, "Equality/PathSubject");

    let (mut result, runtime) = execute(PHASE1_TRANSITIVITY);
    equality_path_mut(
        &mut forall_proof_mut(&mut result.statement_results[0]).proved_then_facts[0].verify_result,
    )
    .path
    .swap(0, 1);
    let error = compile_run(&result, &runtime, "phase1_reordered_path")
        .expect_err("valid edges cannot be consumed out of order");
    assert_eq!(error.route, "Equality/PathOrder");
}

#[test]
fn phase1_invocation_requires_the_earlier_named_declaration() {
    let source = format!("{PHASE1_ADD_ZERO}by thm add_zero(2) => 2 + 0 = 2\n");
    let (mut result, runtime) = execute(&source);
    result.statement_results.remove(0);
    let error = compile_run(&result, &runtime, "phase1_missing_theorem")
        .expect_err("runtime declaration is not compiled evidence");
    assert_eq!(error.route, "ByThm/Producer");

    let (mut result, runtime) = execute(&source);
    match &mut by_theorem_mut(&mut result.statement_results[1]).callee {
        ResolvedTheoremCallee::UserTheorem(declaration) => declaration.name.push_str("_other"),
        _ => panic!("actual user theorem callee"),
    }
    let error = compile_run(&result, &runtime, "phase1_corrupt_callee")
        .expect_err("captured callee must equal compiled declaration");
    assert_eq!(error.route, "ByThm/Callee");
}

#[test]
fn phase1_theorem_goal_wd_requires_its_own_parameter_producers() {
    let (mut result, runtime) = execute(PHASE1_ADD_ZERO);
    theorem_goal_wd_mut(named_theorem_mut(&mut result.statement_results[0]))
        .introduced_params
        .defined_params
        .stored_fact_ids
        .clear();
    let error = compile_run(&result, &runtime, "phase1_missing_goal_parameter")
        .expect_err("goal WD binder introductions are a required stage");
    assert_eq!(error.route, "Parameters/StoreCapture");

    let (mut result, runtime) = execute(PHASE1_ADD_ZERO);
    theorem_goal_wd_mut(named_theorem_mut(&mut result.statement_results[0]))
        .introduced_params
        .defined_params
        .stored_fact_ids[0] = FactId::new(u64::MAX);
    let error = compile_run(&result, &runtime, "phase1_wrong_goal_parameter")
        .expect_err("goal WD cannot use a nonexistent introducing membership");
    assert_eq!(error.route, "Parameters/StoreCapture");
}

#[test]
fn phase1_named_declaration_binder_identity_cannot_change_behind_goal_wd() {
    let (mut result, runtime) = execute(PHASE1_ADD_ZERO);
    match &mut named_theorem_mut(&mut result.statement_results[0])
        .statement
        .fact
    {
        Fact::ForallFact(fact) => {
            fact.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX)
        }
        _ => panic!("forall theorem interface"),
    }
    let error = compile_run(&result, &runtime, "phase1_corrupt_declaration_binder")
        .expect_err("declaration and goal-WD binder identities must agree");
    assert_eq!(error.route, "Parameters/Subject");
}

#[test]
fn phase1_guarded_theorem_goal_wd_replays_the_exact_domain_store() {
    let (result, runtime) = execute(PHASE1_GUARDED_THEOREM);
    assert!(compile_run(&result, &runtime, "phase1_guarded_goal").is_ok());

    let (mut result, runtime) = execute(PHASE1_GUARDED_THEOREM);
    let wd = theorem_goal_wd_mut(named_theorem_mut(&mut result.statement_results[0]));
    match &mut wd.assumed_dom_facts[0].store_and_infer.store {
        StoreFactResult::AtomicFact(stored) => stored.fact_id = FactId::new(u64::MAX),
        _ => panic!("atomic nonzero domain store"),
    }
    let error = compile_run(&result, &runtime, "phase1_corrupt_goal_domain_store")
        .expect_err("domain assumption must own its exact primary store");
    assert_eq!(error.route, "Store/Subject");
}

#[test]
fn phase1_theorem_goal_wd_checks_every_exact_then_subject() {
    let (mut result, runtime) = execute(PHASE1_ADD_ZERO);
    theorem_goal_wd_mut(named_theorem_mut(&mut result.statement_results[0]))
        .then
        .clear();
    let error = compile_run(&result, &runtime, "phase1_missing_goal_then_wd")
        .expect_err("goal formation cannot skip a conclusion");
    assert_eq!(error.route, "WD/ForallThenArity");

    let (mut result, runtime) = execute(PHASE1_ADD_ZERO);
    match &mut theorem_goal_wd_mut(named_theorem_mut(&mut result.statement_results[0])).then[0] {
        FactWellDefinedProof::Equality(wd) => replace_wd_subject(&mut wd.left, number_object("9")),
        _ => panic!("equality goal WD"),
    }
    let error = compile_run(&result, &runtime, "phase1_changed_goal_then_wd")
        .expect_err("another object's WD is not this conclusion's WD");
    assert_eq!(error.route, "WD/Subject");
}

#[test]
fn phase1_theorem_body_source_steps_cannot_be_replaced_by_other_definitions() {
    let source = "thm alias_in_body:\n    ? forall x R:\n        x + 0 = x\n    let temporary = x + 0\n    have body_zero R = 0\n    temporary = x\n";
    let (mut result, runtime) = execute(source);
    let theorem = named_theorem_mut(&mut result.statement_results[0]);
    match &mut theorem.body {
        ExecDefThmBodyProof::Forall(body) => {
            let_definition_mut(&mut body.proof_steps[0])
                .statement
                .name
                .id = IdentifierId::new(u64::MAX);
        }
        _ => panic!("forall body"),
    }
    let error = compile_run(&result, &runtime, "phase1_changed_body_capture")
        .expect_err("captured result must belong to its source statement");
    assert_eq!(error.route, "Theorem/ProofStepCapture");
}

#[test]
fn phase1_invocation_cannot_delete_a_returned_producer() {
    let source = format!("{PHASE1_ADD_ZERO}by thm add_zero(2) => 2 + 0 = 2\n");
    let (mut result, runtime) = execute(&source);
    by_theorem_mut(&mut result.statement_results[1])
        .returned_conclusions
        .clear();
    let error = compile_run(&result, &runtime, "phase1_deleted_return")
        .expect_err("selected proof needs the invocation's actual returned producer");
    assert_eq!(error.route, "ByThm/Stages");
}

#[test]
fn phase1_explicit_selection_cannot_be_replaced_by_an_unrelated_ambient_truth() {
    let source = format!("1 = 1\n1 = 1\n{PHASE1_ADD_ZERO}by thm add_zero(2) => 2 + 0 = 2\n");
    let (mut result, runtime) = execute(&source);
    let ambient = match result.statement_results.remove(1) {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(ambient)) => ambient,
        _ => panic!("actual independently verified ambient truth"),
    };
    let call = by_theorem_mut(&mut result.statement_results[2]);
    call.selected_proof = ambient.verify_result;
    call.stored = ambient.store_and_infer_result;
    let error = compile_run(&result, &runtime, "phase1_ambient_selection")
        .expect_err("a true ambient proof does not select a returned theorem atom");
    assert_eq!(error.route, "ByThm/SelectionProvenance");
}

#[test]
fn phase1_explicit_selection_rejects_ambient_citations_even_with_the_right_alpha_shape() {
    let source = format!("1 = 1\n1 = 1\n{PHASE1_ADD_ZERO}by thm add_zero(2) => 2 + 0 = 2\n");
    let (mut result, runtime) = execute(&source);
    let registered = equality_proof(&fact_statement(&result.statement_results[0]).verify_result)
        .fact
        .clone();
    let ambient = match result.statement_results.remove(1) {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(ambient)) => ambient,
        _ => panic!("independent truth"),
    };
    let mut ambient_proof = match ambient.verify_result {
        VerifyFactResult::Equality(proof) => match *proof {
            VerifyEqualityResult::Success(proof) => proof,
            _ => panic!("successful ambient equality"),
        },
        _ => panic!("ambient equality"),
    };
    let call = by_theorem_mut(&mut result.statement_results[2]);
    let selected = equality_proof_mut(&mut call.selected_proof);
    std::mem::swap(
        &mut selected.well_defined_proof,
        &mut ambient_proof.well_defined_proof,
    );
    selected.fact = ambient_proof.fact;
    match &mut selected.searched_proof {
        EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(proof),
        ) => proof.cited = registered,
        _ => panic!("actual exact selected alpha shape"),
    }
    call.stored = ambient.store_and_infer_result;
    let error = compile_run(&result, &runtime, "phase1_ambient_alpha_selection")
        .expect_err("a correctly shaped citation must still originate in this return list");
    assert_eq!(error.route, "ByThm/SelectionProvenance");
}

#[test]
fn phase1_explicit_selection_cannot_reverse_a_directly_returned_equality() {
    let source = format!("{PHASE1_ADD_ZERO}by thm add_zero(2) => 2 + 0 = 2\n");
    let (mut result, runtime) = execute(&source);
    let call = by_theorem_mut(&mut result.statement_results[1]);
    let selected = equality_proof_mut(&mut call.selected_proof);
    std::mem::swap(&mut selected.fact.left, &mut selected.fact.right);
    std::mem::swap(
        &mut selected.well_defined_proof.left,
        &mut selected.well_defined_proof.right,
    );
    match &mut selected.searched_proof {
        EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(proof),
        ) => proof.reversed = true,
        _ => panic!("actual exact selected alpha shape"),
    }
    let reversed = selected.fact.clone();
    match &mut call.stored.store {
        StoreFactResult::AtomicFact(stored) => stored.fact = AtomicFact::EqualFact(reversed),
        _ => panic!("atomic selected store"),
    }
    let error = compile_run(&result, &runtime, "phase1_reversed_selection")
        .expect_err("equality symmetry is not direct theorem selection");
    assert_eq!(error.route, "ByThm/SelectionProvenance");
}

const PHASE1_KNOWN_FORALL: &str = "forall a,b,c R:\n    a = b\n    =>:\n        b = a\nforall p,q,r R:\n    p = q\n    =>:\n        q = p\n";

#[test]
fn phase1_known_forall_reuses_the_exact_producer_with_all_binders_including_unused() {
    let (result, runtime) = execute(PHASE1_KNOWN_FORALL);
    let source = forall_proof(&result.statement_results[0]);
    let target = known_forall(&result.statement_results[1]);
    assert_eq!(target.cite_fact_id, source.fact.fact_id);
    assert_eq!(target.parameter_renamings.len(), 3);
    for ((source, target), renaming) in source.fact.typed_parameters.groups[0]
        .params
        .iter()
        .zip(&target.fact.typed_parameters.groups[0].params)
        .zip(&target.parameter_renamings)
    {
        assert_eq!(renaming.source, source.id);
        assert_eq!(renaming.target, target.id);
    }
    let output = compile_run(&result, &runtime, "phase1_whole_forall")
        .expect("whole-proposition alpha reuse");
    assert!(output.contains("fact_1 (M := M)"));
    assert!(output.contains("theorem fact_2"));
    assert!(!output.contains("(by ring)"));
}

#[test]
fn phase1_known_forall_cannot_omit_or_add_even_an_unused_binder_renaming() {
    let (mut result, runtime) = execute(PHASE1_KNOWN_FORALL);
    known_forall_mut(&mut result.statement_results[1])
        .parameter_renamings
        .pop();
    let error = compile_run(&result, &runtime, "phase1_missing_unused_renaming")
        .expect_err("unused binder still owns one positional renaming");
    assert_eq!(error.route, "KnownForall/Arity");

    let (mut result, runtime) = execute(PHASE1_KNOWN_FORALL);
    let proof = known_forall_mut(&mut result.statement_results[1]);
    let first = &proof.parameter_renamings[0];
    let extra = crate::execute::execute_fact_stmt::verify_forall_fact::ForallParameterRenaming {
        source: first.source,
        target: first.target,
    };
    proof.parameter_renamings.push(extra);
    let error = compile_run(&result, &runtime, "phase1_extra_renaming")
        .expect_err("an additional mapping cannot alter source binder arity");
    assert_eq!(error.route, "KnownForall/Arity");
}

#[test]
fn phase1_known_forall_requires_an_ordered_bijection_without_duplicate_ids() {
    for change in [
        "wrong_source",
        "wrong_target",
        "reordered",
        "duplicate_source",
        "duplicate_target",
    ] {
        let (mut result, runtime) = execute(PHASE1_KNOWN_FORALL);
        let renamings = &mut known_forall_mut(&mut result.statement_results[1]).parameter_renamings;
        match change {
            "wrong_source" => renamings[0].source = IdentifierId::new(u64::MAX),
            "wrong_target" => renamings[0].target = IdentifierId::new(u64::MAX),
            "reordered" => renamings.swap(0, 1),
            "duplicate_source" => renamings[1].source = renamings[0].source,
            "duplicate_target" => renamings[1].target = renamings[0].target,
            _ => unreachable!(),
        }
        let error = compile_run(&result, &runtime, "phase1_changed_renaming").expect_err(change);
        assert_eq!(error.route, "KnownForall/Renaming", "{change}");
    }
}

#[test]
fn phase1_known_forall_needs_an_earlier_compiled_producer() {
    let (mut result, runtime) = execute(PHASE1_KNOWN_FORALL);
    result.statement_results.remove(0);
    let error = compile_run(&result, &runtime, "phase1_missing_whole_forall_producer")
        .expect_err("runtime source fact does not replace its removed proof producer");
    assert_eq!(error.route, "FactId/Producer");
}

#[test]
fn phase1_known_forall_rejects_missing_wrong_family_and_closed_scope_citations() {
    let (mut result, runtime) = execute(PHASE1_KNOWN_FORALL);
    known_forall_mut(&mut result.statement_results[1]).cite_fact_id = FactId::new(u64::MAX);
    let error = compile_run(&result, &runtime, "phase1_missing_whole_forall_cite")
        .expect_err("missing source citation cannot be searched again");
    assert_eq!(error.route, "FactId/Resolution");

    let source = format!("1 = 1\n{PHASE1_KNOWN_FORALL}");
    let (mut result, runtime) = execute(&source);
    let atomic_id = fact_statement(&result.statement_results[0])
        .store_and_infer_result
        .primary_fact_id();
    known_forall_mut(&mut result.statement_results[2]).cite_fact_id = atomic_id;
    let error = compile_run(&result, &runtime, "phase1_wrong_whole_forall_family")
        .expect_err("an atomic theorem is not the cited whole forall");
    assert_eq!(error.route, "KnownForall/Citation");

    let (mut result, runtime) = execute(PHASE1_KNOWN_FORALL);
    let closed_id = forall_proof(&result.statement_results[0]).assumed_dom_facts[0]
        .store_and_infer
        .primary_fact_id();
    known_forall_mut(&mut result.statement_results[1]).cite_fact_id = closed_id;
    let error = compile_run(&result, &runtime, "phase1_closed_whole_forall_cite")
        .expect_err("a previous forall's local premise has left the active scope");
    assert_eq!(error.route, "FactId/Resolution");
}

#[test]
fn phase1_known_forall_cannot_change_parameter_carriers() {
    let (mut result, runtime) = execute(PHASE1_KNOWN_FORALL);
    known_forall_mut(&mut result.statement_results[1])
        .fact
        .typed_parameters
        .groups[0]
        .param_type = ParamType::Obj(Obj::StandardSet(StandardSet::C));
    let error = compile_run(&result, &runtime, "phase1_changed_whole_forall_carrier")
        .expect_err("alpha renaming cannot change R into C");
    assert_eq!(error.route, "KnownForall/Carrier");
}

#[test]
fn phase1_known_forall_cannot_change_domain_or_conclusion_subjects() {
    let (mut result, runtime) = execute(PHASE1_KNOWN_FORALL);
    match &mut known_forall_mut(&mut result.statement_results[1])
        .fact
        .dom_facts[0]
    {
        Fact::AtomicFact(AtomicFact::EqualFact(fact)) => fact.right = number_object("0"),
        _ => panic!("guard equality"),
    }
    let error = compile_run(&result, &runtime, "phase1_changed_whole_forall_domain")
        .expect_err("recorded binder bijection does not justify another premise");
    assert_eq!(error.route, "KnownForall/Domain");

    let (mut result, runtime) = execute(PHASE1_KNOWN_FORALL);
    match &mut known_forall_mut(&mut result.statement_results[1])
        .fact
        .then_facts[0]
    {
        ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(fact)) => {
            fact.right = number_object("0")
        }
        _ => panic!("conclusion equality"),
    }
    let error = compile_run(&result, &runtime, "phase1_changed_whole_forall_conclusion")
        .expect_err("recorded binder bijection does not justify another conclusion");
    assert_eq!(error.route, "KnownForall/Conclusion");
}

#[test]
fn phase1_second_theorem_call_needs_its_own_argument_type_proof_identity() {
    let (mut result, runtime) = execute(PHASE1_NAMED_ALIAS);
    by_theorem_mut(&mut result.statement_results[6])
        .type_proofs
        .clear();
    let error = compile_run(&result, &runtime, "phase1_deleted_second_type_proof")
        .expect_err("the alias call cannot skip its argument membership stage");
    assert_eq!(error.route, "ByThm/Arguments");

    let (mut result, runtime) = execute(PHASE1_NAMED_ALIAS);
    let proof = &mut by_theorem_mut(&mut result.statement_results[6]).type_proofs[0];
    match &mut atomic_proof_mut(proof).fact {
        AtomicFact::InFact(fact) => fact.fact_id = FactId::new(u64::MAX),
        _ => panic!("actual alias argument membership proof"),
    }
    let error = compile_run(&result, &runtime, "phase1_changed_second_type_proof_id")
        .expect_err("returned WD cites this exact checked type producer's original identity");
    assert_eq!(error.route, "FactId/Producer");
}

#[test]
fn phase1_second_call_return_wd_cannot_cite_a_closed_first_call_type_proof() {
    let (mut result, runtime) = execute(PHASE1_NAMED_ALIAS);
    let closed =
        atomic_proof_mut(&mut by_theorem_mut(&mut result.statement_results[3]).type_proofs[0])
            .fact
            .fact_id();
    let call = by_theorem_mut(&mut result.statement_results[6]);
    let add = match &mut call.conclusions_wd[0] {
        FactWellDefinedProof::Equality(wd) => match &mut wd.left {
            ObjWellDefinedProof::ByDef {
                proof:
                    ObjWellDefinedProofByDef::ArithmeticOperator(
                        ArithmeticOperatorObjWellDefinedProofByDef::Add(proof),
                    ),
                ..
            } => proof,
            _ => panic!("actual alias-plus-zero conclusion construction"),
        },
        _ => panic!("returned equality WD"),
    };
    let requirement = atomic_proof_mut(&mut add.requirement_fact_verified[0]);
    match &mut requirement.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) => {
            structural_known_citation_mut(proof).cite_fact_id = closed
        }
        _ => panic!("actual standard numeric-superset operand requirement"),
    }
    let error = compile_run(&result, &runtime, "phase1_closed_call_type_producer")
        .expect_err("the first invocation's fresh membership producer is closed");
    assert_eq!(error.route, "FactId/Resolution");
}

fn structural_known_citation_mut(
    proof: &mut StructuralMembershipProof,
) -> &mut AtomicExceptEqualityFactSearchProofByKnownAtomicFact {
    match &mut proof.reason {
        StructuralMembershipReason::Known(proof) => proof,
        StructuralMembershipReason::StandardSuperset(proof) => structural_known_citation_mut(proof),
        _ => panic!("actual captured known membership under standard supersets"),
    }
}

fn known_forall(result: &ExecStmtResult) -> &VerifyKnownForallFactProof {
    match &fact_statement(result).verify_result {
        VerifyFactResult::ForallFact(proof) => match proof.as_ref() {
            VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) => {
                proof
            }
            _ => panic!("actual whole-forall source replay"),
        },
        _ => panic!("forall result"),
    }
}

fn known_forall_mut(result: &mut ExecStmtResult) -> &mut VerifyKnownForallFactProof {
    let fact = match result {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => proof,
        _ => panic!("successful forall fact statement"),
    };
    match &mut fact.verify_result {
        VerifyFactResult::ForallFact(proof) => match proof.as_mut() {
            VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) => {
                proof
            }
            _ => panic!("actual whole-forall source replay"),
        },
        _ => panic!("forall result"),
    }
}

const PHASE1_COMPUTED_REWRITE: &str =
    "let computed = 2 + 3\ncomputed $in C\ncomputed + 1 = computed + 1\n";
const PHASE1_CARRIER_REWRITE: &str =
    "let base_carrier = R\nlet carrier_alias = base_carrier\n1 $in carrier_alias\n";

#[test]
fn phase1_computed_alias_membership_consumes_the_actual_closed_endpoint() {
    let (mut result, runtime) = execute(PHASE1_COMPUTED_REWRITE);
    let expected = let_definition(&result.statement_results[0])
        .stored_fact_ids
        .clone();
    let expected_closed_ir = let_definition(&result.statement_results[0])
        .statement
        .value
        .ir();
    match atomic_rewrite_mut(&mut result.statement_results[1]) {
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(
            proof,
        ) => {
            assert_eq!(proof.cited_equal_fact_ids, expected);
            match &proof.rewritten_fact {
                Fact::AtomicFact(AtomicFact::InFact(fact)) => {
                    assert_eq!(fact.element.ir(), expected_closed_ir)
                }
                _ => panic!("actual closed membership residual"),
            }
        }
        _ => panic!("actual computed alias ClosedNumeric winning route"),
    }
    let output = compile_run(&result, &runtime, "phase1_computed_alias")
        .expect("computed alias membership and arithmetic WD");
    assert!(output.contains("Litex.inOfSame"));
    assert!(output.contains("Litex.sameRefl (Litex.add"));
    assert!(!output.contains("NativeBridge.sameOfDenoteNumber"));
}

#[test]
fn phase1_carrier_alias_membership_consumes_its_actual_ordered_known_equality_path() {
    let (mut result, runtime) = execute(PHASE1_CARRIER_REWRITE);
    let expected = vec![
        let_definition(&result.statement_results[1]).stored_fact_ids[0],
        let_definition(&result.statement_results[0]).stored_fact_ids[0],
    ];
    match atomic_rewrite_mut(&mut result.statement_results[2]) {
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::KnownEqualObjSubstitution(proof) => {
            assert_eq!(proof.cited_equal_fact_ids, expected)
        }
        _ => panic!("actual carrier KnownEqual winning route"),
    }
    let output = compile_run(&result, &runtime, "phase1_carrier_alias")
        .expect("carrier alias equality path");
    assert!(output.contains("Litex.inOfSame"));
    assert!(output.contains(".trans"));
}

#[test]
fn phase1_atomic_rewrite_needs_nonempty_nonduplicated_citations() {
    for duplicate in [false, true] {
        let (mut result, runtime) = execute(PHASE1_COMPUTED_REWRITE);
        let ids = atomic_rewrite_cites_mut(atomic_rewrite_mut(&mut result.statement_results[1]));
        if duplicate {
            ids.push(ids[0]);
        } else {
            ids.clear();
        }
        let error = compile_run(&result, &runtime, "phase1_changed_rewrite_cites")
            .expect_err("recorded rewrite citations cannot disappear or duplicate");
        assert_eq!(error.route, "AtomicRewrite/Citations");
    }
}

#[test]
fn phase1_closed_atomic_rewrite_rejects_wrong_and_unused_source_equalities() {
    let source = "let computed = 2 + 3\nlet other_offset = 3\ncomputed $in C\n";
    for unused in [false, true] {
        let (mut result, runtime) = execute(source);
        let other = let_definition(&result.statement_results[1]).stored_fact_ids[0];
        let ids = atomic_rewrite_cites_mut(atomic_rewrite_mut(&mut result.statement_results[2]));
        if unused {
            ids.push(other);
        } else {
            ids[0] = other;
        }
        let error = compile_run(&result, &runtime, "phase1_unrelated_rewrite_equality")
            .expect_err("rewrite must consume exactly its recorded source equalities");
        assert_eq!(
            error.route,
            if unused {
                "AtomicRewrite/CitationOrder"
            } else {
                "AtomicRewrite/ClosedTopLevelCitation"
            }
        );
    }
}

#[test]
fn phase1_known_atomic_rewrite_rejects_discontinuous_incomplete_and_reordered_paths() {
    for change in ["reorder", "missing_first", "missing_last"] {
        let (mut result, runtime) = execute(PHASE1_CARRIER_REWRITE);
        let ids = atomic_rewrite_cites_mut(atomic_rewrite_mut(&mut result.statement_results[2]));
        assert_eq!(ids.len(), 2);
        match change {
            "reorder" => ids.swap(0, 1),
            "missing_first" => {
                ids.remove(0);
            }
            "missing_last" => {
                ids.pop();
            }
            _ => unreachable!(),
        }
        let error =
            compile_run(&result, &runtime, "phase1_changed_known_rewrite_path").expect_err(change);
        assert_eq!(
            error.route,
            if change == "missing_last" {
                "AtomicRewrite/PathEndpoint"
            } else {
                "AtomicRewrite/PathOrder"
            }
        );
    }
}

#[test]
fn phase1_atomic_rewrite_requires_the_exact_residual_family_and_child_subject() {
    let (mut result, runtime) = execute("5 != 0\nlet computed = 2 + 3\ncomputed $in C\n");
    let other_family = atomic_fact_from_statement(&result.statement_results[0]);
    match atomic_rewrite_mut(&mut result.statement_results[2]) {
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(
            proof,
        ) => proof.rewritten_fact = Fact::AtomicFact(other_family),
        _ => panic!("closed alias rewrite"),
    }
    let error = compile_run(&result, &runtime, "phase1_changed_rewrite_family")
        .expect_err("membership rewrite cannot become inequality");
    assert_eq!(error.route, "AtomicRewrite/Family");

    let (mut result, runtime) = execute(PHASE1_COMPUTED_REWRITE);
    match atomic_rewrite_mut(&mut result.statement_results[1]) {
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(
            proof,
        ) => match &mut proof.rewritten_fact {
            Fact::AtomicFact(AtomicFact::InFact(fact)) => fact.element = number_object("6"),
            _ => panic!("membership residual"),
        },
        _ => panic!("closed alias rewrite"),
    }
    let error = compile_run(&result, &runtime, "phase1_changed_rewrite_residual")
        .expect_err("genuine residual proof for five does not certify six");
    assert_eq!(error.route, "AtomicRewrite/ChildSubject");
}

#[test]
fn phase1_computed_rhs_rewrite_requires_the_actual_closed_endpoint() {
    let (mut result, runtime) = execute("let computed = 2 + 3\n6 $in C\ncomputed $in C\n");
    let six = match result.statement_results.remove(1) {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => proof,
        _ => panic!("genuine primitive six-membership proof"),
    };
    let residual = Fact::AtomicFact(match &six.verify_result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof.fact.clone(),
            _ => panic!("six member success"),
        },
        _ => panic!("atomic six membership"),
    });
    match atomic_rewrite_mut(&mut result.statement_results[1]) {
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(
            proof,
        ) => {
            proof.rewritten_fact = residual;
            proof.proof_of_rewritten_fact = six.verify_result;
        }
        _ => panic!("computed alias closed rewrite"),
    }
    let error = compile_run(&result, &runtime, "phase1_changed_closed_endpoint").expect_err(
        "a genuine proof that six is complex cannot replace the selected closed endpoint two plus three",
    );
    assert_eq!(error.route, "AtomicRewrite/ClosedTopLevelCitation");
}

#[test]
fn phase2_computed_value_equality_replays_the_selected_subterm_rewrite() {
    let (result, runtime) = execute("let computed = 2 + 3\ncomputed + 1 = 6\n");
    assert!(matches!(
        &equality_proof(&fact_statement(&result.statement_results[1]).verify_result).searched_proof,
        EqualFactSearchedProof::ByBuiltinRewrite(_)
    ));
    let output = compile_run(&result, &runtime, "phase2_computed_alias_sum").expect(
        "the selected closed-subterm rewrite has exact live citation and residual evidence",
    );
    assert!(output.contains("congrArg₂ M.addValue"));
    if let Some(directory) = std::env::var_os("LITEX_LEAN_PHASE2_OUTPUT_DIR") {
        std::fs::write(
            std::path::PathBuf::from(directory).join("computed_alias_sum.lean"),
            output,
        )
        .expect("write requested actual alias-sum compiler artifact");
    }
}

fn atomic_fact_from_statement(result: &ExecStmtResult) -> AtomicFact {
    match &fact_statement(result).verify_result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof.fact.clone(),
            _ => panic!("successful atomic fact"),
        },
        _ => panic!("atomic result"),
    }
}

fn atomic_rewrite_mut(
    result: &mut ExecStmtResult,
) -> &mut AtomicExceptEqualityFactSearchProofByBuiltinRewrite {
    let fact = match result {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => proof,
        _ => panic!("successful atomic statement"),
    };
    match &mut atomic_proof_mut(&mut fact.verify_result).searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRewrite(proof) => proof,
        _ => panic!("actual atomic builtin rewrite winner"),
    }
}

fn atomic_rewrite_cites_mut(
    proof: &mut AtomicExceptEqualityFactSearchProofByBuiltinRewrite,
) -> &mut Vec<FactId> {
    match proof {
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(
            proof,
        ) => &mut proof.cited_equal_fact_ids,
        AtomicExceptEqualityFactSearchProofByBuiltinRewrite::KnownEqualObjSubstitution(proof) => {
            &mut proof.cited_equal_fact_ids
        }
        _ => panic!("bounded equality rewrite adapter"),
    }
}

fn number_object(value: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(value.to_string())))
}

fn replace_wd_subject(wd: &mut ObjWellDefinedProof, replacement: Obj) {
    match wd {
        ObjWellDefinedProof::ByKnown { obj, .. } | ObjWellDefinedProof::ByDef { obj, .. } => {
            *obj = replacement
        }
    }
}

fn fact_statement(result: &ExecStmtResult) -> &ExecFactStmtSuccessResult {
    match result {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => proof,
        _ => panic!("successful fact statement"),
    }
}

fn let_definition(result: &ExecStmtResult) -> &ExecLetObjStmtSuccessResult {
    match result {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(proof)),
        )) => proof,
        _ => panic!("successful let definition"),
    }
}

fn let_definition_mut(result: &mut ExecStmtResult) -> &mut ExecLetObjStmtSuccessResult {
    match result {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::LetObj(ExecLetObjStmtResult::Success(proof)),
        )) => proof,
        _ => panic!("successful let definition"),
    }
}

fn have_equal_mut(result: &mut ExecStmtResult) -> &mut ExecHaveObjEqualStmtSuccessResult {
    match result {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjEqual(ExecHaveObjEqualStmtResult::Success(proof)),
        )) => proof,
        _ => panic!("successful typed value definition"),
    }
}

fn named_theorem_mut(result: &mut ExecStmtResult) -> &mut ExecDefThmStmtSuccess {
    match result {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
            ExecDefThmStmtResult::Success(proof),
        )) => proof,
        _ => panic!("successful named theorem"),
    }
}

fn theorem_goal_wd_mut(proof: &mut ExecDefThmStmtSuccess) -> &mut ForallFactWellDefinedProof {
    match &mut proof.goal_wd {
        VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(proof)) => proof,
        _ => panic!("actual forall goal formation"),
    }
}

fn by_theorem(result: &ExecStmtResult) -> &ExecByThmStmtSuccess {
    match result {
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))) => proof,
        _ => panic!("successful explicit theorem selection"),
    }
}

fn by_theorem_mut(result: &mut ExecStmtResult) -> &mut ExecByThmStmtSuccess {
    match result {
        ExecStmtResult::By(ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof))) => proof,
        _ => panic!("successful explicit theorem selection"),
    }
}

fn equality_path_mut(result: &mut VerifyFactResult) -> &mut KnownEqualityPathProof {
    match &mut equality_proof_mut(result).searched_proof {
        EqualFactSearchedProof::ByEquivalenceClass(
            EqualFactSearchedProofByEquivalenceClass::KnownPath(proof),
        ) => proof,
        _ => panic!("actual known oriented equality path"),
    }
}

fn forall_proof(result: &ExecStmtResult) -> &VerifyForallFactSuccess {
    match result {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => {
            match &success.verify_result {
                VerifyFactResult::ForallFact(proof) => match proof.as_ref() {
                    VerifyForallFactResult::Success(
                        VerifyForallFactProof::ByLocalIntroduction(proof),
                    ) => proof,
                    _ => panic!("local-introduction forall"),
                },
                _ => panic!("forall result"),
            }
        }
        _ => panic!("successful fact"),
    }
}

fn equality_proof(result: &VerifyFactResult) -> &VerifyEqualitySuccess {
    match result {
        VerifyFactResult::Equality(proof) => match proof.as_ref() {
            VerifyEqualityResult::Success(proof) => proof,
            VerifyEqualityResult::Failed(_) => panic!("verified equality"),
        },
        _ => panic!("equality result"),
    }
}

fn equality_proof_mut(result: &mut VerifyFactResult) -> &mut VerifyEqualitySuccess {
    match result {
        VerifyFactResult::Equality(proof) => match proof.as_mut() {
            VerifyEqualityResult::Success(proof) => proof,
            VerifyEqualityResult::Failed(_) => panic!("verified equality"),
        },
        _ => panic!("equality result"),
    }
}

fn atomic_proof_mut(result: &mut VerifyFactResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    match result {
        VerifyFactResult::AtomicExceptEquality(proof) => match proof.as_mut() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof,
            VerifyAtomicExceptEqualityFactResult::Failed(_) => panic!("verified atomic"),
        },
        _ => panic!("atomic result"),
    }
}

fn forall_proof_mut(result: &mut ExecStmtResult) -> &mut VerifyForallFactSuccess {
    match result {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(success)) => {
            match &mut success.verify_result {
                VerifyFactResult::ForallFact(proof) => match proof.as_mut() {
                    VerifyForallFactResult::Success(
                        VerifyForallFactProof::ByLocalIntroduction(proof),
                    ) => proof,
                    _ => panic!("local-introduction forall"),
                },
                _ => panic!("forall result"),
            }
        }
        _ => panic!("successful fact"),
    }
}

// These sources are the independently verified phase-2 drafts, kept inline so
// a public Rust test does not depend on the ignored local scripts workspace.
const PHASE2_HALF: &str = "have half Q = 1 / 2\nhalf + half = 1\n";
const PHASE2_HIERARCHY: &str = "forall n N:\n    n $in Z\nforall z Z:\n    z $in Q\nforall q Q:\n    q $in R\nforall r R:\n    r $in C\n";
const PHASE2_DIVISION: &str = "forall a,b Q:\n    b != 0\n    =>:\n        a / b $in Q\n";
const PHASE2_SQUARES: &str = "forall x R:\n    0 <= x^2\nforall x R:\n    x^2 >= 0\n";
const PHASE2_TRANS: &str = "forall a,b,c R:\n    a <= b\n    b <= c\n    =>:\n        a <= c\n";
const PHASE2_MONOTONE: &str = "forall a,b,t R:\n    a <= b\n    =>:\n        a + t <= b + t\n";
const PHASE2_HAVE: &str = "have arbitrary_real R\narbitrary_real = arbitrary_real\narbitrary_real + 0 = arbitrary_real\narbitrary_real >= arbitrary_real\n";
const PHASE2_Q_TRANSPORT: &str =
    "forall u,v C:\n    u = v\n    u $in Q\n    =>:\n        v $in Q\n";
const PHASE2_CLOSED_ORDER: &str = "1 / 3 < 1 / 2\n2 >= 1\n";

use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_rewrite_result::{
    ClosedNumericEqualSubstitutionBuiltinRewriteProof, EqualitySearchProofByBuiltinRewrite,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::greater_equal::GreaterEqualFactSearchProofByBuiltinRule;

#[test]
fn phase2_all_verified_problem_profiles_emit_replayed_artifacts() {
    let cases = [
        ("numeric_hierarchy", PHASE2_HIERARCHY),
        (
            "exact_fractions_and_decimals",
            "1 / 3 + 1 / 6 = 1 / 2\n0.5 = 1 / 2\n1 / 3 != 0.333\n",
        ),
        ("nonzero_rational_division", PHASE2_DIVISION),
        ("real_squares_nonnegative", PHASE2_SQUARES),
        ("weak_order_transitivity", PHASE2_TRANS),
        ("addition_preserves_weak_order", PHASE2_MONOTONE),
        (
            "weak_order_duality",
            "forall a,b R:\n    a <= b\n    =>:\n        b >= a\n",
        ),
        ("rational_membership_transport", PHASE2_Q_TRANSPORT),
        ("arbitrary_real_laws", PHASE2_HAVE),
        ("typed_rational_half", PHASE2_HALF),
        (
            "positive_real_is_nonzero",
            "forall positive_real R:\n    positive_real > 0\n    =>:\n        positive_real != 0\n",
        ),
        ("closed_real_order", PHASE2_CLOSED_ORDER),
    ];
    for (name, source) in cases {
        let (result, runtime) = execute(source);
        let output = compile_run(&result, &runtime, &format!("phase2_{name}"))
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        assert!(!output.contains("sorry"));
        assert!(!output.contains("admit"));
        if let Some(directory) = std::env::var_os("LITEX_LEAN_PHASE2_OUTPUT_DIR") {
            let directory = std::path::PathBuf::from(directory);
            assert!(
                directory.is_absolute(),
                "explicit Lean gate directory must be absolute"
            );
            std::fs::create_dir_all(&directory).expect("create requested phase2 gate directory");
            std::fs::write(directory.join(format!("{name}.lean")), output)
                .expect("write requested actual compiler artifact");
        }
    }
}

#[test]
fn phase2_typed_half_uses_the_actual_closed_substitution_and_closed_child() {
    let (mut result, runtime) = execute(PHASE2_HALF);
    let equality_id = have_equal_mut(&mut result.statement_results[0])
        .store_and_infer_result
        .stored_fact_ids[1];
    let proof = phase2_half_rewrite_mut(&mut result.statement_results[1]);
    assert_eq!(proof.cited_equal_fact_ids, vec![equality_id]);
    let child = equality_proof(&proof.residual_equal);
    assert_eq!(child.fact.left.ir(), proof.rewritten_left.ir());
    assert_eq!(child.fact.right.ir(), proof.rewritten_right.ir());
    assert!(matches!(
        &child.searched_proof,
        EqualFactSearchedProof::ByClosedCalculation(_)
    ));
    assert!(compile_run(&result, &runtime, "phase2_half_exact_route").is_ok());
}

#[test]
fn phase2_half_substitution_rejects_deleted_duplicate_wrong_and_unused_citations() {
    let source = "let other_value = 2\nhave half Q = 1 / 2\nhalf + half = 1\n";
    for change in ["deleted", "duplicate", "wrong", "unused"] {
        let (mut result, runtime) = execute(source);
        let other = let_definition(&result.statement_results[0]).stored_fact_ids[0];
        let ids =
            &mut phase2_half_rewrite_mut(&mut result.statement_results[2]).cited_equal_fact_ids;
        match change {
            "deleted" => ids.clear(),
            "duplicate" => ids.push(ids[0]),
            "wrong" => ids[0] = other,
            "unused" => ids.push(other),
            _ => unreachable!(),
        }
        phase2_rejected(&result, &runtime, change, &["EqualityRewrite/", "FactId/"]);
    }
}

#[test]
fn phase2_two_closed_aliases_preserve_source_substitution_order() {
    let source =
        "have first_half Q = 1 / 2\nhave second_half Q = 1 / 2\nfirst_half + second_half = 1\n";
    let (mut result, runtime) = execute(source);
    assert!(compile_run(&result, &runtime, "phase2_two_half_aliases").is_ok());
    let ids = &mut phase2_half_rewrite_mut(&mut result.statement_results[2]).cited_equal_fact_ids;
    assert_eq!(ids.len(), 2);
    ids.swap(0, 1);
    phase2_rejected(
        &result,
        &runtime,
        "phase2_reordered_half_substitution",
        &["EqualityRewrite/CitationOrder"],
    );
}

#[test]
fn phase2_half_substitution_requires_exact_residual_and_scalar_evidence() {
    let (mut result, runtime) = execute(PHASE2_HALF);
    phase2_half_rewrite_mut(&mut result.statement_results[1]).rewritten_left = number_object("2");
    phase2_rejected(
        &result,
        &runtime,
        "phase2_changed_half_residual",
        &["EqualityRewrite/Residual"],
    );

    let (mut result, runtime) = execute(PHASE2_HALF);
    let child = equality_proof_mut(
        &mut phase2_half_rewrite_mut(&mut result.statement_results[1]).residual_equal,
    );
    match &mut child.searched_proof {
        EqualFactSearchedProof::ByClosedCalculation(proof) => match &mut proof.values {
            ClosedValuePair::Decimal { right, .. } => *right = "2".into(),
            _ => panic!("actual half-sum decimal certificate"),
        },
        _ => panic!("actual closed residual child"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_changed_half_scalar",
        &["ClosedEquality/"],
    );
}

#[test]
fn phase2_half_substitution_cannot_replace_its_child_by_an_unrelated_true_equality() {
    let source = "2 = 2\n2 = 2\nhave half Q = 1 / 2\nhalf + half = 1\n";
    let (mut result, runtime) = execute(source);
    let unrelated = match result.statement_results.remove(1) {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => proof.verify_result,
        _ => panic!("actual unrelated equality"),
    };
    phase2_half_rewrite_mut(&mut result.statement_results[2]).residual_equal = unrelated;
    phase2_rejected(
        &result,
        &runtime,
        "phase2_unrelated_half_child",
        &["EqualityRewrite/Residual"],
    );
}

#[test]
fn phase2_half_substitution_rejects_a_closed_scope_equality_origin() {
    let source = "forall local_value Q:\n    local_value = 1 / 2\n    =>:\n        local_value = local_value\nhave half Q = 1 / 2\nhalf + half = 1\n";
    let (mut result, runtime) = execute(source);
    let closed_id = forall_proof(&result.statement_results[0]).assumed_dom_facts[0]
        .store_and_infer
        .primary_fact_id();
    phase2_half_rewrite_mut(&mut result.statement_results[2]).cited_equal_fact_ids[0] = closed_id;
    phase2_rejected(
        &result,
        &runtime,
        "phase2_closed_half_origin",
        &["FactId/Resolution"],
    );
}

#[test]
fn phase2_typed_half_preserves_the_original_division_wd_guard() {
    let (mut result, runtime) = execute(PHASE2_HALF);
    let value_wd = &mut have_equal_mut(&mut result.statement_results[0]).equal_to_well_defined[0];
    match value_wd {
        VerifyObjWellDefinedResult::Success(ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Div(proof),
                ),
            ..
        }) => {
            proof.requirement_fact_verified.remove(0);
        }
        _ => panic!("actual rational-half division WD"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_missing_half_division_guard",
        &["WD/Arithmetic"],
    );
}

#[test]
fn phase2_hierarchy_and_rational_closure_preserve_structural_carriers() {
    let (mut result, runtime) = execute(PHASE2_HIERARCHY);
    for statement in &result.statement_results {
        let proof = phase2_atomic(&forall_proof(statement).proved_then_facts[0].verify_result);
        assert!(matches!(
            &proof.searched_proof,
            AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(
                StructuralMembershipProof {
                    reason: StructuralMembershipReason::StandardSuperset(_),
                    ..
                }
            )
        ));
    }
    phase2_structural_mut(
        &mut forall_proof_mut(&mut result.statement_results[1]).proved_then_facts[0].verify_result,
    )
    .set = StandardSet::C;
    phase2_rejected(
        &result,
        &runtime,
        "phase2_changed_hierarchy_set",
        &["StructuralMembership/", "StructuralMembership"],
    );

    let (mut result, runtime) = execute(PHASE2_DIVISION);
    let structural = phase2_structural_mut(
        &mut forall_proof_mut(&mut result.statement_results[0]).proved_then_facts[0].verify_result,
    );
    match &mut structural.reason {
        StructuralMembershipReason::Div { left, .. } => left.set = StandardSet::R,
        _ => panic!("actual rational field division closure"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_changed_rational_operand_domain",
        &["StructuralMembership/", "StructuralMembership"],
    );
}

#[test]
fn phase2_rational_division_closure_cannot_discard_denominator_legality() {
    let (mut result, runtime) = execute(PHASE2_DIVISION);
    let goal = atomic_proof_mut(
        &mut forall_proof_mut(&mut result.statement_results[0]).proved_then_facts[0].verify_result,
    );
    match &mut goal.well_defined_proof.well_defined_of_each_parameter[0] {
        ObjWellDefinedProof::ByDef {
            proof:
                ObjWellDefinedProofByDef::ArithmeticOperator(
                    ArithmeticOperatorObjWellDefinedProofByDef::Div(proof),
                ),
            ..
        } => {
            proof.requirement_fact_verified.remove(0);
        }
        _ => panic!("actual rational quotient object WD"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_missing_rational_guard",
        &["WD/Arithmetic"],
    );
}

#[test]
fn phase2_arbitrary_have_retains_generic_input_and_its_nonempty_evidence() {
    let (mut result, runtime) = execute(PHASE2_HAVE);
    let have = phase2_have_mut(&mut result.statement_results[0]);
    assert!(matches!(
        &have.groups[0].nonempty_check,
        ParamTypeFactCheckResult::Obj(_)
    ));
    assert_eq!(
        have.groups[0].defined_params.store_and_infer_results.len(),
        1
    );
    assert!(std::rc::Rc::ptr_eq(
        &have.groups[0].defined_params.store_and_infer_results[0],
        &have.store_and_infer_result.store_and_infer_results[0]
    ));
    let output = compile_run(&result, &runtime, "phase2_generic_real_context")
        .expect("arbitrary real context");
    assert!(output.contains("Litex.Representation"));
    assert!(output.contains("Litex.Obj"));
    assert!(!output.contains("noncomputable def _object_"));
    // The real value is an exported context input. Zero occurs only as the
    // certified additive identity and the nonempty-carrier witness.
    assert!(output.contains("variable {_Host"));
}

#[test]
fn phase2_arbitrary_have_rejects_missing_and_wrong_nonempty_checks() {
    let (mut result, runtime) = execute(PHASE2_HAVE);
    phase2_have_mut(&mut result.statement_results[0]).groups[0].nonempty_check =
        ParamTypeFactCheckResult::Set;
    phase2_rejected(
        &result,
        &runtime,
        "phase2_missing_nonempty",
        &["Have/NonemptyCheck"],
    );

    let (mut result, runtime) = execute(PHASE2_HAVE);
    let have = phase2_have_mut(&mut result.statement_results[0]);
    match &mut have.groups[0].nonempty_check {
        ParamTypeFactCheckResult::Obj(result) => match &mut atomic_proof_mut(result).searched_proof
        {
            AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
                AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact(
                    IsNonemptySetFactSearchProofByBuiltinRule::StandardSetNonempty(proof),
                ),
            ) => proof.target_set = StandardSet::Q,
            _ => panic!("actual real-standard-set nonempty proof"),
        },
        _ => panic!("actual numeric nonempty check"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_wrong_nonempty_carrier",
        &["Nonempty/", "Have/Nonempty", "Atomic/"],
    );
}

#[test]
fn phase2_arbitrary_have_rejects_missing_store_trees_and_divergent_views() {
    for change in [
        "aggregate_ids",
        "group_ids",
        "aggregate_tree",
        "both_trees",
        "both_ids",
    ] {
        let (mut result, runtime) = execute(PHASE2_HAVE);
        let have = phase2_have_mut(&mut result.statement_results[0]);
        match change {
            "aggregate_ids" => have.store_and_infer_result.stored_fact_ids.clear(),
            "group_ids" => have.groups[0].defined_params.stored_fact_ids.clear(),
            "aggregate_tree" => have.store_and_infer_result.store_and_infer_results.clear(),
            "both_trees" => {
                have.groups[0]
                    .defined_params
                    .store_and_infer_results
                    .clear();
                have.store_and_infer_result.store_and_infer_results.clear();
            }
            "both_ids" => {
                have.groups[0].defined_params.stored_fact_ids.clear();
                have.store_and_infer_result.stored_fact_ids.clear();
            }
            _ => unreachable!(),
        }
        phase2_rejected(&result, &runtime, change, &["Have/", "Parameters/"]);
    }
}

#[test]
fn phase2_arbitrary_have_header_identity_must_match_its_actual_store() {
    let (mut result, runtime) = execute(PHASE2_HAVE);
    phase2_have_mut(&mut result.statement_results[0])
        .statement
        .param_def
        .groups[0]
        .params[0]
        .id = IdentifierId::new(u64::MAX);
    phase2_rejected(
        &result,
        &runtime,
        "phase2_changed_have_header",
        &["Parameters/Subject"],
    );
}

#[test]
fn phase2_natural_parameter_cannot_lose_a_captured_inference_identity() {
    let (mut result, runtime) = execute(PHASE2_HIERARCHY);
    let parameters = &mut forall_proof_mut(&mut result.statement_results[0])
        .introduced_params
        .defined_params;
    assert!(
        parameters.stored_fact_ids.len() > 1,
        "actual natural membership has a nonnegative inference projection"
    );
    parameters.stored_fact_ids.pop();
    phase2_rejected(
        &result,
        &runtime,
        "phase2_deleted_natural_inference_id",
        &["Parameters/StoreCapture", "Forall/"],
    );
}

#[test]
fn phase2_closed_order_consumes_actual_comparison_certificates() {
    let (mut result, runtime) = execute(PHASE2_CLOSED_ORDER);
    let proof =
        atomic_proof_mut(&mut fact_statement_mut(&mut result.statement_results[0]).verify_result);
    match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
            ClosedAtomicExceptEqualityCalculationProof::Less(proof),
        ) => {
            proof.comparison = crate::rational_expression::NumberCompareResult::Greater;
        }
        _ => panic!("actual closed exact rational order certificate"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_changed_comparison_direction",
        &["Closed", "Order/", "Atomic/"],
    );

    let (mut result, runtime) = execute(PHASE2_CLOSED_ORDER);
    let proof =
        atomic_proof_mut(&mut fact_statement_mut(&mut result.statement_results[1]).verify_result);
    match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
            ClosedAtomicExceptEqualityCalculationProof::GreaterEqual(proof),
        ) => match &mut proof.values {
            ClosedValuePair::Decimal { left, .. } => *left = "0".into(),
            _ => panic!("actual primitive decimal value pair"),
        },
        _ => panic!("actual closed weak-order certificate"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_changed_closed_order_value",
        &["Closed", "Order/", "Atomic/"],
    );
}

#[test]
fn phase2_closed_order_ignores_presentation_strings() {
    let (mut result, runtime) = execute(PHASE2_CLOSED_ORDER);
    let expected =
        compile_run(&result, &runtime, "phase2_presentation").expect("actual typed values");
    for statement in &mut result.statement_results {
        let proof = atomic_proof_mut(&mut fact_statement_mut(statement).verify_result);
        match &mut proof.searched_proof {
            AtomicExceptEqualityFactSearchedProof::ByClosedCalculation(
                ClosedAtomicExceptEqualityCalculationProof::Less(p)
                | ClosedAtomicExceptEqualityCalculationProof::GreaterEqual(p),
            ) => {
                p.left_normal = "changed presentation".into();
                p.right_normal = "unrelated display".into();
            }
            _ => panic!("actual closed comparison variants"),
        }
    }
    assert_eq!(
        compile_run(&result, &runtime, "phase2_presentation")
            .expect("presentation is not evidence"),
        expected
    );
}

#[test]
fn phase2_closed_order_rejects_a_changed_fact_family_even_with_true_value_payload() {
    let (mut result, runtime) = execute(PHASE2_CLOSED_ORDER);
    let source =
        match &phase2_atomic(&fact_statement(&result.statement_results[0]).verify_result).fact {
            AtomicFact::LessFact(fact) => fact.clone(),
            _ => panic!("closed less source"),
        };
    let statement = fact_statement_mut(&mut result.statement_results[0]);
    let changed = AtomicFact::GreaterFact(GreaterFact {
        fact_id: source.fact_id,
        left: source.left,
        right: source.right,
        line_file: source.line_file,
    });
    atomic_proof_mut(&mut statement.verify_result).fact = changed.clone();
    match &mut statement.store_and_infer_result.store {
        StoreFactResult::AtomicFact(store) => store.fact = changed,
        _ => panic!("atomic store"),
    };
    phase2_rejected(
        &result,
        &runtime,
        "phase2_changed_order_family",
        &["Closed", "Order/", "Atomic/", "WD/"],
    );
}

#[test]
fn phase2_order_transitivity_replays_oriented_actual_premise_ids() {
    let (mut result, runtime) = execute(PHASE2_TRANS);
    let proof = atomic_proof_mut(
        &mut forall_proof_mut(&mut result.statement_results[0]).proved_then_facts[0].verify_result,
    );
    match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::LessEqualTransitivity(proof),
            ),
        ) => std::mem::swap(
            &mut proof.left_to_mid_cite_fact_id,
            &mut proof.mid_to_right_cite_fact_id,
        ),
        _ => panic!("actual weak transitivity route"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_reversed_transitivity_citations",
        &["Order/", "Atomic/", "FactId/"],
    );
}

#[test]
fn phase2_order_addition_requires_its_original_order_premise() {
    let (mut result, runtime) = execute(PHASE2_MONOTONE);
    let proof = atomic_proof_mut(
        &mut forall_proof_mut(&mut result.statement_results[0]).proved_then_facts[0].verify_result,
    );
    let premise = match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::AddRightCongruence(proof),
            ),
        ) => &mut proof.premise_proof,
        _ => panic!("actual add-right monotonicity proof"),
    };
    match &mut atomic_proof_mut(premise).searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => {
            proof.cite_fact_id = FactId::new(u64::MAX)
        }
        _ => panic!("actual stored order premise citation"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_missing_addition_premise",
        &["FactId/Resolution"],
    );
}

#[test]
fn phase2_square_rule_cannot_lose_its_real_base_citation() {
    let (mut result, runtime) = execute(PHASE2_SQUARES);
    let proof = atomic_proof_mut(
        &mut forall_proof_mut(&mut result.statement_results[0]).proved_then_facts[0].verify_result,
    );
    let real = match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::EvenPowNonnegative(proof),
            ),
        ) => &mut proof.base_in_real_proof,
        _ => panic!("actual even-power nonnegative primitive"),
    };
    match &mut atomic_proof_mut(real).searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => {
            proof.cite_fact_id = FactId::new(u64::MAX)
        }
        _ => panic!("actual base-real citation"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_missing_square_real_proof",
        &["FactId/Resolution"],
    );
}

#[test]
fn phase2_order_reflexivity_uses_the_recorded_same_object() {
    let (mut result, runtime) = execute(PHASE2_HAVE);
    let proof =
        atomic_proof_mut(&mut fact_statement_mut(&mut result.statement_results[3]).verify_result);
    match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact(
                GreaterEqualFactSearchProofByBuiltinRule::OrderReflexivity(proof),
            ),
        ) => proof.repeated_object = number_object("0"),
        _ => panic!("actual generic real >= reflexivity"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_changed_reflexive_subject",
        &["Order/", "Atomic/"],
    );
}

#[test]
fn phase2_q_membership_transport_cannot_drop_its_known_fact_citation() {
    let (mut result, runtime) = execute(PHASE2_Q_TRANSPORT);
    let proof = atomic_proof_mut(
        &mut forall_proof_mut(&mut result.statement_results[0]).proved_then_facts[0].verify_result,
    );
    match &mut proof.searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => {
            proof.cite_fact_id = FactId::new(u64::MAX)
        }
        _ => panic!("actual rational-membership equality transport citation"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_missing_q_transport_fact",
        &["FactId/Resolution"],
    );
}

fn phase2_rejected(result: &RunLitexCodeResult, runtime: &Runtime, name: &str, families: &[&str]) {
    let error = compile_run(result, runtime, "phase2_changed_evidence").expect_err(name);
    assert!(
        families
            .iter()
            .any(|prefix| error.route.starts_with(prefix)),
        "{name}: {error:?}"
    );
}

fn phase2_atomic(result: &VerifyFactResult) -> &VerifyAtomicExceptEqualityFactSuccess {
    match result {
        VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => proof,
            _ => panic!("successful atomic evidence"),
        },
        _ => panic!("atomic evidence"),
    }
}

fn phase2_structural_mut(result: &mut VerifyFactResult) -> &mut StructuralMembershipProof {
    match &mut atomic_proof_mut(result).searched_proof {
        AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) => proof,
        _ => panic!("actual source structural membership"),
    }
}

fn phase2_half_rewrite_mut(
    statement: &mut ExecStmtResult,
) -> &mut ClosedNumericEqualSubstitutionBuiltinRewriteProof {
    match &mut equality_proof_mut(&mut fact_statement_mut(statement).verify_result).searched_proof {
        EqualFactSearchedProof::ByBuiltinRewrite(
            EqualitySearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(proof),
        ) => proof,
        _ => panic!("actual closed numeric equality substitution"),
    }
}

fn phase2_have_mut(
    statement: &mut ExecStmtResult,
) -> &mut ExecHaveObjInNonemptySetStmtSuccessResult {
    match statement {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefineObj(
            ExecDefineObjStmtResult::HaveObjInNonemptySet(
                ExecHaveObjInNonemptySetStmtResult::Success(proof),
            ),
        )) => proof,
        _ => panic!("actual arbitrary-have result"),
    }
}

fn fact_statement_mut(statement: &mut ExecStmtResult) -> &mut ExecFactStmtSuccessResult {
    match statement {
        ExecStmtResult::Fact(ExecFactStmtResult::Success(proof)) => proof,
        _ => panic!("successful fact statement"),
    }
}

#[test]
fn phase2_order_wd_keeps_both_real_requirements_in_source_order() {
    for change in ["missing", "reordered"] {
        let (mut result, runtime) = execute(PHASE2_SQUARES);
        let square = atomic_proof_mut(
            &mut forall_proof_mut(&mut result.statement_results[0]).proved_then_facts[0]
                .verify_result,
        );
        let requirements = match &mut square.well_defined_proof.predicate_domain {
            PredicateDomainProof::ByRequirements(requirements) => requirements,
            _ => panic!("actual square order has explicit real-domain requirements"),
        };
        assert_eq!(requirements.len(), 2);
        if change == "missing" {
            requirements.pop();
        } else {
            requirements.swap(0, 1);
        }
        phase2_rejected(&result, &runtime, change, &["WD/OrderRealDomain"]);
    }
}

#[test]
fn phase2_even_power_tag_rejects_a_genuinely_well_defined_odd_power() {
    // The first equality constructs a genuine cubic object and its cached WD.
    // The first membership proves it real. The repeated membership supplies an
    // actual citation proof that can be moved into the forged order's WD stage.
    // The original source remains true; only the test's result values change.
    let source = "forall real_power_base R:\n    real_power_base^3 = real_power_base^3\n    real_power_base^3 $in R\n    real_power_base^3 $in R\n    real_power_base^3 $in R\n    0 <= real_power_base^2\n";
    let (mut result, runtime) = execute(source);
    let success = fact_statement_mut(&mut result.statement_results[0]);
    let forall = match &mut success.verify_result {
        VerifyFactResult::ForallFact(result) => match result.as_mut() {
            VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(forall)) => {
                forall
            }
            _ => panic!("actual locally introduced real-power source"),
        },
        _ => panic!("forall statement"),
    };
    let cubic_equality = equality_proof(&forall.proved_then_facts[0].verify_result);
    let cube = cubic_equality.fact.left.clone();
    // Consume a separate genuine cubic WD from a removable duplicate, so this
    // control does not assume whether the source chose ByDef or ByKnown.
    let mut cube_formation = forall.proved_then_facts.remove(3);
    forall.fact.then_facts.remove(3);
    let cube_wd = atomic_proof_mut(&mut cube_formation.verify_result)
        .well_defined_proof
        .well_defined_of_each_parameter
        .remove(0);
    match &cube_wd {
        ObjWellDefinedProof::ByKnown { obj, .. } | ObjWellDefinedProof::ByDef { obj, .. } => {
            assert_eq!(obj.ir(), cube.ir())
        }
    };

    // Reuse the actual repeated-membership result. Do not manufacture an In R
    // proof, a WD certificate, or a fresh source identity for the changed goal.
    let cube_member = forall.proved_then_facts.remove(2);
    forall.fact.then_facts.remove(2);
    let cube_member_fact = phase2_atomic(&cube_member.verify_result).fact.clone();
    match &cube_member_fact {
        AtomicFact::InFact(fact) => {
            assert_eq!(fact.element.ir(), cube.ir());
            assert_eq!(fact.set, Obj::StandardSet(StandardSet::R));
        }
        _ => panic!("actual cubic real-membership result"),
    }

    let square = atomic_proof_mut(&mut forall.proved_then_facts[2].verify_result);
    assert!(matches!(
        &square.searched_proof,
        AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
            AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact(
                LessEqualFactSearchProofByBuiltinRule::EvenPowNonnegative(_),
            ),
        )
    ));
    match &mut square.fact {
        AtomicFact::LessEqualFact(fact) => fact.right = cube.clone(),
        _ => panic!("actual weak square nonnegativity goal"),
    }
    square.well_defined_proof.well_defined_of_each_parameter[1] = cube_wd;
    match &mut square.well_defined_proof.predicate_domain {
        PredicateDomainProof::ByRequirements(requirements) => {
            assert_eq!(requirements.len(), 2);
            requirements[1].requirement = Fact::AtomicFact(cube_member_fact);
            requirements[1].result = Box::new(cube_member.verify_result);
        }
        _ => panic!("actual two-stage real-domain WD"),
    }

    // Keep every enclosing primary store and source conclusion aligned so the
    // counterfeit reaches the parity guard, rather than an incidental mismatch.
    let changed_goal = square.fact.clone();
    forall.fact.then_facts[2] = ExistOrAndChainAtomicFact::AtomicFact(changed_goal.clone());
    match &mut forall.proved_then_facts[2].store_and_infer.store {
        StoreFactResult::AtomicFact(stored) => stored.fact = changed_goal,
        _ => panic!("atomic order primary store"),
    }
    let changed_forall = forall.fact.clone();
    match &mut success.store_and_infer_result.store {
        StoreFactResult::ForallFact(stored) => stored.fact = changed_forall,
        _ => panic!("whole forall primary store"),
    }
    phase2_rejected(
        &result,
        &runtime,
        "phase2_odd_exponent_with_even_tag",
        &["Order/EvenPowerExponent"],
    );
}
