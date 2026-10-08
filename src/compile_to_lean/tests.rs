use super::compile_run;
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
