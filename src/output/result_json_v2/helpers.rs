use super::renderer::*;
use crate::prelude::*;

pub(super) fn verify_fact_kind(result: &SuccessVerifyFactResult) -> &'static str {
    match result {
        SuccessVerifyFactResult::AtomicFact(_) => "AtomicFact",
        SuccessVerifyFactResult::ExistFact(_) => "ExistFact",
        SuccessVerifyFactResult::OrFact(_) => "OrFact",
        SuccessVerifyFactResult::AndFact(_) => "AndFact",
        SuccessVerifyFactResult::ChainFact(_) => "ChainFact",
        SuccessVerifyFactResult::ForallFact(_) => "ForallFact",
        SuccessVerifyFactResult::ForallFactWithIff(_) => "ForallFactWithIff",
        SuccessVerifyFactResult::NotForallFact(_) => "NotForallFact",
    }
}

pub(super) fn unknown_fact_kind(result: &UnknownFactResult) -> &'static str {
    match result {
        UnknownFactResult::AtomicFact(_) => "AtomicFact",
        UnknownFactResult::ExistFact(_) => "ExistFact",
        UnknownFactResult::OrFact(_) => "OrFact",
        UnknownFactResult::AndFact(_) => "AndFact",
        UnknownFactResult::ChainFact(_) => "ChainFact",
        UnknownFactResult::ForallFact(_) => "ForallFact",
        UnknownFactResult::ForallFactWithIff(_) => "ForallFactWithIff",
        UnknownFactResult::NotForall(_) => "NotForallFact",
    }
}

pub(super) fn function_definition_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyFunctionDefinitionResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyFunctionDefinitionResult"),
        (
            "return_check".to_string(),
            renderer.stmt_result(&result.return_check),
        ),
        (
            "assumption_infers".to_string(),
            infer_result_value(&result.assumption_infers),
        ),
        string_field(
            "function_membership",
            result.function_membership.to_string(),
        ),
        string_field("defining_equality", result.defining_equality.to_string()),
    ])
}

pub(super) fn by_assignment_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByAssignmentResult,
) -> JsonValue {
    object(vec![
        ("assignment".to_string(), string_pairs(&result.assignment)),
        (
            "assumptions".to_string(),
            array(
                result
                    .assumptions
                    .iter()
                    .map(|assumption| {
                        object(vec![
                            string_field("fact", assumption.fact.to_string()),
                            string_field("fact_id", fact_id(assumption.fact_id)),
                            string_field("reason", assumption.reason.clone()),
                            ("infers".to_string(), infer_result_value(&assumption.infers)),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "domain_checks".to_string(),
            array(
                result
                    .domain_checks
                    .iter()
                    .map(|domain| {
                        object(vec![
                            string_field("fact", domain.fact.to_string()),
                            ("check".to_string(), renderer.stmt_result(&domain.check)),
                            (
                                "negated_check".to_string(),
                                domain
                                    .negated_check
                                    .as_ref()
                                    .map(|check| renderer.stmt_result(check))
                                    .unwrap_or(JsonValue::Null),
                            ),
                            ("satisfied".to_string(), JsonValue::Bool(domain.satisfied)),
                            (
                                "satisfied_infers".to_string(),
                                domain
                                    .satisfied_infers
                                    .as_ref()
                                    .map(infer_result_value)
                                    .unwrap_or(JsonValue::Null),
                            ),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "conclusion_checks".to_string(),
            renderer.stmt_results(&result.conclusion_checks),
        ),
    ])
}

pub(super) fn by_enumerate_finite_set_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByEnumerateFiniteSetResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByEnumerateFiniteSetResult"),
        ("parameters".to_string(), strings(&result.parameters)),
        (
            "parameter_sets".to_string(),
            strings(
                &result
                    .parameter_sets
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            ),
        ),
        string_field("prove_goal", result.prove_goal.clone()),
        (
            "assignments".to_string(),
            array(
                result
                    .assignments
                    .iter()
                    .map(|assignment| by_assignment_verification_value(renderer, assignment))
                    .collect(),
            ),
        ),
        string_field("generated_forall", result.generated_forall.clone()),
    ])
}

pub(super) fn by_for_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByForResult,
) -> JsonValue {
    match result {
        SuccessVerifyByForResult::Ranges(result) => object(vec![
            string_field("kind", "SuccessVerifyByForRangesResult"),
            (
                "parameters".to_string(),
                array(
                    result
                        .parameters
                        .iter()
                        .map(|parameter| {
                            object(vec![
                                string_field("kind", "SuccessVerifyByForRangeParameterResult"),
                                string_field("parameter", parameter.parameter.clone()),
                                string_field("range", parameter.range.to_string()),
                                string_field("evaluated_start", parameter.evaluated_start.clone()),
                                string_field("evaluated_end", parameter.evaluated_end.clone()),
                                (
                                    "enumerated_values".to_string(),
                                    strings(&parameter.enumerated_values),
                                ),
                            ])
                        })
                        .collect(),
                ),
            ),
            string_field("prove_goal", result.prove_goal.clone()),
            (
                "assignments".to_string(),
                array(
                    result
                        .assignments
                        .iter()
                        .map(|assignment| by_assignment_verification_value(renderer, assignment))
                        .collect(),
                ),
            ),
            string_field("generated_forall", result.generated_forall.clone()),
        ]),
        SuccessVerifyByForResult::CartesianProductOfListSets(result) => object(vec![
            string_field("kind", "SuccessVerifyByForCartesianProductOfListSetsResult"),
            string_field("parameter", result.parameter.clone()),
            (
                "factors".to_string(),
                strings(
                    &result
                        .factors
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>(),
                ),
            ),
            string_field("prove_goal", result.prove_goal.clone()),
            (
                "assignments".to_string(),
                array(
                    result
                        .assignments
                        .iter()
                        .map(|assignment| by_assignment_verification_value(renderer, assignment))
                        .collect(),
                ),
            ),
            string_field("generated_forall", result.generated_forall.clone()),
        ]),
    }
}

pub(super) fn by_enumerate_range_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByEnumerateRangeResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByEnumerateRangeResult"),
        string_field("element", result.element.to_string()),
        string_field("range", result.range.to_string()),
        string_field("membership_fact", result.membership_fact.to_string()),
        string_field("generated_cases", result.generated_cases.to_string()),
        (
            "membership_check".to_string(),
            renderer.stmt_result(&result.membership_check),
        ),
        (
            "endpoint_checks".to_string(),
            array(
                result
                    .endpoint_checks
                    .iter()
                    .map(|check| {
                        object(vec![
                            string_field("kind", "SuccessVerifyByEnumerateRangeEndpointResult"),
                            string_field(
                                "position",
                                match check.position {
                                    SuccessVerifyByEnumerateRangeEndpointPosition::Start => "Start",
                                    SuccessVerifyByEnumerateRangeEndpointPosition::End => "End",
                                },
                            ),
                            string_field("endpoint", check.endpoint.to_string()),
                            string_field(
                                "integer_membership_fact",
                                check.integer_membership_fact.to_string(),
                            ),
                            (
                                "verification".to_string(),
                                renderer.stmt_result(&check.verification),
                            ),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

pub(super) fn by_induc_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByInducResult,
) -> JsonValue {
    let proof = match &result.proof {
        SuccessVerifyByInducProofResult::IntegerUnstructured(proof) => object(vec![
            string_field("kind", "IntegerUnstructured"),
            ("strong".to_string(), JsonValue::Bool(proof.strong)),
            string_field("start", proof.start.clone()),
            (
                "base_assumptions".to_string(),
                string_pairs(&proof.base_assumptions),
            ),
            (
                "step_assumptions".to_string(),
                string_pairs(&proof.step_assumptions),
            ),
            (
                "proof_steps".to_string(),
                renderer.stmt_results(&proof.proof_steps),
            ),
            (
                "goals".to_string(),
                array(
                    proof
                        .goals
                        .iter()
                        .map(|goal| by_induc_goal_value(renderer, goal))
                        .collect(),
                ),
            ),
        ]),
        SuccessVerifyByInducProofResult::IntegerStructured(proof) => object(vec![
            string_field("kind", "IntegerStructured"),
            ("strong".to_string(), JsonValue::Bool(proof.strong)),
            string_field("start", proof.start.to_string()),
            (
                "start_in_z_check".to_string(),
                renderer.stmt_result(&proof.start_in_z_check),
            ),
            (
                "base".to_string(),
                structured_integer_induc_case_value(renderer, &proof.base),
            ),
            (
                "step".to_string(),
                structured_integer_induc_case_value(renderer, &proof.step),
            ),
        ]),
        SuccessVerifyByInducProofResult::FiniteSet(proof) => object(vec![
            string_field("kind", "FiniteSet"),
            (
                "base".to_string(),
                by_induc_case_value(renderer, &proof.base),
            ),
            (
                "step".to_string(),
                by_induc_case_value(renderer, &proof.step),
            ),
        ]),
    };
    object(vec![
        string_field("kind", "SuccessVerifyByInducResult"),
        string_field("parameter_binding", result.parameter_binding.to_string()),
        string_field("parameter", result.parameter.to_string()),
        (
            "prove_goals".to_string(),
            strings(
                &result
                    .prove_goals
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
            ),
        ),
        string_field("generated_forall", result.generated_forall.to_string()),
        ("proof".to_string(), proof),
    ])
}

pub(super) fn by_induc_goal_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByInducGoalResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByInducGoalResult"),
        string_field("source_goal", result.source_goal.to_string()),
        (
            "base_check".to_string(),
            renderer.stmt_result(&result.base_check),
        ),
        (
            "start_in_z_check".to_string(),
            renderer.stmt_result(&result.start_in_z_check),
        ),
        (
            "step_check".to_string(),
            renderer.stmt_result(&result.step_check),
        ),
        ("infers".to_string(), infer_result_value(&result.infers)),
    ])
}

pub(super) fn by_induc_case_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByInducCaseResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByInducCaseResult"),
        (
            "assumptions".to_string(),
            array(
                result
                    .assumptions
                    .iter()
                    .map(induc_assumption_value)
                    .collect(),
            ),
        ),
        (
            "assumption_infers".to_string(),
            infer_result_value(&result.assumption_infers),
        ),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "conclusions".to_string(),
            array(
                result
                    .conclusions
                    .iter()
                    .map(|conclusion| {
                        object(vec![
                            string_field("kind", "SuccessVerifyByInducConclusionResult"),
                            string_field("goal", conclusion.goal.to_string()),
                            ("check".to_string(), renderer.stmt_result(&conclusion.check)),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

fn induc_assumption_value(assumption: &SuccessVerifyByInducAssumptionResult) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByInducAssumptionResult"),
        string_field("fact", assumption.fact.to_string()),
        string_field("fact_id", assumption.fact_id.to_string()),
        string_field(
            "role",
            match assumption.role {
                SuccessVerifyByInducAssumptionRole::ParameterType => "ParameterType",
                SuccessVerifyByInducAssumptionRole::BaseCaseEquality => "BaseCaseEquality",
                SuccessVerifyByInducAssumptionRole::DomainLowerBound => "DomainLowerBound",
                SuccessVerifyByInducAssumptionRole::CarrierConstraint => "CarrierConstraint",
                SuccessVerifyByInducAssumptionRole::FreshInsertionElement => {
                    "FreshInsertionElement"
                }
                SuccessVerifyByInducAssumptionRole::InductionHypothesis => "InductionHypothesis",
                SuccessVerifyByInducAssumptionRole::StrongInductionHypothesis => {
                    "StrongInductionHypothesis"
                }
            },
        ),
        (
            "goal_index".to_string(),
            assumption
                .goal_index
                .map(JsonValue::Number)
                .unwrap_or(JsonValue::Null),
        ),
    ])
}

pub(super) fn structured_integer_induc_case_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByStructuredIntegerInducCaseResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByStructuredIntegerInducCaseResult"),
        (
            "assumptions".to_string(),
            array(
                result
                    .assumptions
                    .iter()
                    .map(induc_assumption_value)
                    .collect(),
            ),
        ),
        (
            "assumption_infers".to_string(),
            infer_result_value(&result.assumption_infers),
        ),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "conclusions".to_string(),
            array(
                result
                    .conclusions
                    .iter()
                    .map(|conclusion| {
                        object(vec![
                            string_field("kind", "SuccessVerifyByInducConclusionResult"),
                            string_field("goal", conclusion.goal.to_string()),
                            ("check".to_string(), renderer.stmt_result(&conclusion.check)),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

pub(super) fn by_extension_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByExtensionResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByExtensionResult"),
        string_field("left", result.left.clone()),
        string_field("right", result.right.clone()),
        string_field("prove_goal", result.prove_goal.clone()),
        string_field("left_to_right_subset", result.left_to_right_subset.clone()),
        string_field("right_to_left_subset", result.right_to_left_subset.clone()),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "left_to_right_check".to_string(),
            renderer.stmt_result(&result.left_to_right_check),
        ),
        (
            "right_to_left_check".to_string(),
            renderer.stmt_result(&result.right_to_left_check),
        ),
    ])
}

pub(super) fn prop_registration_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByPropRegistrationResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByPropRegistrationResult"),
        string_field("registration_type", result.registration_type.clone()),
        string_field("prop_name", result.prop_name.clone()),
        string_field("forall_fact", result.forall_fact.to_string()),
        (
            "well_definedness".to_string(),
            renderer.fact_well_definedness(&result.well_definedness),
        ),
        (
            "assumption_infers".to_string(),
            infer_result_value(&result.assumption_infers),
        ),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "forall_check".to_string(),
            renderer.stmt_result(&result.forall_check),
        ),
    ])
}

pub(super) fn optional_prop_registration(
    renderer: &mut StmtResultJsonV2,
    result: Option<&SuccessVerifyByPropRegistrationResult>,
) -> JsonValue {
    result
        .map(|result| prop_registration_verification_value(renderer, result))
        .unwrap_or(JsonValue::Null)
}

pub(super) fn by_choice_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByChoiceResult,
) -> JsonValue {
    let proof_type = match result.proof_kind {
        SuccessVerifyByChoiceProofKind::AxiomOfChoice => "by axiom_of_choice proof",
        SuccessVerifyByChoiceProofKind::ZornLemma => "by zorn_lemma proof",
        SuccessVerifyByChoiceProofKind::RegularityAxiom => "by regularity_axiom proof",
    };
    let target = match &result.target {
        SuccessVerifyByChoiceTargetResult::AxiomOfChoice { family } => object(vec![
            string_field("kind", "AxiomOfChoice"),
            string_field("family", family.to_string()),
        ]),
        SuccessVerifyByChoiceTargetResult::ZornLemma {
            set,
            relation,
            upper_bound,
            maximal,
        } => object(vec![
            string_field("kind", "ZornLemma"),
            string_field("set", set.to_string()),
            string_field("relation", relation.to_string()),
            string_field("upper_bound", upper_bound.to_string()),
            string_field("maximal", maximal.to_string()),
        ]),
        SuccessVerifyByChoiceTargetResult::RegularityAxiom { set } => object(vec![
            string_field("kind", "RegularityAxiom"),
            string_field("set", set.to_string()),
        ]),
    };
    object(vec![
        string_field("kind", "SuccessVerifyByChoiceResult"),
        string_field("proof_type", proof_type),
        ("target".to_string(), target),
        (
            "proof_steps".to_string(),
            renderer.stmt_results(&result.proof_steps),
        ),
        (
            "obligations".to_string(),
            array(
                result
                    .obligations
                    .iter()
                    .map(|obligation| {
                        object(vec![
                            string_field(
                                "role",
                                match obligation.role {
                                    SuccessVerifyByChoiceObligationRole::ChoiceFamilyIsSet => {
                                        "family_is_set"
                                    }
                                    SuccessVerifyByChoiceObligationRole::ChoiceMembersNonempty => {
                                        "members_nonempty"
                                    }
                                    SuccessVerifyByChoiceObligationRole::ZornNonempty
                                    | SuccessVerifyByChoiceObligationRole::RegularityNonempty => {
                                        "nonempty"
                                    }
                                    SuccessVerifyByChoiceObligationRole::ZornReflexive => {
                                        "reflexive"
                                    }
                                    SuccessVerifyByChoiceObligationRole::ZornTransitive => {
                                        "transitive"
                                    }
                                    SuccessVerifyByChoiceObligationRole::ZornAntisymmetric => {
                                        "antisymmetric"
                                    }
                                    SuccessVerifyByChoiceObligationRole::ZornChainUpperBound => {
                                        "chain_upper_bound"
                                    }
                                },
                            ),
                            string_field("statement", obligation.fact.to_string()),
                            string_field("fact_id", obligation.fact_id.to_string()),
                            (
                                "check".to_string(),
                                obligation
                                    .check
                                    .as_ref()
                                    .map(|check| renderer.stmt_result(check))
                                    .unwrap_or(JsonValue::Null),
                            ),
                        ])
                    })
                    .collect(),
            ),
        ),
        string_field("trusted_conclusion", result.trusted_conclusion.to_string()),
        string_field(
            "trusted_conclusion_fact_id",
            result.trusted_conclusion_fact_id.to_string(),
        ),
    ])
}

pub(super) fn optional_choice_verification(
    renderer: &mut StmtResultJsonV2,
    result: Option<&SuccessVerifyByChoiceResult>,
) -> JsonValue {
    result
        .map(|result| by_choice_verification_value(renderer, result))
        .unwrap_or(JsonValue::Null)
}

pub(super) fn theorem_application_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyTheoremApplicationResult,
) -> JsonValue {
    let arguments = result
        .arguments
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let direct_conclusions = result
        .direct_conclusions
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    let (
        theorem_source,
        source_fact_id,
        domain_facts,
        requirement_roles,
        argument_verification,
        requirement_checks,
        domain_checks,
        conclusion_well_definedness,
        provenance,
    ) = match &result.source {
        SuccessVerifyTheoremApplicationSourceResult::Litex(source) => (
            "litex",
            source.source_fact_id,
            source
                .domain_facts
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            Vec::new(),
            source.argument_verification.as_deref(),
            &[][..],
            source.domain_checks.as_slice(),
            JsonValue::Null,
            None,
        ),
        SuccessVerifyTheoremApplicationSourceResult::Builtin(source) => (
            "builtin_rule",
            None,
            source
                .requirement_facts
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>(),
            source
                .requirement_roles
                .iter()
                .map(|role| role.as_str().to_string())
                .collect::<Vec<_>>(),
            None,
            source.requirement_checks.as_slice(),
            &[][..],
            source
                .conclusion_well_definedness
                .as_ref()
                .map(|well_definedness| renderer.fact_well_definedness(well_definedness))
                .unwrap_or(JsonValue::Null),
            source.provenance.map(BuiltinTheoremProvenance::as_str),
        ),
    };
    object(vec![
        string_field("kind", "SuccessVerifyByTheoremResult"),
        string_field("theorem", result.theorem.clone()),
        string_field("theorem_source", theorem_source),
        optional_fact_id_field("source_fact_id", source_fact_id),
        string_field("mode", "release_all"),
        ("arguments".to_string(), strings(&arguments)),
        ("domain_facts".to_string(), strings(&domain_facts)),
        ("requirement_roles".to_string(), strings(&requirement_roles)),
        (
            "conclusion_well_definedness".to_string(),
            conclusion_well_definedness,
        ),
        (
            "direct_conclusions".to_string(),
            display_values(&result.direct_conclusions),
        ),
        (
            "stored_then_facts".to_string(),
            strings(&direct_conclusions),
        ),
        ("temporary_then_facts".to_string(), strings(&[])),
        optional_string_field("selected_fact", None),
        (
            "parent_stored_facts".to_string(),
            strings(&direct_conclusions),
        ),
        optional_string_field("provenance", provenance),
        (
            "argument_verification".to_string(),
            argument_verification
                .map(|verification| {
                    args_satisfy_param_def_verification_value(renderer, verification)
                })
                .unwrap_or(JsonValue::Null),
        ),
        (
            "requirement_checks".to_string(),
            renderer.stmt_results(requirement_checks),
        ),
        (
            "domain_checks".to_string(),
            renderer.stmt_results(domain_checks),
        ),
        ("selected_fact_check".to_string(), JsonValue::Null),
    ])
}

pub(super) fn theorem_selection_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByTheoremSelectionResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByTheoremSelectionResult"),
        (
            "temporary_application".to_string(),
            renderer.stmt_result(&result.temporary_application),
        ),
        string_field("selected_fact", result.selected_fact.to_string()),
        (
            "selected_fact_check".to_string(),
            renderer.stmt_result(&result.selected_fact_check),
        ),
    ])
}

pub(super) fn by_definition_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyByDefinitionResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyByDefinitionResult"),
        string_field("prop", result.prop.clone()),
        optional_string_field(
            "definition",
            result
                .definition
                .as_ref()
                .map(ToString::to_string)
                .as_deref(),
        ),
        ("arguments".to_string(), strings(&result.arguments)),
        (
            "definition_clauses".to_string(),
            strings(&result.definition_clauses),
        ),
        string_field("stored_fact", result.stored_fact.clone()),
        (
            "concrete_user_prop".to_string(),
            JsonValue::Bool(result.concrete_user_prop),
        ),
        (
            "target_well_definedness".to_string(),
            result
                .target_well_definedness
                .as_ref()
                .map(|well_definedness| renderer.fact_well_definedness(well_definedness))
                .unwrap_or(JsonValue::Null),
        ),
        (
            "definition_clause_facts".to_string(),
            display_values(&result.definition_clause_facts),
        ),
        (
            "argument_verification".to_string(),
            result
                .argument_verification
                .as_ref()
                .map(|verification| {
                    args_satisfy_param_def_verification_value(renderer, verification)
                })
                .unwrap_or(JsonValue::Null),
        ),
        (
            "clause_checks".to_string(),
            renderer.stmt_results(&result.clause_checks),
        ),
    ])
}

pub(super) fn args_satisfy_param_def_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyArgsSatisfyParamDefResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyArgsSatisfyParamDefResult"),
        ("checks".to_string(), renderer.stmt_results(&result.checks)),
        ("infers".to_string(), infer_result_value(&result.infers)),
    ])
}

pub(super) fn object_choice_verification_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyObjectChoiceResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyObjectChoiceResult"),
        (
            "groups".to_string(),
            array(
                result
                    .groups
                    .iter()
                    .map(|group| {
                        object(vec![
                            (
                                "selected_type_facts".to_string(),
                                display_values(&group.selected_type_facts),
                            ),
                            (
                                "nonempty_check".to_string(),
                                group
                                    .nonempty_check
                                    .as_ref()
                                    .map(|check| renderer.stmt_result(check))
                                    .unwrap_or(JsonValue::Null),
                            ),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

pub(super) fn existential_elimination_value(
    renderer: &mut StmtResultJsonV2,
    result: &SuccessVerifyExistentialEliminationResult,
) -> JsonValue {
    object(vec![
        string_field("kind", "SuccessVerifyExistentialEliminationResult"),
        (
            "source_result".to_string(),
            renderer.stmt_result(&result.source_result),
        ),
        string_field("source_exist_fact", result.source_exist_fact.to_string()),
        (
            "witness_type_facts".to_string(),
            display_values(&result.witness_type_facts),
        ),
        (
            "instantiated_body_facts".to_string(),
            display_values(&result.instantiated_body_facts),
        ),
        (
            "includes_uniqueness".to_string(),
            JsonValue::Bool(result.includes_uniqueness),
        ),
    ])
}

pub(super) fn optional_existential_elimination(
    renderer: &mut StmtResultJsonV2,
    result: Option<&SuccessVerifyExistentialEliminationResult>,
) -> JsonValue {
    result
        .map(|result| existential_elimination_value(renderer, result))
        .unwrap_or(JsonValue::Null)
}

pub(super) fn infer_result_value(result: &SuccessInferResult) -> JsonValue {
    object(vec![
        (
            "stores".to_string(),
            array(
                result
                    .store_fact_outputs
                    .iter()
                    .map(store_fact_output_value)
                    .collect(),
            ),
        ),
        (
            "rule_applications".to_string(),
            array(
                result
                    .rule_applications
                    .iter()
                    .map(infer_rule_application_value)
                    .collect(),
            ),
        ),
    ])
}

pub(super) fn infer_rule_application_value(
    result: &SuccessInferRuleApplicationResult,
) -> JsonValue {
    let mut fields = vec![
        string_field(
            "rule",
            match &result.rule {
                InferRule::NaturalMembershipImpliesNonnegative => {
                    "NaturalMembershipImpliesNonnegative"
                }
                InferRule::PositiveStandardSetMembershipImpliesPositive(_) => {
                    "PositiveStandardSetMembershipImpliesPositive"
                }
                InferRule::NegativeStandardSetMembershipImpliesNegative(_) => {
                    "NegativeStandardSetMembershipImpliesNegative"
                }
                InferRule::NonzeroStandardSetMembershipImpliesNonzero(_) => {
                    "NonzeroStandardSetMembershipImpliesNonzero"
                }
                InferRule::SetBuilderBaseMembershipProjection => {
                    "SetBuilderBaseMembershipProjection"
                }
                InferRule::SetBuilderPredicateProjection { .. } => "SetBuilderPredicateProjection",
                InferRule::DefinedPredicateParameterRequirementProjection(_) => {
                    "DefinedPredicateParameterRequirementProjection"
                }
                InferRule::DefinedPredicateDefinitionClauseProjection(_) => {
                    "DefinedPredicateDefinitionClauseProjection"
                }
                InferRule::EqualityChainClosure(_) => "EqualityChainClosure",
                InferRule::NumericOrderChainClosure(_) => "NumericOrderChainClosure",
                InferRule::ClosedPositivePowerEqualityImpliesEqualSideMembership(_) => {
                    "ClosedPositivePowerEqualityImpliesEqualSideMembership"
                }
                InferRule::PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(_) => {
                    "PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership"
                }
                InferRule::RegisteredTransitivePredicateChainClosure(_) => {
                    "RegisteredTransitivePredicateChainClosure"
                }
                InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(_) => {
                    "TupleEqualityWithKnownTupleImpliesTupleShape"
                }
                InferRule::CartesianMembershipProjection(_) => "CartesianMembershipProjection",
                InferRule::ListSetMembershipImpliesEqualityAlternatives(_) => {
                    "ListSetMembershipImpliesEqualityAlternatives"
                }
                InferRule::FunctionRangeMembershipImpliesCodomainMembership => {
                    "FunctionRangeMembershipImpliesCodomainMembership"
                }
                InferRule::NumericOrderBoundImpliesZeroSign => "NumericOrderBoundImpliesZeroSign",
                InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero => {
                    "MultiplicationByNegativeOneReversesOrderAgainstZero"
                }
                InferRule::StrictOrderComparedToZeroImpliesWeakOrder => {
                    "StrictOrderComparedToZeroImpliesWeakOrder"
                }
                InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_) => {
                    "MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet"
                }
                InferRule::SubsetImpliesElementwiseMembershipForall(_) => {
                    "SubsetImpliesElementwiseMembershipForall"
                }
                InferRule::SupersetImpliesElementwiseMembershipForall(_) => {
                    "SupersetImpliesElementwiseMembershipForall"
                }
                InferRule::ConjunctionImpliesComponent(_) => "ConjunctionImpliesComponent",
            },
        ),
        (
            "premises".to_string(),
            array(
                result
                    .premises
                    .iter()
                    .map(|premise| {
                        object(vec![
                            string_field("statement", premise.fact.to_string()),
                            optional_fact_id_field("fact_id", premise.fact_id),
                        ])
                    })
                    .collect(),
            ),
        ),
        (
            "conclusions".to_string(),
            array(
                result
                    .conclusions
                    .iter()
                    .map(success_store_fact_value)
                    .collect(),
            ),
        ),
    ];
    if let InferRule::SetBuilderPredicateProjection { clause_index } = &result.rule {
        fields.insert(1, number_field("clause_index", *clause_index));
    }
    let source_set = match &result.rule {
        InferRule::PositiveStandardSetMembershipImpliesPositive(rule) => Some(rule.source_set),
        InferRule::NegativeStandardSetMembershipImpliesNegative(rule) => Some(rule.source_set),
        InferRule::NonzeroStandardSetMembershipImpliesNonzero(rule) => Some(rule.source_set),
        _ => None,
    };
    if let Some(source_set) = source_set {
        fields.insert(1, string_field("source_set", source_set.to_string()));
    }
    if let InferRule::DefinedPredicateParameterRequirementProjection(rule) = &result.rule {
        fields.insert(1, string_field("predicate_name", &rule.predicate_name));
        fields.insert(2, number_field("parameter_index", rule.parameter_index));
    }
    if let InferRule::DefinedPredicateDefinitionClauseProjection(rule) = &result.rule {
        fields.insert(1, string_field("predicate_name", &rule.predicate_name));
        fields.insert(2, number_field("clause_index", rule.clause_index));
    }
    if let InferRule::RegisteredTransitivePredicateChainClosure(rule) = &result.rule {
        fields.insert(1, string_field("predicate_name", &rule.predicate_name));
        fields.insert(
            2,
            number_field("start_object_index", rule.start_object_index),
        );
        fields.insert(3, number_field("end_object_index", rule.end_object_index));
    }
    if let InferRule::EqualityChainClosure(rule) = &result.rule {
        fields.insert(
            1,
            number_field("start_object_index", rule.start_object_index),
        );
        fields.insert(2, number_field("end_object_index", rule.end_object_index));
    }
    if let InferRule::NumericOrderChainClosure(rule) = &result.rule {
        fields.insert(
            1,
            number_field("start_object_index", rule.start_object_index),
        );
        fields.insert(2, number_field("end_object_index", rule.end_object_index));
    }
    if let InferRule::ClosedPositivePowerEqualityImpliesEqualSideMembership(rule) = &result.rule {
        fields.insert(
            1,
            (
                "power_is_left_endpoint".to_string(),
                JsonValue::Bool(rule.power_is_left_endpoint),
            ),
        );
    }
    if let InferRule::PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembership(rule) =
        &result.rule
    {
        fields.insert(
            1,
            (
                "power_is_left_endpoint".to_string(),
                JsonValue::Bool(rule.power_is_left_endpoint),
            ),
        );
    }
    if let InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(rule) = &result.rule {
        fields.insert(
            1,
            string_field(
                "known_side",
                match rule.known_side {
                    KnownTupleEqualitySide::Left => "left",
                    KnownTupleEqualitySide::Right => "right",
                },
            ),
        );
        fields.insert(2, number_field("tuple_length", rule.tuple_length));
    }
    if let InferRule::CartesianMembershipProjection(rule) = &result.rule {
        fields.insert(1, number_field("coordinate_count", rule.coordinate_count));
        fields.insert(
            2,
            string_field(
                "projection",
                match rule.projection {
                    CartesianMembershipProjectionKind::TupleShape => "tuple_shape",
                    CartesianMembershipProjectionKind::TupleDimension => "tuple_dimension",
                    CartesianMembershipProjectionKind::Coordinate { .. } => "coordinate",
                },
            ),
        );
        if let CartesianMembershipProjectionKind::Coordinate { index } = rule.projection {
            fields.insert(3, number_field("coordinate_index", index));
        }
    }
    if let InferRule::ListSetMembershipImpliesEqualityAlternatives(rule) = &result.rule {
        fields.insert(1, number_field("element_count", rule.element_count));
    }
    if let InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(rule) =
        &result.rule
    {
        fields.insert(
            1,
            string_field(
                "equality_orientation",
                match rule.equality_orientation {
                    KnownSetEqualityOrientation::SourceSetOnLeft => "source_set_on_left",
                    KnownSetEqualityOrientation::SourceSetOnRight => "source_set_on_right",
                },
            ),
        );
    }
    let binder_symbol_id = match &result.rule {
        InferRule::SubsetImpliesElementwiseMembershipForall(rule) => Some(rule.binder_symbol_id),
        InferRule::SupersetImpliesElementwiseMembershipForall(rule) => Some(rule.binder_symbol_id),
        _ => None,
    };
    if let Some(binder_symbol_id) = binder_symbol_id {
        fields.insert(
            1,
            string_field(
                "binder_symbol_id",
                format!("symbol-{}", binder_symbol_id.value()),
            ),
        );
    }
    if let InferRule::ConjunctionImpliesComponent(rule) = &result.rule {
        fields.insert(1, number_field("component_index", rule.component_index));
        fields.insert(2, number_field("component_count", rule.component_count));
    }
    object(fields)
}

pub(super) fn success_store_fact_value(result: &SuccessStoreFactResult) -> JsonValue {
    object(vec![
        string_field("fact", result.fact.to_string()),
        optional_fact_id_field("fact_id", result.fact_id),
        ("infers".to_string(), infer_result_value(&result.infers)),
    ])
}

pub(super) fn store_fact_output_value(store: &SuccessStoreFactOutput) -> JsonValue {
    object(vec![
        optional_fact_id_field("fact_id", store.fact_id),
        string_field(
            "statement",
            store.itself_and_why_itself_is_stored.0.to_string(),
        ),
        string_field("reason", store.itself_and_why_itself_is_stored.1.clone()),
        (
            "inferred_facts".to_string(),
            array(
                store
                    .inferred_facts
                    .iter()
                    .zip(store.inferred_fact_ids.iter())
                    .map(|(fact, id)| {
                        object(vec![
                            optional_fact_id_field("fact_id", *id),
                            string_field("statement", fact.to_string()),
                        ])
                    })
                    .collect(),
            ),
        ),
    ])
}

pub(super) fn evaluation_value(result: &SuccessEvaluateObjResult) -> JsonValue {
    let step = match &result.step {
        SuccessEvaluateObjStepResult::Literal(literal) => object(vec![
            string_field("kind", "Literal"),
            string_field("literal", literal.literal.to_string()),
        ]),
        SuccessEvaluateObjStepResult::Unary(unary) => object(vec![
            string_field("kind", "Unary"),
            string_field("operator", unary_operator(unary.operator)),
            ("argument".to_string(), evaluation_value(&unary.argument)),
        ]),
        SuccessEvaluateObjStepResult::Binary(binary) => object(vec![
            string_field("kind", "Binary"),
            string_field("operator", binary_operator(binary.operator)),
            ("left".to_string(), evaluation_value(&binary.left)),
            ("right".to_string(), evaluation_value(&binary.right)),
        ]),
        SuccessEvaluateObjStepResult::Shape(shape) => object(vec![
            string_field("kind", "Shape"),
            string_field("operator", shape_operator(shape.operator)),
            (
                "inputs".to_string(),
                array(
                    shape
                        .inputs
                        .iter()
                        .map(|input| string(input.to_string()))
                        .collect(),
                ),
            ),
            (
                "evaluated_children".to_string(),
                array(
                    shape
                        .evaluated_children
                        .iter()
                        .map(evaluation_value)
                        .collect(),
                ),
            ),
        ]),
    };
    object(vec![
        string_field("expression", result.expression.to_string()),
        string_field("value", result.value.to_string()),
        ("step".to_string(), step),
    ])
}

pub(super) fn eval_stmt_execution_result_value(
    result: &SuccessEvalStmtExecutionResult,
) -> JsonValue {
    match result {
        SuccessEvalStmtExecutionResult::SkippedByTrustedExecution => {
            object(vec![string_field("kind", "SkippedByTrustedExecution")])
        }
        SuccessEvalStmtExecutionResult::Evaluated(result) => object(vec![
            string_field("kind", "Evaluated"),
            string_field("source_object", result.source_object.to_string()),
            string_field("evaluated_object", result.evaluated_object.to_string()),
            (
                "recursive_numeric_evaluation".to_string(),
                result
                    .recursive_numeric_evaluation
                    .as_ref()
                    .map(evaluation_value)
                    .unwrap_or(JsonValue::Null),
            ),
        ]),
    }
}

pub(super) fn optional_trace(trace: Option<&StatementExecutionTrace>) -> JsonValue {
    trace
        .map(|trace| {
            object(vec![
                (
                    "verify_well_definedness".to_string(),
                    phase_trace_value(&trace.verify_well_definedness),
                ),
                (
                    "verify_process".to_string(),
                    phase_trace_value(&trace.verify_process),
                ),
                (
                    "affect_environment".to_string(),
                    phase_trace_value(&trace.affect_environment),
                ),
                optional_string_field("verification_status", trace.verification_status.as_deref()),
            ])
        })
        .unwrap_or(JsonValue::Null)
}

pub(super) fn phase_trace_value(trace: &ExecutionPhaseTrace) -> JsonValue {
    object(vec![
        string_field("status", phase_status(trace.status)),
        optional_string_field("message", trace.message.as_deref()),
    ])
}

pub(super) fn equality_transport_value(result: Option<&EqualityTransportEvidence>) -> JsonValue {
    result
        .map(|result| {
            array(
                result
                    .steps
                    .iter()
                    .map(|step| {
                        object(vec![
                            string_field("from", step.from.to_string()),
                            string_field("to", step.to.to_string()),
                            string_field("equality", step.equality.to_string()),
                            string_field("equality_fact_id", fact_id(step.equality_fact_id)),
                        ])
                    })
                    .collect(),
            )
        })
        .unwrap_or(JsonValue::Null)
}

pub(super) fn fact_transformation_rule_value(rule: &FactTransformationRule) -> JsonValue {
    match rule {
        FactTransformationRule::EqualityRewrite(evidence) => object(vec![
            string_field("kind", "EqualityRewrite"),
            (
                "transport".to_string(),
                equality_transport_value(Some(evidence)),
            ),
        ]),
        FactTransformationRule::RationalNormalization => {
            object(vec![string_field("kind", "RationalNormalization")])
        }
        FactTransformationRule::AnonymousFunctionBetaNormalization => object(vec![string_field(
            "kind",
            "AnonymousFunctionBetaNormalization",
        )]),
        FactTransformationRule::TransparentDefinitionReduction(evidence) => object(vec![
            string_field("kind", "TransparentDefinitionReduction"),
            (
                "definitions".to_string(),
                array(
                    evidence
                        .definitions
                        .iter()
                        .map(|definition| {
                            object(vec![
                                string_field("symbol", definition.symbol.display_name()),
                                string_field(
                                    "symbol_id",
                                    definition.symbol.id().value().to_string(),
                                ),
                                string_field(
                                    "definition_object",
                                    definition.definition_object.to_string(),
                                ),
                                string_field(
                                    "defining_equality",
                                    definition.defining_equality.to_string(),
                                ),
                                string_field(
                                    "defining_equality_fact_id",
                                    fact_id(definition.defining_equality_fact_id),
                                ),
                            ])
                        })
                        .collect(),
                ),
            ),
        ]),
    }
}

pub(super) fn rule_evidence_value(kind: &str, rule: &str) -> JsonValue {
    object(vec![string_field("kind", kind), string_field("rule", rule)])
}

pub(super) fn arithmetic_builtin_rule_name(rule: ArithmeticBuiltinRule) -> &'static str {
    match rule {
        ArithmeticBuiltinRule::OrderTransitivity => "OrderTransitivity",
        ArithmeticBuiltinRule::LessEqualFromStrictOrder => "LessEqualFromStrictOrder",
        ArithmeticBuiltinRule::GreaterEqualFromStrictOrder => "GreaterEqualFromStrictOrder",
        ArithmeticBuiltinRule::SubNonnegativeFromLessEqual => "SubNonnegativeFromLessEqual",
        ArithmeticBuiltinRule::SubPositiveFromLess => "SubPositiveFromLess",
        ArithmeticBuiltinRule::AddNonnegative => "AddNonnegative",
        ArithmeticBuiltinRule::AddPositive => "AddPositive",
        ArithmeticBuiltinRule::AddPositiveLeftStrict => "AddPositiveLeftStrict",
        ArithmeticBuiltinRule::AddPositiveRightStrict => "AddPositiveRightStrict",
        ArithmeticBuiltinRule::MulNonnegative => "MulNonnegative",
        ArithmeticBuiltinRule::MulPositive => "MulPositive",
        ArithmeticBuiltinRule::DivNonnegative => "DivNonnegative",
        ArithmeticBuiltinRule::DivPositive => "DivPositive",
        ArithmeticBuiltinRule::AddCommonLeftLessEqual => "AddCommonLeftLessEqual",
        ArithmeticBuiltinRule::SubRightNonnegativeLessEqual => "SubRightNonnegativeLessEqual",
        ArithmeticBuiltinRule::AddRightNonnegativeLessEqual => "AddRightNonnegativeLessEqual",
        ArithmeticBuiltinRule::AddComponentwiseLessEqual => "AddComponentwiseLessEqual",
        ArithmeticBuiltinRule::MulComponentwiseLessEqual => "MulComponentwiseLessEqual",
        ArithmeticBuiltinRule::MulCommonFactorLessEqualNonnegative => {
            "MulCommonFactorLessEqualNonnegative"
        }
        ArithmeticBuiltinRule::MulCommonFactorLessEqualNonpositive => {
            "MulCommonFactorLessEqualNonpositive"
        }
        ArithmeticBuiltinRule::MulCommonFactorLessPositive => "MulCommonFactorLessPositive",
        ArithmeticBuiltinRule::MulCommonFactorLessNegative => "MulCommonFactorLessNegative",
        ArithmeticBuiltinRule::AddCommonLeftLess => "AddCommonLeftLess",
        ArithmeticBuiltinRule::AddComponentwiseLess => "AddComponentwiseLess",
        ArithmeticBuiltinRule::AddComponentwiseLessLessEqual => "AddComponentwiseLessLessEqual",
        ArithmeticBuiltinRule::AddComponentwiseLessEqualLess => "AddComponentwiseLessEqualLess",
        ArithmeticBuiltinRule::SubComponentwiseLessEqualLess => "SubComponentwiseLessEqualLess",
    }
}

pub(super) fn integer_membership_closure_rule_name(
    rule: IntegerMembershipClosureBuiltinRule,
) -> &'static str {
    match rule {
        IntegerMembershipClosureBuiltinRule::Add => "Add",
        IntegerMembershipClosureBuiltinRule::Sub => "Sub",
        IntegerMembershipClosureBuiltinRule::Mul => "Mul",
        IntegerMembershipClosureBuiltinRule::Mod => "Mod",
        IntegerMembershipClosureBuiltinRule::PowNat => "PowNat",
    }
}

pub(super) fn natural_membership_closure_rule_name(
    rule: NaturalMembershipClosureBuiltinRule,
) -> &'static str {
    match rule {
        NaturalMembershipClosureBuiltinRule::Add => "Add",
        NaturalMembershipClosureBuiltinRule::Mul => "Mul",
    }
}

pub(super) fn rational_membership_closure_rule_name(
    rule: RationalMembershipClosureBuiltinRule,
) -> &'static str {
    match rule {
        RationalMembershipClosureBuiltinRule::Add => "Add",
        RationalMembershipClosureBuiltinRule::Sub => "Sub",
        RationalMembershipClosureBuiltinRule::Mul => "Mul",
        RationalMembershipClosureBuiltinRule::Div => "Div",
        RationalMembershipClosureBuiltinRule::Pow => "Pow",
    }
}

pub(super) fn complex_membership_closure_rule_name(
    rule: ComplexArithmeticMembershipClosureBuiltinRule,
) -> &'static str {
    match rule {
        ComplexArithmeticMembershipClosureBuiltinRule::Add => "Add",
        ComplexArithmeticMembershipClosureBuiltinRule::Sub => "Sub",
        ComplexArithmeticMembershipClosureBuiltinRule::Mul => "Mul",
        ComplexArithmeticMembershipClosureBuiltinRule::Div => "Div",
    }
}

pub(super) fn real_membership_closure_rule_name(
    rule: RealArithmeticMembershipClosureBuiltinRule,
) -> &'static str {
    match rule {
        RealArithmeticMembershipClosureBuiltinRule::Add => "Add",
        RealArithmeticMembershipClosureBuiltinRule::Sub => "Sub",
        RealArithmeticMembershipClosureBuiltinRule::Mul => "Mul",
        RealArithmeticMembershipClosureBuiltinRule::Div => "Div",
        RealArithmeticMembershipClosureBuiltinRule::Pow => "Pow",
        RealArithmeticMembershipClosureBuiltinRule::Abs => "Abs",
    }
}

pub(super) fn native_constant_membership_rule_name(
    rule: NativeConstantMembershipBuiltinRule,
) -> &'static str {
    match rule {
        NativeConstantMembershipBuiltinRule::ImaginaryUnitInComplex => "ImaginaryUnitInComplex",
        NativeConstantMembershipBuiltinRule::EulerNumberInReal => "EulerNumberInReal",
        NativeConstantMembershipBuiltinRule::PiInReal => "PiInReal",
        NativeConstantMembershipBuiltinRule::EulerNumberInPositiveReal => {
            "EulerNumberInPositiveReal"
        }
        NativeConstantMembershipBuiltinRule::PiInPositiveReal => "PiInPositiveReal",
        NativeConstantMembershipBuiltinRule::EulerNumberInComplex => "EulerNumberInComplex",
        NativeConstantMembershipBuiltinRule::PiInComplex => "PiInComplex",
    }
}

pub(super) fn set_relation_duality_rule_name(rule: SetRelationDualityBuiltinRule) -> &'static str {
    match rule {
        SetRelationDualityBuiltinRule::SubsetFromSuperset => "SubsetFromSuperset",
        SetRelationDualityBuiltinRule::SupersetFromSubset => "SupersetFromSubset",
        SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset => "NotSubsetFromNotSuperset",
        SetRelationDualityBuiltinRule::NotSupersetFromNotSubset => "NotSupersetFromNotSubset",
    }
}

pub(super) fn set_builtin_rule_name(rule: SetBuiltinRule) -> &'static str {
    match rule {
        SetBuiltinRule::EmptySubset => "EmptySubset",
        SetBuiltinRule::SubsetReflexivity => "SubsetReflexivity",
        SetBuiltinRule::SupersetReflexivity => "SupersetReflexivity",
        SetBuiltinRule::SubsetTransitivity => "SubsetTransitivity",
        SetBuiltinRule::SubsetUnionLeft => "SubsetUnionLeft",
        SetBuiltinRule::SubsetUnionRight => "SubsetUnionRight",
        SetBuiltinRule::UnionCommutative => "UnionCommutative",
        SetBuiltinRule::UnionAssociative => "UnionAssociative",
        SetBuiltinRule::UnionIdempotent => "UnionIdempotent",
        SetBuiltinRule::UnionEmptyLeft => "UnionEmptyLeft",
        SetBuiltinRule::UnionEmptyRight => "UnionEmptyRight",
        SetBuiltinRule::UnionSetMinusDecomposition => "UnionSetMinusDecomposition",
        SetBuiltinRule::UnionEqRightOfSubset => "UnionEqRightOfSubset",
        SetBuiltinRule::UnionFinite => "UnionFinite",
        SetBuiltinRule::UnionNonemptyLeft => "UnionNonemptyLeft",
        SetBuiltinRule::UnionNonemptyRight => "UnionNonemptyRight",
        SetBuiltinRule::UnionSubset => "UnionSubset",
        SetBuiltinRule::IntersectCommutative => "IntersectCommutative",
        SetBuiltinRule::IntersectAssociative => "IntersectAssociative",
        SetBuiltinRule::IntersectIdempotent => "IntersectIdempotent",
        SetBuiltinRule::IntersectEqLeftOfSubset => "IntersectEqLeftOfSubset",
        SetBuiltinRule::IntersectEqRightOfSubset => "IntersectEqRightOfSubset",
        SetBuiltinRule::IntersectFinite => "IntersectFinite",
        SetBuiltinRule::IntersectSubsetLeft => "IntersectSubsetLeft",
        SetBuiltinRule::IntersectSubsetRight => "IntersectSubsetRight",
        SetBuiltinRule::IntersectUnionDistributive => "IntersectUnionDistributive",
        SetBuiltinRule::IntersectSetMinusSelfEmpty => "IntersectSetMinusSelfEmpty",
        SetBuiltinRule::IntersectSetMinusDisjointFromSubset => {
            "IntersectSetMinusDisjointFromSubset"
        }
        SetBuiltinRule::PowerSetFinite => "PowerSetFinite",
        SetBuiltinRule::PowerSetMembershipOfSubset => "PowerSetMembershipOfSubset",
        SetBuiltinRule::PowerSetNonempty => "PowerSetNonempty",
        SetBuiltinRule::SetMinusSelfEmpty => "SetMinusSelfEmpty",
        SetBuiltinRule::SetMinusEmptyRight => "SetMinusEmptyRight",
        SetBuiltinRule::SetMinusEmptyLeft => "SetMinusEmptyLeft",
        SetBuiltinRule::SetMinusFiniteLeft => "SetMinusFiniteLeft",
        SetBuiltinRule::SetMinusInfiniteOfInfiniteFinite => "SetMinusInfiniteOfInfiniteFinite",
        SetBuiltinRule::SetMinusIntersectDeMorgan => "SetMinusIntersectDeMorgan",
        SetBuiltinRule::SetMinusIntersectSelf => "SetMinusIntersectSelf",
        SetBuiltinRule::SetMinusRecoverSubset => "SetMinusRecoverSubset",
        SetBuiltinRule::SetMinusSubsetLeft => "SetMinusSubsetLeft",
        SetBuiltinRule::SetMinusUnionDeMorgan => "SetMinusUnionDeMorgan",
        SetBuiltinRule::SubsetEqSetMinusRecovery => "SubsetEqSetMinusRecovery",
        SetBuiltinRule::UnionMembershipLeft => "UnionMembershipLeft",
        SetBuiltinRule::UnionMembershipRight => "UnionMembershipRight",
        SetBuiltinRule::IntersectMembershipBoth => "IntersectMembershipBoth",
        SetBuiltinRule::IntersectNonMembershipLeft => "IntersectNonMembershipLeft",
        SetBuiltinRule::IntersectNonMembershipRight => "IntersectNonMembershipRight",
        SetBuiltinRule::SetMinusMembership => "SetMinusMembership",
    }
}

pub(super) fn finite_set_builtin_rule_name(rule: FiniteSetBuiltinRule) -> &'static str {
    match rule {
        FiniteSetBuiltinRule::ListSet => "ListSet",
        FiniteSetBuiltinRule::Range => "Range",
        FiniteSetBuiltinRule::ClosedRange => "ClosedRange",
    }
}

pub(super) fn absolute_value_builtin_rule_name(rule: AbsoluteValueBuiltinRule) -> &'static str {
    match rule {
        AbsoluteValueBuiltinRule::Nonnegative => "Nonnegative",
        AbsoluteValueBuiltinRule::SelfLessEqual => "SelfLessEqual",
        AbsoluteValueBuiltinRule::NegationLessEqual => "NegationLessEqual",
        AbsoluteValueBuiltinRule::NegativeAbsoluteLessEqual => "NegativeAbsoluteLessEqual",
        AbsoluteValueBuiltinRule::TriangleAdd => "TriangleAdd",
        AbsoluteValueBuiltinRule::TriangleSub => "TriangleSub",
        AbsoluteValueBuiltinRule::ReverseTriangleAdd => "ReverseTriangleAdd",
        AbsoluteValueBuiltinRule::ReverseTriangleSub => "ReverseTriangleSub",
        AbsoluteValueBuiltinRule::NonnegativeIdentity => "NonnegativeIdentity",
        AbsoluteValueBuiltinRule::NonpositiveNegation => "NonpositiveNegation",
        AbsoluteValueBuiltinRule::Product => "Product",
        AbsoluteValueBuiltinRule::PositiveFromNonzero => "PositiveFromNonzero",
    }
}

pub(super) fn extrema_builtin_rule_name(rule: ExtremaBuiltinRule) -> &'static str {
    match rule {
        ExtremaBuiltinRule::MinLessEqualLeft => "MinLessEqualLeft",
        ExtremaBuiltinRule::MinLessEqualRight => "MinLessEqualRight",
        ExtremaBuiltinRule::LessEqualMaxLeft => "LessEqualMaxLeft",
        ExtremaBuiltinRule::LessEqualMaxRight => "LessEqualMaxRight",
        ExtremaBuiltinRule::MinEqLeftOfLessEqual => "MinEqLeftOfLessEqual",
        ExtremaBuiltinRule::MinEqRightOfLessEqual => "MinEqRightOfLessEqual",
        ExtremaBuiltinRule::MaxEqLeftOfLessEqual => "MaxEqLeftOfLessEqual",
        ExtremaBuiltinRule::MaxEqRightOfLessEqual => "MaxEqRightOfLessEqual",
        ExtremaBuiltinRule::MinCommutative => "MinCommutative",
        ExtremaBuiltinRule::MinAssociative => "MinAssociative",
        ExtremaBuiltinRule::MinIdempotent => "MinIdempotent",
        ExtremaBuiltinRule::MinAbsorbMaxLeft => "MinAbsorbMaxLeft",
        ExtremaBuiltinRule::MaxCommutative => "MaxCommutative",
        ExtremaBuiltinRule::MaxAssociative => "MaxAssociative",
        ExtremaBuiltinRule::MaxIdempotent => "MaxIdempotent",
        ExtremaBuiltinRule::MaxAbsorbMinLeft => "MaxAbsorbMinLeft",
        ExtremaBuiltinRule::MinMonotone => "MinMonotone",
        ExtremaBuiltinRule::MaxMonotone => "MaxMonotone",
    }
}

pub(super) fn aggregate_builtin_rule_name(rule: AggregateBuiltinRule) -> &'static str {
    match rule {
        AggregateBuiltinRule::SumSingle => "SumSingle",
        AggregateBuiltinRule::SumSplitLast => "SumSplitLast",
    }
}

pub(super) fn nonzero_builtin_rule_name(rule: NonzeroBuiltinRule) -> &'static str {
    match rule {
        NonzeroBuiltinRule::Mul => "Mul",
    }
}

pub(super) fn unary_operator(operator: EvaluateUnaryObjOperator) -> &'static str {
    match operator {
        EvaluateUnaryObjOperator::Floor => "Floor",
        EvaluateUnaryObjOperator::Ceil => "Ceil",
        EvaluateUnaryObjOperator::Exp => "Exp",
        EvaluateUnaryObjOperator::Ln => "Ln",
        EvaluateUnaryObjOperator::Sign => "Sign",
        EvaluateUnaryObjOperator::Factorial => "Factorial",
        EvaluateUnaryObjOperator::Abs => "Abs",
    }
}

pub(super) fn binary_operator(operator: EvaluateBinaryObjOperator) -> &'static str {
    match operator {
        EvaluateBinaryObjOperator::Add => "Add",
        EvaluateBinaryObjOperator::Sub => "Sub",
        EvaluateBinaryObjOperator::Mul => "Mul",
        EvaluateBinaryObjOperator::Div => "Div",
        EvaluateBinaryObjOperator::Mod => "Mod",
        EvaluateBinaryObjOperator::Quot => "Quot",
        EvaluateBinaryObjOperator::Gcd => "Gcd",
        EvaluateBinaryObjOperator::Lcm => "Lcm",
        EvaluateBinaryObjOperator::Min => "Min",
        EvaluateBinaryObjOperator::Max => "Max",
        EvaluateBinaryObjOperator::Pow => "Pow",
    }
}

pub(super) fn shape_operator(operator: EvaluateObjShapeOperator) -> &'static str {
    match operator {
        EvaluateObjShapeOperator::CartDim => "CartDim",
        EvaluateObjShapeOperator::TupleDim => "TupleDim",
        EvaluateObjShapeOperator::ListSetSize => "ListSetSize",
        EvaluateObjShapeOperator::ClosedRangeSize => "ClosedRangeSize",
        EvaluateObjShapeOperator::RangeSize => "RangeSize",
        EvaluateObjShapeOperator::CartSize => "CartSize",
        EvaluateObjShapeOperator::FiniteSetMax => "FiniteSetMax",
        EvaluateObjShapeOperator::FiniteSetMin => "FiniteSetMin",
    }
}

pub(super) fn wd_child_role_value(role: WellDefinedObjChildRole) -> JsonValue {
    match role {
        WellDefinedObjChildRole::FunctionPrefix {
            through_layer_index,
        } => object(vec![
            string_field("kind", "FunctionPrefix"),
            number_field("through_layer_index", through_layer_index),
        ]),
        WellDefinedObjChildRole::FunctionHead => object(vec![string_field("kind", "FunctionHead")]),
        WellDefinedObjChildRole::FunctionArgument {
            layer_index,
            argument_index,
        } => object(vec![
            string_field("kind", "FunctionArgument"),
            number_field("layer_index", layer_index),
            number_field("argument_index", argument_index),
        ]),
        WellDefinedObjChildRole::BuiltinArgument { argument_index } => object(vec![
            string_field("kind", "BuiltinArgument"),
            number_field("argument_index", argument_index),
        ]),
        WellDefinedObjChildRole::ConstructorArgument { argument_index } => object(vec![
            string_field("kind", "ConstructorArgument"),
            number_field("argument_index", argument_index),
        ]),
        WellDefinedObjChildRole::BinderParameterCarrier {
            parameter_group_index,
        } => object(vec![
            string_field("kind", "BinderParameterCarrier"),
            number_field("parameter_group_index", parameter_group_index),
        ]),
        WellDefinedObjChildRole::BinderReturnCarrier => {
            object(vec![string_field("kind", "BinderReturnCarrier")])
        }
        WellDefinedObjChildRole::BinderBody => object(vec![string_field("kind", "BinderBody")]),
        WellDefinedObjChildRole::VerificationDependency { dependency_index } => object(vec![
            string_field("kind", "VerificationDependency"),
            number_field("dependency_index", dependency_index),
        ]),
    }
}

pub(super) fn wd_binder_premise_role(role: WellDefinedBinderPremiseRole) -> JsonValue {
    match role {
        WellDefinedBinderPremiseRole::ParameterMembership {
            parameter_group_index,
            parameter_index,
        } => object(vec![
            string_field("kind", "ParameterMembership"),
            number_field("parameter_group_index", parameter_group_index),
            number_field("parameter_index", parameter_index),
        ]),
        WellDefinedBinderPremiseRole::Domain { domain_index } => object(vec![
            string_field("kind", "Domain"),
            number_field("domain_index", domain_index),
        ]),
        WellDefinedBinderPremiseRole::LocalCondition { condition_index } => object(vec![
            string_field("kind", "LocalCondition"),
            number_field("condition_index", condition_index),
        ]),
    }
}

pub(super) fn wd_requirement_role(role: WellDefinednessRequirementRole) -> JsonValue {
    match role {
        WellDefinednessRequirementRole::BuiltinArgumentMembership { argument_index } => {
            object(vec![
                string_field("kind", "BuiltinArgumentMembership"),
                number_field("argument_index", argument_index),
            ])
        }
        WellDefinednessRequirementRole::BuiltinArgumentNonzero { argument_index } => object(vec![
            string_field("kind", "BuiltinArgumentNonzero"),
            number_field("argument_index", argument_index),
        ]),
        WellDefinednessRequirementRole::ConstructorPairwiseDistinct {
            left_index,
            right_index,
        } => object(vec![
            string_field("kind", "ConstructorPairwiseDistinct"),
            number_field("left_index", left_index),
            number_field("right_index", right_index),
        ]),
        WellDefinednessRequirementRole::FunctionArgumentMembership {
            layer_index,
            parameter_index,
        } => object(vec![
            string_field("kind", "FunctionArgumentMembership"),
            number_field("layer_index", layer_index),
            number_field("parameter_index", parameter_index),
        ]),
        WellDefinednessRequirementRole::FunctionDomain {
            layer_index,
            domain_index,
        } => object(vec![
            string_field("kind", "FunctionDomain"),
            number_field("layer_index", layer_index),
            number_field("domain_index", domain_index),
        ]),
        WellDefinednessRequirementRole::AnonymousFunctionBodyMembership => {
            object(vec![string_field(
                "kind",
                "AnonymousFunctionBodyMembership",
            )])
        }
        WellDefinednessRequirementRole::AnonymousFunctionBoundParameterSubset {
            parameter_group_index,
            parameter_index,
        } => object(vec![
            string_field("kind", "AnonymousFunctionBoundParameterSubset"),
            number_field("parameter_group_index", parameter_group_index),
            number_field("parameter_index", parameter_index),
        ]),
    }
}

pub(super) fn phase_status(status: StatementPhaseStatus) -> &'static str {
    match status {
        StatementPhaseStatus::Success => "Success",
        StatementPhaseStatus::Unknown => "Unknown",
        StatementPhaseStatus::Error => "Error",
        StatementPhaseStatus::Skipped => "Skipped",
        StatementPhaseStatus::NotRun => "NotRun",
    }
}

pub(super) fn fact_id(id: FactId) -> String {
    id.to_string()
}

pub(super) fn forall_conclusion_location(location: ForallConclusionLocation) -> JsonValue {
    match location {
        ForallConclusionLocation::DirectThenFact(location) => object(vec![
            string_field("kind", "DirectThenFact"),
            number_field("then_fact_index", location.then_fact_index),
        ]),
        ForallConclusionLocation::AndFactComponent(location) => object(vec![
            string_field("kind", "AndFactComponent"),
            number_field("then_fact_index", location.then_fact_index),
            number_field("component_index", location.component_index),
        ]),
        ForallConclusionLocation::ChainFactComponent(location) => object(vec![
            string_field("kind", "ChainFactComponent"),
            number_field("then_fact_index", location.then_fact_index),
            number_field("component_index", location.component_index),
        ]),
    }
}

pub(super) fn atomic_predicate_domain_check_role(
    role: AtomicPredicateDomainCheckRole,
) -> &'static str {
    match role {
        AtomicPredicateDomainCheckRole::ChoiceFunctionIndexSet => "ChoiceFunctionIndexSet",
        AtomicPredicateDomainCheckRole::ChoiceFunctionFamilySet => "ChoiceFunctionFamilySet",
        AtomicPredicateDomainCheckRole::ChoiceFunctionFamily => "ChoiceFunctionFamily",
        AtomicPredicateDomainCheckRole::ChoiceFunctionMember => "ChoiceFunctionMember",
        AtomicPredicateDomainCheckRole::PrimeNaturalArgument => "PrimeNaturalArgument",
        AtomicPredicateDomainCheckRole::CoprimeNaturalArgument => "CoprimeNaturalArgument",
        AtomicPredicateDomainCheckRole::DivisibilityIntegerArgument => {
            "DivisibilityIntegerArgument"
        }
        AtomicPredicateDomainCheckRole::DivisibilityNonzeroIntegerArgument => {
            "DivisibilityNonzeroIntegerArgument"
        }
        AtomicPredicateDomainCheckRole::OrderedRealCarrierEvidence => "OrderedRealCarrierEvidence",
        AtomicPredicateDomainCheckRole::FunctionPropertySignature => "FunctionPropertySignature",
    }
}

pub(super) fn strings(values: &[String]) -> JsonValue {
    array(values.iter().cloned().map(string).collect())
}

pub(super) fn display_values<T: ToString>(values: &[T]) -> JsonValue {
    array(
        values
            .iter()
            .map(|value| string(value.to_string()))
            .collect(),
    )
}

pub(super) fn string_pairs(values: &[(String, String)]) -> JsonValue {
    array(
        values
            .iter()
            .map(|(left, right)| {
                object(vec![
                    string_field("left", left.clone()),
                    string_field("right", right.clone()),
                ])
            })
            .collect(),
    )
}

pub(super) fn object(fields: Vec<(String, JsonValue)>) -> JsonValue {
    JsonValue::Object(fields)
}

pub(super) fn array(values: Vec<JsonValue>) -> JsonValue {
    JsonValue::Array(values)
}

pub(super) fn string(value: impl Into<String>) -> JsonValue {
    JsonValue::JsonString(value.into())
}

pub(super) fn string_field(name: &str, value: impl Into<String>) -> (String, JsonValue) {
    (name.to_string(), string(value))
}

pub(super) fn number_field(name: &str, value: usize) -> (String, JsonValue) {
    (name.to_string(), JsonValue::Number(value))
}

pub(super) fn optional_string_field(name: &str, value: Option<&str>) -> (String, JsonValue) {
    (
        name.to_string(),
        value.map(string).unwrap_or(JsonValue::Null),
    )
}

pub(super) fn optional_strings(values: Option<&Vec<String>>) -> JsonValue {
    values
        .map(|values| array(values.iter().cloned().map(string).collect()))
        .unwrap_or(JsonValue::Null)
}

pub(super) fn optional_fact_id_field(name: &str, id: Option<FactId>) -> (String, JsonValue) {
    (
        name.to_string(),
        id.map(|id| string(fact_id(id))).unwrap_or(JsonValue::Null),
    )
}

pub(super) fn optional_symbol_id_field(name: &str, id: Option<SymbolId>) -> (String, JsonValue) {
    (
        name.to_string(),
        id.map(|id| string(format!("symbol-{}", id.value())))
            .unwrap_or(JsonValue::Null),
    )
}
