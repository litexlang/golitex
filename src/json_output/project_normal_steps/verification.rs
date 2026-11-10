use super::*;

pub(super) fn verification_steps(
    result: &VerifyFactResult,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainProof;
    match result {
        VerifyFactResult::ForallFact(result) => match result.as_ref() {
            VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) => {
                let local = scoped(scopes, &proof.local_env);
                let mut steps = forall_open(
                    &Fact::ForallFact(proof.fact.clone()),
                    proof.assumed_dom_facts.len(),
                    rt,
                    source,
                );
                steps.extend(
                    proof
                        .proved_then_facts
                        .iter()
                        .map(|proof| proved_then_step(proof, rt, source, &local)),
                );
                steps
            }
            VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToSearchProof {
                fact,
                assumed_dom_facts,
                proved_then_facts,
                failed_then,
                local_env,
                ..
            }) => {
                let local = scoped(scopes, local_env);
                let mut steps = forall_open(
                    &Fact::ForallFact(fact.clone()),
                    assumed_dom_facts.len(),
                    rt,
                    source,
                );
                steps.extend(
                    proved_then_facts
                        .iter()
                        .map(|proof| proved_then_step(proof, rt, source, &local)),
                );
                steps.push(verification_step(
                    "statement",
                    failed_then,
                    rt,
                    source,
                    &local,
                ));
                steps
            }
            VerifyForallFactResult::Failed(VerifyForallFactFailed::FailToVerifyWellDefined(
                reason,
            )) => {
                vec![goal_wd(&Fact::ForallFact(reason.fact().clone()), false, rt)]
            }
            VerifyForallFactResult::Success(VerifyForallFactProof::ByEmptyParameterDomain(
                proof,
            )) => {
                let local = scoped(scopes, &proof.local_env);
                vec![verification_step(
                    "requirement",
                    &proof.empty_carrier_proof,
                    rt,
                    source,
                    &local,
                )]
            }
            VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(_)) => {
                Vec::new()
            }
        },
        VerifyFactResult::Equality(result) => {
            let (wd, searched) = match result.as_ref() {
                VerifyEqualityResult::Success(proof) => {
                    (&proof.well_defined_proof, Some(&proof.searched_proof))
                }
                VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToSearchProof {
                    well_defined_proof,
                    ..
                }) => (well_defined_proof, None),
                VerifyEqualityResult::Failed(VerifyEqualityFailed::FailToVerifyWellDefined(
                    failed,
                )) => {
                    return vec![stage(
                        "well_defined",
                        false,
                        rt,
                        vec![("expression", string(failed.failed_obj.readable_string()))],
                    )];
                }
            };
            let mut steps = Vec::new();
            if let Ok(wd) = wd.as_detailed() {
                append_object_wd(&wd.left, &mut steps, rt, source, scopes);
                if wd.left.obj() != wd.right.obj() {
                    append_object_wd(&wd.right, &mut steps, rt, source, scopes);
                }
            }
            use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::EqualitySearchProofByBuiltinRewrite;
            match searched {
                Some(EqualFactSearchedProof::ByKnownForallFact(proof)) => {
                    steps.extend(application_steps(proof, rt, source, scopes))
                }
                Some(EqualFactSearchedProof::ByKnownForallFactViaSymmetry(proof)) => {
                    steps.extend(application_steps(&proof.known_forall, rt, source, scopes))
                }
                Some(EqualFactSearchedProof::ByBuiltinRewrite(
                    EqualitySearchProofByBuiltinRewrite::ClosedNumericEqualSubstitution(proof),
                )) => {
                    for id in &proof.cited_equal_fact_ids {
                        steps.push(citation_step(rt, scopes, *id));
                    }
                    steps.push(verification_step(
                        "requirement",
                        &proof.residual_equal,
                        rt,
                        source,
                        scopes,
                    ));
                }
                _ => {}
            }
            steps
        }
        VerifyFactResult::AtomicExceptEquality(result) => match result.as_ref() {
            VerifyAtomicExceptEqualityFactResult::Success(proof) => {
                let mut steps = Vec::new();
                if let Ok(wd) = proof.well_defined_proof.as_detailed() {
                    for object in &wd.well_defined_of_each_parameter {
                        append_object_wd(object, &mut steps, rt, source, scopes);
                    }
                    if let PredicateDomainProof::ByRequirements(requirements) = &wd.predicate_domain
                    {
                        use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::PredicateDomainRequirementProof;
                        steps.extend(requirements.iter().map(
                            |requirement| match &requirement.result {
                                PredicateDomainRequirementProof::Verified(proof) => {
                                    verification_step("requirement", proof, rt, source, scopes)
                                }
                                PredicateDomainRequirementProof::CheckedArgument(_) => stage(
                                    "requirement",
                                    true,
                                    rt,
                                    vec![(
                                        "fact",
                                        string(requirement.requirement.readable_string()),
                                    )],
                                ),
                            },
                        ));
                    }
                }
                use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactSearchProofByDefinition;
                match &proof.searched_proof {
                    AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(application) => {
                        steps.extend(application_steps(application, rt, source, scopes));
                    }
                    AtomicExceptEqualityFactSearchedProof::ByDefinition(
                        AtomicExceptEqualityFactSearchProofByDefinition::UserDefinedProp(proof),
                    ) => {
                        steps.extend(check_steps(
                            &proof.proof_of_requirement_facts,
                            rt,
                            source,
                            scopes,
                        ));
                    }
                    _ => {}
                }
                steps
            }
            _ => Vec::new(),
        },
        VerifyFactResult::AndFact(result) => {
            use crate::execute::execute_fact_stmt::verify_and_fact::*;
            match result.as_ref() {
                VerifyAndFactResult::Success(proof) => {
                    if let Some(application) = &proof.known_forall {
                        application_steps(application, rt, source, scopes)
                    } else {
                        check_steps(proof.components.iter(), rt, source, scopes)
                    }
                }
                VerifyAndFactResult::Failed(
                    VerifyAndFactFailed::FailToSearchProof {
                        succeeded_components,
                        failed_component,
                        ..
                    }
                    | VerifyAndFactFailed::FailToVerifyWellDefined {
                        succeeded_components,
                        failed_component,
                        ..
                    },
                ) => check_steps(
                    succeeded_components.iter().chain([failed_component]),
                    rt,
                    source,
                    scopes,
                ),
            }
        }
        VerifyFactResult::ChainFact(result) => {
            use crate::execute::execute_fact_stmt::verify_chain_fact::*;
            match result.as_ref() {
                VerifyChainFactResult::Success(proof) => {
                    if let Some(application) = &proof.known_forall {
                        application_steps(&application.application, rt, source, scopes)
                    } else {
                        check_steps(proof.adjacent.iter(), rt, source, scopes)
                    }
                }
                VerifyChainFactResult::Failed(
                    VerifyChainFactFailed::FailToSearchProof {
                        succeeded_adjacent,
                        failed_adjacent,
                        ..
                    }
                    | VerifyChainFactFailed::FailToVerifyWellDefined {
                        succeeded_adjacent,
                        failed_adjacent,
                        ..
                    },
                ) => check_steps(
                    succeeded_adjacent.iter().chain([failed_adjacent]),
                    rt,
                    source,
                    scopes,
                ),
            }
        }
        VerifyFactResult::ForallFactWithIff(result) => {
            use crate::execute::execute_fact_stmt::verify_forall_fact_with_iff::*;
            match result.as_ref() {
                VerifyForallFactWithIffResult::Success(proof) => check_steps(
                    [&proof.then_implies_iff, &proof.iff_implies_then],
                    rt,
                    source,
                    scopes,
                ),
                VerifyForallFactWithIffResult::Failed(
                    VerifyForallFactWithIffFailed::FailThenImpliesIff {
                        then_implies_iff, ..
                    },
                ) => check_steps([then_implies_iff], rt, source, scopes),
                VerifyForallFactWithIffResult::Failed(
                    VerifyForallFactWithIffFailed::FailIffImpliesThen {
                        then_implies_iff,
                        iff_implies_then,
                        ..
                    },
                ) => check_steps([then_implies_iff, iff_implies_then], rt, source, scopes),
            }
        }
        VerifyFactResult::NotForall(result) => {
            use crate::execute::execute_fact_stmt::verify_not_forall_fact::*;
            match result.as_ref() {
                VerifyNotForallFactResult::Success(proof) => {
                    check_steps([&proof.prove_derived_exist], rt, source, scopes)
                }
                VerifyNotForallFactResult::Failed(
                    VerifyNotForallFactFailed::FailToProveDerivedExist {
                        prove_derived_exist,
                        ..
                    },
                ) => check_steps([prove_derived_exist], rt, source, scopes),
                _ => Vec::new(),
            }
        }
        VerifyFactResult::OrFact(result) => {
            use crate::execute::execute_fact_stmt::verify_or_fact::*;
            let VerifyOrFactResult::Success(proof) = result.as_ref() else {
                return Vec::new();
            };
            match &proof.searched_proof {
                OrFactSearchedProof::BySelectedBranch(proof) => {
                    let local = scoped(scopes, &proof.local_env);
                    let mut steps = proof
                        .assumed_negated_branches
                        .iter()
                        .map(|branch| assumption(&branch.negated_fact, rt, None))
                        .collect::<Vec<_>>();
                    steps.push(verification_step(
                        "requirement",
                        &proof.selected_branch,
                        rt,
                        source,
                        &local,
                    ));
                    steps
                }
                OrFactSearchedProof::ByKnownForallFact(proof) => {
                    application_steps(proof, rt, source, scopes)
                }
                _ => Vec::new(),
            }
        }
        VerifyFactResult::ExistShapedFact(result) => match exist_search(result) {
            Some(ExistShapedFactSearchedProof::ByKnownForallFact(proof)) => {
                application_steps(proof, rt, source, scopes)
            }
            Some(ExistShapedFactSearchedProof::ByBuiltinRule(rule)) => {
                use ExistShapedFactSearchProofByBuiltinRule::*;
                let requirements = match rule {
                    BijectivePreimage(proof) => std::slice::from_ref(&proof.target_membership),
                    RealLineComparisonWitness(proof) => proof.proof_of_requirement_facts.as_slice(),
                    EqualityWitnessFromMembership(proof) => {
                        std::slice::from_ref(&proof.membership_proof)
                    }
                    NonemptySetMemberWitness(proof) => std::slice::from_ref(&proof.nonempty_proof),
                    RationalPositiveDenominator(proof) => {
                        std::slice::from_ref(&proof.rational_membership_proof)
                    }
                    RationalIntegerRatio(proof) => {
                        std::slice::from_ref(&proof.rational_membership_proof)
                    }
                    IntegerMultipleFromZeroRemainder(proof) => {
                        proof.proof_of_requirement_facts.as_slice()
                    }
                    ArchimedeanReciprocal(proof) => {
                        std::slice::from_ref(&proof.positive_bound_proof)
                    }
                    RealDensityMidpoint(proof) => proof.proof_of_requirement_facts.as_slice(),
                };
                check_steps(requirements, rt, source, scopes)
            }
            _ => Vec::new(),
        },
    }
}

pub(super) fn verification_step(
    kind: &str,
    result: &VerifyFactResult,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> JsonValue {
    let fact = verify_goal_fact(result);
    let success = !result.is_failed();
    let mut fields = vec![
        ("kind", string(kind)),
        ("fact", string(fact.readable_string())),
    ];
    if kind == "statement" {
        fields.push((
            "statement_result",
            crate::json_output::helper::statement_result_value(success),
        ));
    } else {
        fields.push((
            "result",
            crate::json_output::helper::run_result_value(success),
        ));
    }
    if let Some(location) = fact_source_line(&fact) {
        fields.push(("line", number(location.line)));
        if let Some(source) = source.filter(|source| source.origin == location.origin) {
            if kind == "statement" {
                if let Some(raw) = source.block(location.line) {
                    fields.push(("source", string(raw)));
                }
            }
        }
    }
    if success {
        fields.push(("proof_method", method(result, rt, scopes)));
    }
    let steps = verification_steps(result, rt, source, scopes);
    if !steps.is_empty() {
        fields.push(("steps", JsonValue::Array(steps)));
    }
    object_for(rt, fields)
}

pub(super) fn method(result: &VerifyFactResult, rt: &Runtime, scopes: &[&ExecEnv]) -> JsonValue {
    match result {
        VerifyFactResult::ForallFact(result) => match result.as_ref() {
            VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(_)) => {
                return described_method(rt, "forall_introduction",
                    "Introduce arbitrary parameters and prove each conclusion under the local assumptions.",
                    "引入任意参数，在局部前提下证明每个结论。");
            }
            VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(proof)) => {
                return cited_method(rt, scopes, "cite_forall", proof.cite_fact_id);
            }
            VerifyForallFactResult::Success(VerifyForallFactProof::ByEmptyParameterDomain(_)) => {
                return object_for(rt, vec![("type", string("empty_parameter_domain"))]);
            }
            _ => {}
        },
        VerifyFactResult::AtomicExceptEquality(result) => {
            if let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_ref() {
                match &proof.searched_proof {
                    AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof) => {
                        return cited_method(rt, scopes, "cite_known", proof.cite_fact_id);
                    }
                    AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(
                        SearchProofByKnownForallFact::Detailed(proof),
                    ) => {
                        return cited_method(rt, scopes, "cite_forall", proof.cite.fact_id);
                    }
                    _ => {}
                }
            }
        }
        VerifyFactResult::Equality(result) => {
            if let VerifyEqualityResult::Success(proof) = result.as_ref() {
                if let EqualFactSearchedProof::ByKnownForallFact(application) =
                    &proof.searched_proof
                {
                    if let SearchProofByKnownForallFact::Detailed(proof) = application.as_ref() {
                        return cited_method(rt, scopes, "cite_forall", proof.cite.fact_id);
                    }
                }
            }
        }
        VerifyFactResult::ExistShapedFact(result) => match exist_search(result) {
            Some(ExistShapedFactSearchedProof::ByKnownExistShapedFact(proof)) => {
                return cited_method(rt, scopes, "cite_known", proof.cite_fact_id);
            }
            Some(ExistShapedFactSearchedProof::ByBuiltinRule(rule)) => {
                let text = rule.rule_name_and_message(rt.launch_command.output_language());
                return crate::json_output::helper::builtin_rule_with_optional_cite(
                    rt, &text, None,
                );
            }
            _ => {}
        },
        VerifyFactResult::ForallFactWithIff(_) => {
            return described_method(
                rt,
                "forall_equivalence",
                "Prove both directions of the equivalence.",
                "分别证明等价的两个方向。",
            )
        }
        VerifyFactResult::NotForall(_) => {
            return described_method(
                rt,
                "counterexample",
                "Establish a counterexample to the universal statement.",
                "证明存在一个反例。",
            )
        }
        VerifyFactResult::AndFact(result) => {
            use crate::execute::execute_fact_stmt::verify_and_fact::VerifyAndFactResult;
            if let VerifyAndFactResult::Success(proof) = result.as_ref() {
                if proof.known_forall.is_none() {
                    return described_method(
                        rt,
                        "conjunction",
                        "Verify each conjunct.",
                        "逐项验证合取命题。",
                    );
                }
            }
        }
        VerifyFactResult::ChainFact(result) => {
            use crate::execute::execute_fact_stmt::verify_chain_fact::VerifyChainFactResult;
            if let VerifyChainFactResult::Success(proof) = result.as_ref() {
                if proof.known_forall.is_none() {
                    return described_method(
                        rt,
                        "chain",
                        "Verify each adjacent relation in the chain.",
                        "逐项验证相邻关系。",
                    );
                }
            }
        }
        VerifyFactResult::OrFact(result) => {
            use crate::execute::execute_fact_stmt::verify_or_fact::*;
            if let VerifyOrFactResult::Success(proof) = result.as_ref() {
                match &proof.searched_proof {
                    OrFactSearchedProof::ByKnownOrFact(proof) => {
                        return cited_method(rt, scopes, "cite_known", proof.cite_fact_id)
                    }
                    OrFactSearchedProof::BySelectedBranch(proof) => {
                        return if proof.assumed_negated_branches.is_empty() {
                            described_method(
                                rt,
                                "selected_branch",
                                "Verify one of the alternatives.",
                                "验证其中一个分支。",
                            )
                        } else {
                            described_method(rt, "selected_branch",
                                "Verify the selected alternative under the negations of the other alternatives.",
                                "在其余分支不成立的条件下，验证所选分支。")
                        };
                    }
                    _ => {}
                }
            }
        }
    }
    build_proof_method(result, rt)
}

fn cited_method(rt: &Runtime, scopes: &[&ExecEnv], kind: &str, id: FactId) -> JsonValue {
    let mut result = described_method(
        rt,
        kind,
        "Apply a previously established fact.",
        "使用已建立的命题。",
    );
    let fact = scoped_fact(rt, scopes, id);
    if let Some(fact) = fact {
        let mut citation = vec![("fact", string(fact.readable_string()))];
        if let Some(position) = fact_source_line(fact) {
            citation.push(("file", string(position.origin.to_string())));
            citation.push(("line", number(position.line)));
        }
        field(&mut result, rt, "cite", object_for(rt, citation));
    }
    result
}

fn described_method(rt: &Runtime, kind: &str, english: &str, chinese: &str) -> JsonValue {
    object_for(
        rt,
        vec![
            ("type", string(kind)),
            (
                "message",
                string(
                    if rt.launch_command.output_language() == OutputLanguage::Chinese {
                        chinese
                    } else {
                        english
                    },
                ),
            ),
        ],
    )
}

fn application_steps(
    application: &SearchProofByKnownForallFact,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    let SearchProofByKnownForallFact::Detailed(proof) = application else {
        return Vec::new();
    };
    let Ok(requirements) = proof.instantiation_requirements.as_detailed() else {
        return Vec::new();
    };
    check_steps(
        requirements
            .param_type_requirements
            .iter()
            .map(|requirement| &requirement.proof)
            .chain(&requirements.proof_of_dom_facts),
        rt,
        source,
        scopes,
    )
}

fn append_object_wd(
    proof: &ObjWellDefinedProof,
    steps: &mut Vec<JsonValue>,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) {
    let Ok(DetailedObjWellDefinedProof::ByDef { obj, proof }) = proof.as_detailed() else {
        return;
    };
    let mut local = Vec::new();
    let (children, requirements) = match proof {
        ObjWellDefinedProofByDef::FnObj(proof) => {
            if let Some(scope) = &proof.argument_scope {
                local = scoped(scopes, &scope.local_env);
            }
            (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            )
        }
        ObjWellDefinedProofByDef::ArithmeticOperator(arithmetic) => match arithmetic {
            ArithmeticOperatorObjWellDefinedProofByDef::Div(proof) => (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            ArithmeticOperatorObjWellDefinedProofByDef::Add(proof) => (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            ArithmeticOperatorObjWellDefinedProofByDef::Sub(proof) => (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            ArithmeticOperatorObjWellDefinedProofByDef::Mul(proof) => (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            ArithmeticOperatorObjWellDefinedProofByDef::Neg(proof) => (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            ArithmeticOperatorObjWellDefinedProofByDef::Pow(proof) => (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            _ => return,
        },
        ObjWellDefinedProofByDef::ExpLogOperator(operator) => match operator {
            ExpLogOperatorObjWellDefinedProofByDef::Exp(proof) => (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            ExpLogOperatorObjWellDefinedProofByDef::Ln(proof) => (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            ExpLogOperatorObjWellDefinedProofByDef::Log(proof) => (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
            ExpLogOperatorObjWellDefinedProofByDef::Sqrt(proof) => (
                &proof.child_obj_well_defined,
                &proof.requirement_fact_verified,
            ),
        },
        _ => return,
    };
    let scopes = if local.is_empty() { scopes } else { &local };
    let mut child_steps = Vec::new();
    for child in children {
        append_object_wd(child, &mut child_steps, rt, source, scopes);
    }
    child_steps.extend(
        requirements
            .iter()
            .map(|proof| verification_step("requirement", proof, rt, source, scopes)),
    );
    if !child_steps.is_empty() {
        steps.push(stage(
            "well_defined",
            true,
            rt,
            vec![
                ("expression", string(obj.readable_string())),
                ("steps", JsonValue::Array(child_steps)),
            ],
        ));
    }
}

fn check_steps<'a>(
    results: impl IntoIterator<Item = &'a VerifyFactResult>,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    results
        .into_iter()
        .map(|proof| verification_step("requirement", proof, rt, source, scopes))
        .collect()
}

fn citation_step(rt: &Runtime, scopes: &[&ExecEnv], id: FactId) -> JsonValue {
    object_for(
        rt,
        vec![
            ("kind", string("cite")),
            ("proof_method", cited_method(rt, scopes, "cite_known", id)),
        ],
    )
}

fn exist_search(result: &VerifyExistShapedFactResult) -> Option<&ExistShapedFactSearchedProof> {
    match result {
        VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(proof)) => {
            Some(&proof.searched_proof)
        }
        VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(
            proof,
        )) => Some(&proof.searched_proof),
        VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Success(proof)) => {
            Some(&proof.searched_proof)
        }
        _ => None,
    }
}

fn scoped_fact<'a>(rt: &'a Runtime, scopes: &[&'a ExecEnv], id: FactId) -> Option<&'a Fact> {
    scopes
        .iter()
        .rev()
        .find_map(|env| env.facts.facts_by_id.get(&id))
        .or_else(|| rt.fact_by_id_in_stack(id))
}

fn proved_then_step(
    proof: &ProveAndStoreThenFactResult,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> JsonValue {
    let mut step = verification_step("statement", &proof.verify_result, rt, source, scopes);
    let store = &proof.store_and_infer;
    let stored = store.store.stored_fact_ids();
    let inferences = store
        .stored_fact_ids()
        .into_iter()
        .filter(|id| !stored.contains(id))
        .filter_map(|id| scoped_fact(rt, scopes, id).map(Fact::readable_string))
        .collect::<Vec<_>>();
    if !inferences.is_empty() {
        field(&mut step, rt, "infers", array_of_strings(inferences));
    }
    step
}
