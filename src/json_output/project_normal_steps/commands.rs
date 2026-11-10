use super::*;

pub(super) fn by_steps(
    result: &ExecByStmtResult,
    rt: &Runtime,
    source: Option<&RunSource>,
    line: Option<usize>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    match result {
        ExecByStmtResult::Cases(ExecByCasesStmtResult::Success(proof)) => {
            let mut steps = vec![verification_step(
                "coverage",
                &proof.coverage,
                rt,
                source,
                scopes,
            )];
            steps.extend(
                proof
                    .branches
                    .iter()
                    .map(|branch| case_steps(branch, rt, source, scopes)),
            );
            steps.push(publish(rt, None, &proof.stored.iter().collect::<Vec<_>>()));
            steps
        }
        ExecByStmtResult::Cases(ExecByCasesStmtResult::Failed(failure)) => match failure {
            ExecByCasesStmtFailed::Coverage(proof) => {
                vec![verification_step("coverage", proof, rt, source, scopes)]
            }
            ExecByCasesStmtFailed::ThenFactWd { result, .. } => rejected_wd(result, rt),
            ExecByCasesStmtFailed::Branch {
                coverage,
                branches,
                failed,
                ..
            } => {
                let mut steps = vec![verification_step("coverage", coverage, rt, source, scopes)];
                steps.extend(
                    branches
                        .iter()
                        .map(|branch| case_steps(branch, rt, source, scopes)),
                );
                steps.push(failed_case_steps(failed, rt, source, scopes));
                steps
            }
            _ => Vec::new(),
        },
        ExecByStmtResult::Contra(ExecByContraStmtResult::Success(proof)) => {
            let local = scoped(scopes, &proof.local_env);
            let mut steps = vec![
                goal_wd(&proof.goal, true, rt),
                assumption(&proof.reverse_assumption, rt, None),
            ];
            let lines = proof_source_lines(source, line);
            steps.extend(body_steps(
                &proof.proof_steps,
                &[],
                source,
                &lines,
                rt,
                &local,
            ));
            steps.push(contradiction_step(&proof.closing, rt, source, &local));
            steps.push(publish(rt, None, &[&proof.stored]));
            steps
        }
        ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
            ExecByContraStmtFailed::Local(failure),
        )) => {
            let local = scoped(scopes, &failure.local_env);
            let mut steps = vec![goal_wd(&failure.statement.to_prove, true, rt)];
            match &failure.failure {
                ExecByContraEnteredFailed::AssumptionWd(failed) => {
                    steps.extend(rejected_wd(failed, rt))
                }
                ExecByContraEnteredFailed::ProofBody {
                    failure: failed, ..
                } => {
                    steps.push(assumption(&failure.reverse_assumption, rt, None));
                    steps.extend(failed_body_steps(
                        failed,
                        &failure.statement.proof,
                        source,
                        &[],
                        rt,
                        &local,
                    ));
                }
                ExecByContraEnteredFailed::Closing {
                    proof_steps,
                    failure: failed,
                    ..
                } => {
                    steps.push(assumption(&failure.reverse_assumption, rt, None));
                    steps.extend(body_steps(
                        proof_steps,
                        &failure.statement.proof,
                        source,
                        &[],
                        rt,
                        &local,
                    ));
                    steps.push(failed_contradiction_step(failed, rt, source, &local));
                }
            }
            steps
        }
        ExecByStmtResult::Thm(ExecByThmStmtResult::Success(proof)) => {
            let local = scoped(scopes, &proof.local_env);
            let mut steps = invocation_steps(
                &proof.call,
                &proof.callee,
                &proof.type_proofs,
                &proof.dom_proofs,
                rt,
                source,
                &local,
            );
            steps.push(verification_step(
                "select_conclusion",
                &proof.selected_proof,
                rt,
                source,
                &local,
            ));
            steps.push(publish(rt, None, &[&proof.stored]));
            steps
        }
        ExecByStmtResult::Def(ExecByDefStmtResult::Success(proof)) => {
            let local = scoped(scopes, &proof.local_env);
            vec![
                goal_wd(&verify_goal_fact(&proof.proof), true, rt),
                verification_step("verify_conclusion", &proof.proof, rt, source, &local),
                publish(rt, None, &[&proof.stored]),
            ]
        }
        ExecByStmtResult::Extension(ExecByExtensionStmtResult::Success(proof)) => {
            let local = scoped(scopes, &proof.local_env);
            let lines = proof_source_lines(source, line);
            let mut steps = body_steps(&proof.proof_steps, &[], source, &lines, rt, &local);
            steps.push(verification_step(
                "verify_conclusion",
                &proof.left_to_right,
                rt,
                source,
                &local,
            ));
            steps.push(verification_step(
                "verify_conclusion",
                &proof.right_to_left,
                rt,
                source,
                &local,
            ));
            steps.push(publish(rt, None, &[&proof.stored]));
            steps
        }
        ExecByStmtResult::FnExtension(ExecByFnExtensionStmtResult::Success(proof)) => {
            let local = scoped(scopes, &proof.local_env);
            let lines = proof_source_lines(source, line);
            let mut steps = body_steps(&proof.proof_steps, &[], source, &lines, rt, &local);
            steps.push(verification_step(
                "verify_conclusion",
                &proof.pointwise_proof,
                rt,
                source,
                &local,
            ));
            steps.push(publish(rt, None, &[&proof.stored]));
            steps
        }
        ExecByStmtResult::Induc(ExecByInducStmtResult::Success(proof)) => induction_steps(
            &proof.from_in_z,
            &proof.body,
            &proof.stored,
            rt,
            source,
            line,
            scopes,
        ),
        ExecByStmtResult::StrongInduc(ExecByStrongInducStmtResult::Success(proof)) => {
            induction_steps(
                &proof.from_in_z,
                &proof.body,
                &proof.stored,
                rt,
                source,
                line,
                scopes,
            )
        }
        ExecByStmtResult::EnumerateFiniteSet(ExecByEnumerateFiniteSetStmtResult::Success(
            proof,
        )) => enumeration_steps(&proof.assignments, &proof.stored, rt, source, line, scopes),
        ExecByStmtResult::For(ExecByForStmtResult::Success(proof)) => {
            enumeration_steps(&proof.assignments, &proof.stored, rt, source, line, scopes)
        }
        _ => Vec::new(),
    }
}

pub(super) fn invocation_steps(
    call: &crate::ast::stmt::TheoremCall,
    callee: &ResolvedTheoremCallee,
    types: &[VerifyFactResult],
    premises: &[VerifyFactResult],
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    let mut fields = vec![("theorem", string(call.name.display_string()))];
    let location = match callee {
        ResolvedTheoremCallee::UserTheorem(theorem) => Some(&theorem.line_file),
        ResolvedTheoremCallee::UserAxiom(axiom) => Some(&axiom.line_file),
        ResolvedTheoremCallee::Builtin => None,
    };
    if let Some(location) = location {
        fields.push((
            "cite",
            object_for(
                rt,
                vec![
                    ("file", string(location.origin.to_string())),
                    ("line", number(location.line)),
                ],
            ),
        ));
    }
    let mut steps = vec![stage("resolve_theorem", true, rt, fields)];
    steps.extend(
        types
            .iter()
            .chain(premises)
            .map(|result| verification_step("requirement", result, rt, source, scopes)),
    );
    steps
}

fn case_steps(
    branch: &ByCasesBranchSuccess,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> JsonValue {
    let local = scoped(scopes, &branch.local_env);
    let fact = case_fact(&branch.assumption);
    let line = fact_source_line(&fact).map(|location| location.line);
    let lines = proof_source_lines(source, line);
    let mut steps = vec![assumption(&fact, rt, source)];
    steps.extend(body_steps(
        &branch.proof_steps,
        &[],
        source,
        &lines,
        rt,
        &local,
    ));
    match &branch.closing {
        ByCasesBranchClosingSuccess::ThenFacts { proved_then_facts } => {
            steps.extend(proved_then_facts.iter().map(|proof| {
                verification_step(
                    "verify_conclusion",
                    &proof.verify_result,
                    rt,
                    source,
                    &local,
                )
            }));
        }
        ByCasesBranchClosingSuccess::Impossible(proof) => {
            steps.push(contradiction_step(proof, rt, source, &local))
        }
    }
    stage(
        "branch",
        true,
        rt,
        vec![
            ("fact", string(fact.readable_string())),
            ("steps", JsonValue::Array(steps)),
        ],
    )
}

fn failed_case_steps(
    branch: &ByCasesBranchFailed,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> JsonValue {
    let ByCasesBranchFailed::AfterAssumption(branch) = branch else {
        return stage("branch", false, rt, Vec::new());
    };
    let local = scoped(scopes, &branch.local_env);
    let fact = case_fact(&branch.assumption);
    let lines = proof_source_lines(
        source,
        fact_source_line(&fact).map(|location| location.line),
    );
    let mut steps = vec![assumption(&fact, rt, source)];
    match &branch.failure {
        ByCasesEnteredBranchFailed::ProofBody(failed) => {
            steps.extend(failed_body_steps(failed, &[], source, &lines, rt, &local));
        }
        ByCasesEnteredBranchFailed::ClosingThen {
            proof_steps,
            proved_then_facts,
            result,
            ..
        } => {
            steps.extend(body_steps(proof_steps, &[], source, &lines, rt, &local));
            steps.extend(proved_then_facts.iter().map(|proof| {
                verification_step(
                    "verify_conclusion",
                    &proof.verify_result,
                    rt,
                    source,
                    &local,
                )
            }));
            steps.push(verification_step(
                "verify_conclusion",
                result,
                rt,
                source,
                &local,
            ));
        }
        ByCasesEnteredBranchFailed::ClosingImpossible {
            proof_steps,
            failed,
        } => {
            steps.extend(body_steps(proof_steps, &[], source, &lines, rt, &local));
            steps.push(failed_contradiction_step(failed, rt, source, &local));
        }
    }
    stage(
        "branch",
        false,
        rt,
        vec![
            ("fact", string(fact.readable_string())),
            ("steps", JsonValue::Array(steps)),
        ],
    )
}

fn case_fact(fact: &crate::ast::fact::AndChainAtomicFact) -> Fact {
    use crate::ast::fact::AndChainAtomicFact;
    match fact {
        AndChainAtomicFact::AtomicFact(fact) => Fact::AtomicFact(fact.clone()),
        AndChainAtomicFact::AndFact(fact) => Fact::AndFact(fact.clone()),
        AndChainAtomicFact::ChainFact(fact) => Fact::ChainFact(fact.clone()),
    }
}

fn contradiction_step(
    proof: &ByContradictionClosingSuccess,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> JsonValue {
    stage(
        "contradiction",
        true,
        rt,
        vec![(
            "steps",
            JsonValue::Array(vec![
                verification_step("requirement", &proof.impossible, rt, source, scopes),
                verification_step("requirement", &proof.negated_impossible, rt, source, scopes),
            ]),
        )],
    )
}

fn failed_contradiction_step(
    failed: &ByContradictionClosingFailed,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> JsonValue {
    let mut steps = Vec::new();
    if let ByContradictionClosingFailed::Impossible(result)
    | ByContradictionClosingFailed::NegatedImpossible(result) = failed
    {
        steps.push(verification_step("requirement", result, rt, source, scopes));
    }
    stage(
        "contradiction",
        false,
        rt,
        vec![("steps", JsonValue::Array(steps))],
    )
}

fn proof_source_lines(source: Option<&RunSource>, line: Option<usize>) -> Vec<usize> {
    children(source, line)
        .iter()
        .copied()
        .filter(|line| {
            source
                .and_then(|source| source.line(*line))
                .is_some_and(|text| {
                    let text = text.trim_start();
                    !text.starts_with('?') && text.split_whitespace().next() != Some("impossible")
                })
        })
        .collect()
}

fn induction_steps(
    start: &VerifyFactResult,
    body: &ByInducBodySuccess,
    stored: &StoreFactAndInferResult,
    rt: &Runtime,
    source: Option<&RunSource>,
    line: Option<usize>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    let (base, step, structured) = match body {
        ByInducBodySuccess::Unstructured { base, step } => (base, step, false),
        ByInducBodySuccess::Structured { base, step } => (base, step, true),
    };
    let mut result = vec![verification_step("requirement", start, rt, source, scopes)];
    for (name, case) in [("base", base), ("step", step)] {
        let line = if structured {
            children(source, line).iter().copied().find(|line| {
                source
                    .and_then(|source| source.line(*line))
                    .is_some_and(|text| text.trim_start().starts_with(name))
            })
        } else {
            line
        };
        let local = scoped(scopes, &case.local_env);
        let mut steps = stored_assumptions(&case.assumptions, rt);
        let lines = proof_source_lines(source, line);
        steps.extend(body_steps(
            &case.proof_steps,
            &[],
            source,
            &lines,
            rt,
            &local,
        ));
        steps.extend(
            case.goals_verified
                .iter()
                .map(|result| verification_step("verify_conclusion", result, rt, source, &local)),
        );
        result.push(stage(
            "branch",
            true,
            rt,
            vec![("branch", string(name)), ("steps", JsonValue::Array(steps))],
        ));
    }
    result.push(publish(rt, None, &[stored]));
    result
}

fn enumeration_steps(
    assignments: &[EnumerateAssignmentSuccess],
    stored: &StoreFactAndInferResult,
    rt: &Runtime,
    source: Option<&RunSource>,
    line: Option<usize>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    let mut result = Vec::new();
    let lines = proof_source_lines(source, line);
    for (index, assignment) in assignments.iter().enumerate() {
        let local = scoped(scopes, &assignment.local_env);
        let mut steps = stored_assumptions(&assignment.binding_assumptions, rt);
        let result_kind = match &assignment.outcome {
            EnumerateAssignmentOutcome::Skipped {
                premise_assumptions,
                negated_premise,
                ..
            } => {
                steps.extend(stored_assumptions(premise_assumptions, rt));
                steps.push(verification_step(
                    "premise_excluded",
                    negated_premise,
                    rt,
                    source,
                    &local,
                ));
                "excluded"
            }
            EnumerateAssignmentOutcome::Proved {
                premise_assumptions,
                proof_steps,
                then_proofs,
            } => {
                steps.extend(stored_assumptions(premise_assumptions, rt));
                steps.extend(body_steps(proof_steps, &[], source, &lines, rt, &local));
                steps.extend(then_proofs.iter().map(|proof| {
                    verification_step(
                        "verify_conclusion",
                        &proof.verify_result,
                        rt,
                        source,
                        &local,
                    )
                }));
                "success"
            }
        };
        result.push(object_for(
            rt,
            vec![
                ("kind", string("assignment")),
                ("index", number(index)),
                ("result", string(result_kind)),
                ("steps", JsonValue::Array(steps)),
            ],
        ));
    }
    result.push(publish(rt, None, &[stored]));
    result
}

fn stored_assumptions(assumptions: &[AssumeDomFactResult], rt: &Runtime) -> Vec<JsonValue> {
    assumptions
        .iter()
        .flat_map(|assumption| store_fact_texts(&assumption.store_and_infer.store))
        .map(|fact| object_for(rt, vec![("kind", string("assume")), ("fact", string(fact))]))
        .collect()
}
