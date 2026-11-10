use super::*;

pub(super) fn claim_steps(
    result: &ExecClaimStmtResult,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    match result {
        ExecClaimStmtResult::Success(proof) => {
            let mut steps = claim_body(
                &proof.statement,
                &proof.body,
                &proof.local_env,
                rt,
                source,
                scopes,
            );
            steps.push(publish(rt, None, &[&proof.stored]));
            steps
        }
        ExecClaimStmtResult::Failed(ExecClaimStmtFailed::Local(failure)) => {
            let local = scoped(scopes, &failure.local_env);
            let goal = &failure.statement.fact;
            let proof = &failure.statement.proof;
            let mut steps = vec![goal_wd(goal, true, rt)];
            match &failure.body {
                ExecClaimBodyFailed::NonForall(ExecClaimNonForallFailed::ProofBody(failed)) => {
                    steps.extend(failed_body_steps(failed, proof, source, &[], rt, &local));
                }
                ExecClaimBodyFailed::NonForall(ExecClaimNonForallFailed::Conclusion {
                    proof_steps,
                    result,
                }) => {
                    steps.extend(body_steps(proof_steps, proof, source, &[], rt, &local));
                    steps.push(verification_step(
                        "verify_conclusion",
                        result,
                        rt,
                        source,
                        &local,
                    ));
                }
                ExecClaimBodyFailed::Forall(ExecClaimForallFailed::Entered {
                    assumed_dom_facts,
                    failure,
                    ..
                }) => {
                    steps.extend(forall_open(goal, assumed_dom_facts.len(), rt, source));
                    match failure {
                        ExecClaimForallEnteredFailed::ProofBody(failed) => {
                            steps.extend(failed_body_steps(failed, proof, source, &[], rt, &local))
                        }
                        ExecClaimForallEnteredFailed::Conclusion {
                            proof_steps,
                            conclusion_proofs,
                            result,
                            ..
                        } => {
                            steps.extend(body_steps(proof_steps, proof, source, &[], rt, &local));
                            steps.extend(conclusion_proofs.iter().map(|proof| {
                                verification_step("verify_conclusion", proof, rt, source, &local)
                            }));
                            steps.push(verification_step(
                                "verify_conclusion",
                                result,
                                rt,
                                source,
                                &local,
                            ));
                        }
                        ExecClaimForallEnteredFailed::PremiseWd { result, .. } => {
                            steps.extend(rejected_wd(result, rt))
                        }
                    }
                }
                ExecClaimBodyFailed::Forall(ExecClaimForallFailed::Introduce(_)) => {
                    steps.push(stage("introduce_parameter", false, rt, Vec::new()));
                }
            }
            steps
        }
        ExecClaimStmtResult::Failed(ExecClaimStmtFailed::GoalWd(result)) => rejected_wd(result, rt),
        ExecClaimStmtResult::Failed(ExecClaimStmtFailed::Store {
            statement,
            body,
            local_env,
            ..
        }) => {
            let mut steps = claim_body(statement, body, local_env, rt, source, scopes);
            steps.push(stage("publish", false, rt, Vec::new()));
            steps
        }
        ExecClaimStmtResult::Failed(ExecClaimStmtFailed::GoalUnsupported(_)) => Vec::new(),
    }
}

fn claim_body(
    statement: &crate::ast::stmt::ClaimStmt,
    proof: &ExecClaimBodyProof,
    env: &ExecEnv,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    let local = scoped(scopes, env);
    let mut steps = vec![goal_wd(&statement.fact, true, rt)];
    if let ExecClaimBodyProof::Forall(body) = proof {
        steps.extend(forall_open(
            &statement.fact,
            body.assumed_dom_facts.len(),
            rt,
            source,
        ));
    }
    steps.extend(body_steps(
        proof.proof_steps(),
        &statement.proof,
        source,
        &[],
        rt,
        &local,
    ));
    steps.extend(
        proof
            .conclusion_proofs()
            .iter()
            .map(|proof| verification_step("verify_conclusion", proof, rt, source, &local)),
    );
    steps
}

pub(super) fn theorem_steps(
    result: &ExecDefThmStmtResult,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    match result {
        ExecDefThmStmtResult::Success(proof) => {
            let mut steps = theorem_body(
                &proof.statement,
                &proof.body,
                &proof.local_env,
                rt,
                source,
                scopes,
            );
            steps.push(publish(
                rt,
                Some(proof.statement.name.to_string()),
                &[&proof.stored],
            ));
            steps
        }
        ExecDefThmStmtResult::Failed(ExecDefThmStmtFailed::Local(failure)) => {
            let local = scoped(scopes, &failure.local_env);
            let goal = &failure.statement.fact;
            let proof = &failure.statement.prove_process;
            let mut steps = vec![goal_wd(goal, true, rt)];
            match &failure.body {
                ExecDefThmBodyFailed::NonForall(ExecDefThmNonForallFailed::ProofBody(failed)) => {
                    steps.extend(failed_body_steps(failed, proof, source, &[], rt, &local));
                }
                ExecDefThmBodyFailed::NonForall(ExecDefThmNonForallFailed::Conclusion {
                    proof_steps,
                    result,
                }) => {
                    steps.extend(body_steps(proof_steps, proof, source, &[], rt, &local));
                    steps.push(verification_step(
                        "verify_conclusion",
                        result,
                        rt,
                        source,
                        &local,
                    ));
                }
                ExecDefThmBodyFailed::Forall(ExecDefThmForallFailed::Entered {
                    assumed_dom_facts,
                    failure,
                    ..
                }) => {
                    steps.extend(forall_open(goal, assumed_dom_facts.len(), rt, source));
                    match failure {
                        ExecDefThmForallEnteredFailed::ProofBody(failed) => {
                            steps.extend(failed_body_steps(failed, proof, source, &[], rt, &local))
                        }
                        ExecDefThmForallEnteredFailed::Conclusion {
                            proof_steps,
                            conclusion_proofs,
                            result,
                            ..
                        } => {
                            steps.extend(body_steps(proof_steps, proof, source, &[], rt, &local));
                            steps.extend(conclusion_proofs.iter().map(|proof| {
                                verification_step("verify_conclusion", proof, rt, source, &local)
                            }));
                            steps.push(verification_step(
                                "verify_conclusion",
                                result,
                                rt,
                                source,
                                &local,
                            ));
                        }
                        ExecDefThmForallEnteredFailed::PremiseWd { result, .. } => {
                            steps.extend(rejected_wd(result, rt))
                        }
                    }
                }
                ExecDefThmBodyFailed::Forall(ExecDefThmForallFailed::Introduce(_)) => {
                    steps.push(stage("introduce_parameter", false, rt, Vec::new()));
                }
            }
            steps
        }
        ExecDefThmStmtResult::Failed(ExecDefThmStmtFailed::GoalWd(result)) => {
            rejected_wd(result, rt)
        }
        ExecDefThmStmtResult::Failed(ExecDefThmStmtFailed::Store {
            statement,
            body,
            local_env,
            ..
        }) => {
            let mut steps = theorem_body(statement, body, local_env, rt, source, scopes);
            steps.push(stage("publish", false, rt, Vec::new()));
            steps
        }
        ExecDefThmStmtResult::Failed(
            ExecDefThmStmtFailed::NameClash(_) | ExecDefThmStmtFailed::GoalUnsupported(_),
        ) => Vec::new(),
    }
}

fn theorem_body(
    statement: &crate::ast::stmt::DefThmStmt,
    proof: &ExecDefThmBodyProof,
    env: &ExecEnv,
    rt: &Runtime,
    source: Option<&RunSource>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    let local = scoped(scopes, env);
    let mut steps = vec![goal_wd(&statement.fact, true, rt)];
    let (body, conclusions) = match proof {
        ExecDefThmBodyProof::NonForall(body) => (
            body.proof_steps.as_slice(),
            std::slice::from_ref(&body.conclusion_proof),
        ),
        ExecDefThmBodyProof::Forall(body) => {
            steps.extend(forall_open(
                &statement.fact,
                body.assumed_dom_facts.len(),
                rt,
                source,
            ));
            (
                body.proof_steps.as_slice(),
                body.conclusion_proofs.as_slice(),
            )
        }
    };
    steps.extend(body_steps(
        body,
        &statement.prove_process,
        source,
        &[],
        rt,
        &local,
    ));
    steps.extend(
        conclusions
            .iter()
            .map(|proof| verification_step("verify_conclusion", proof, rt, source, &local)),
    );
    steps
}

pub(super) fn witness_steps(
    result: &ExecWitnessStmtResult,
    rt: &Runtime,
    source: Option<&RunSource>,
    line: Option<usize>,
    scopes: &[&ExecEnv],
) -> Vec<JsonValue> {
    match result {
        ExecWitnessStmtResult::WitnessExistFact(ExecWitnessExistFactStmtResult::Success(proof)) => {
            let local = scoped(scopes, &proof.local_env);
            let fact = crate::ast::fact::exist_shaped_fact_to_fact(
                &proof.statement.exist_shaped_fact_in_witness,
            );
            let mut steps = vec![goal_wd(&fact, true, rt)];
            steps.extend(
                proof
                    .ambient
                    .witness_type_checks
                    .iter()
                    .map(|check| verification_step("requirement", check, rt, source, scopes)),
            );
            steps.extend(introduce_parameters(
                &proof
                    .statement
                    .exist_shaped_fact_in_witness
                    .plain()
                    .typed_parameters,
                line,
                rt,
            ));
            for binding in &proof.witness_equalities {
                steps.push(object_for(
                    rt,
                    vec![
                        ("kind", string("bind_witness")),
                        ("facts", array_of_strings(store_fact_texts(&binding.store))),
                    ],
                ));
            }
            steps.extend(body_steps(
                &proof.proof_steps,
                &[],
                source,
                children(source, line),
                rt,
                &local,
            ));
            steps.extend(
                proof
                    .obligations
                    .body_checks
                    .iter()
                    .chain(proof.obligations.uniqueness_check.iter())
                    .map(|proof| verification_step("requirement", proof, rt, source, &local)),
            );
            steps.push(publish(rt, None, &[&proof.store_and_infer_result]));
            steps
        }
        ExecWitnessStmtResult::WitnessExistFact(ExecWitnessExistFactStmtResult::Failed(
            failure,
        )) => match failure {
            ExecWitnessExistFactStmtFailed::ProofBody(body) => {
                failed_body_steps(body, &[], source, children(source, line), rt, scopes)
            }
            ExecWitnessExistFactStmtFailed::WitnessType(result)
            | ExecWitnessExistFactStmtFailed::BodyCheck(result)
            | ExecWitnessExistFactStmtFailed::Uniqueness(result) => {
                vec![verification_step("requirement", result, rt, source, scopes)]
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}
