use crate::execute::{ExecDefStrategyStmtResult, ExecDefStrategyStmtSuccess, ExecDefThmBodyProof, ExecDefThmStmtResult};
use crate::prelude::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{SearchProofByKnownStrategy, DetailedSearchProofByKnownStrategy};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::SequenceLimitPredicateDomainProof;

const APPLICATION: &str = r#"prop replay_zero(x R):
    x = 0
strategy replay_use_zero:
    ? forall x R:
        x = 0
        =>:
            $replay_zero(x)
    by def $replay_zero(x)
$replay_zero(0)
"#;
const MULTIPLE: &str = r#"prop replay_equal_zero(x R):
    x = 0
prop replay_nonpositive(x R):
    x <= 0
strategy replay_zero_clauses:
    ? forall x R:
        x = 0
        =>:
            $replay_equal_zero(x)
            $replay_nonpositive(x)
    by def $replay_equal_zero(x)
    by def $replay_nonpositive(x)
$replay_equal_zero(0)
$replay_nonpositive(0)
"#;
const DEPENDENT: &str = r#"prop replay_member_zero(S set, x S):
    x = 0
strategy replay_dependent_zero:
    ? forall S set, x S:
        x = 0
        =>:
            $replay_member_zero(S, x)
    by def $replay_member_zero(S, x)
$replay_member_zero(R, 0)
"#;
const LOCAL: &str = r#"prop replay_local_zero(x R):
    x = 0
claim:
    ? $replay_local_zero(0)
    strategy replay_local_rule:
        ? forall x R:
            x = 0
            =>:
                $replay_local_zero(x)
        by def $replay_local_zero(x)
    $replay_local_zero(0)
"#;
const NESTED: &str = r#"# Replay helper declarations, a claim, a witness and an obtain inside a strategy.
prop same(x R):
    x = 0
strategy use_same:
    ? forall x R:
        x = 0
        =>:
            $same(x)
    have helper R = x
    claim:
        ? helper = 0
        helper = 0
    witness exist u R st {u = helper} from helper
    obtain u from exist u R st {u = helper}
    by def $same(x)
$same(0)
have helper R = 1
helper = 1
"#;
const GUARDED: &str = r#"prop replay_guard_zero(x R):
    x = 0
strategy replay_use_guard_zero:
    ? forall x R:
        x = 0
        =>:
            $replay_guard_zero(x)
    by def $replay_guard_zero(x)
have replay_guard_argument R = 0
$replay_guard_zero(replay_guard_argument)
replay_guard_argument = 0
"#;
const LIMIT_RELATION: &str = r#"# A proved strategy rescales a sequence-limit relation supplied by a lemma.
# Reuse it after equality transport while keeping the actual target limit WD.
abstract_prop witness_limit_relation(x,y,z)

strategy sequence_limit_relation_rescale:
    ? forall s seq(R), L R:
        $has_seq_limit(s,L/2)
        forall t seq(R), V R:
            $has_seq_limit(t,V/2)
            =>:
                $witness_limit_relation(t,V,V)
        =>:
            $witness_limit_relation(s,L,2*lim(s))
    lim(s) = L/2
    2*lim(s) = L
    $witness_limit_relation(s,L,L)
    $witness_limit_relation(s,L,2*lim(s))

forall a,b seq(R), L R:
    a = b
    $has_seq_limit(b,L/2)
    forall t seq(R), V R:
        $has_seq_limit(t,V/2)
        =>:
            $witness_limit_relation(t,V,V)
    =>:
        $witness_limit_relation(a,L,2*lim(b))

# Reuse the strategy after opening an existence hypothesis, then close the result.
thm sequence_strategy_after_existential_choice:
    ? forall L R:
        exist s seq(R) st {$has_seq_limit(s,L/2)}
        forall t seq(R), V R:
            $has_seq_limit(t,V/2)
            =>:
                $witness_limit_relation(t,V,V)
        =>:
            exist s seq(R) st {$has_seq_limit(s,L/2) and $witness_limit_relation(s,L,L)}
    obtain picked_sequence from exist s seq(R) st {$has_seq_limit(s,L/2)}
    $witness_limit_relation(picked_sequence,L,2*lim(picked_sequence))
    lim(picked_sequence)=L/2
    2*lim(picked_sequence)=L
    $witness_limit_relation(picked_sequence,L,L)
    witness exist s seq(R) st {$has_seq_limit(s,L/2) and $witness_limit_relation(s,L,L)} from picked_sequence

# Ordered body clauses retain the certificate needed to form the later selector.
thm sequence_strategy_with_dependent_witness_body:
    ? forall L R:
        exist s seq(R) st {$has_seq_limit(s,L/2)}
        forall t seq(R), V R:
            $has_seq_limit(t,V/2)
            =>:
                $witness_limit_relation(t,V,V)
        =>:
            exist s seq(R) st {$has_seq_limit(s,L/2), $witness_limit_relation(s,L,2*lim(s))}
    obtain picked_sequence from exist s seq(R) st {$has_seq_limit(s,L/2)}
    $witness_limit_relation(picked_sequence,L,2*lim(picked_sequence))
    witness exist s seq(R) st {$has_seq_limit(s,L/2), $witness_limit_relation(s,L,2*lim(s))} from picked_sequence
"#;
const ARITHMETIC_DOMAINS: &str = r#"# Reflexive comparisons retain the real domains of composite operands.
forall x,y R:
    x+y <= x+y

forall x R:
    x/2 <= x/2
"#;
const ANALYSIS_RELATIONS: &str = r#"# Proved rescaling strategies for finite-point limits and Riemann integrals.
# Reuse them across equal functions and points while retaining domain evidence.
abstract_prop witness_function_limit_relation(x,y,z,w)

strategy finite_function_limit_relation_rescale:
    ? forall f fn(t R) R, p,L R:
        $has_limit_at(f,p,L/2)
        forall g fn(inner_t R) R, point_arg,V R:
            $has_limit_at(g,point_arg,V/2)
            =>:
                $witness_function_limit_relation(g,point_arg,V,V)
        =>:
            $witness_function_limit_relation(f,p,L,2*fn_lim(f,p))
    fn_lim(f,p) = L/2
    2*fn_lim(f,p) = L
    $witness_function_limit_relation(f,p,L,L)
    $witness_function_limit_relation(f,p,L,2*fn_lim(f,p))

forall f,g fn(t R) R, p,q,L R:
    f = g
    p = q
    $has_limit_at(g,q,L/2)
    forall h fn(inner_t R) R, point_arg,V R:
        $has_limit_at(h,point_arg,V/2)
        =>:
            $witness_function_limit_relation(h,point_arg,V,V)
    =>:
        $witness_function_limit_relation(f,p,L,2*fn_lim(g,q))

abstract_prop witness_integral_relation(x,y,z,w,u)

strategy riemann_integral_relation_rescale:
    ? forall f fn(t R) R, a,b,I R:
        $has_riemann_integral(f,a,b,I/2)
        forall g fn(inner_t R) R, lower_arg,upper_arg,V R:
            $has_riemann_integral(g,lower_arg,upper_arg,V/2)
            =>:
                $witness_integral_relation(g,lower_arg,upper_arg,V,V)
        =>:
            $witness_integral_relation(f,a,b,I,2*integral(f,a,b))
    integral(f,a,b) = I/2
    2*integral(f,a,b) = I
    $witness_integral_relation(f,a,b,I,I)
    $witness_integral_relation(f,a,b,I,2*integral(f,a,b))

forall f,g fn(t R) R, a,b,c,d,I R:
    f = g
    a = c
    b = d
    $has_riemann_integral(g,c,d,I/2)
    forall h fn(inner_t R) R, lower_arg,upper_arg,V R:
        $has_riemann_integral(h,lower_arg,upper_arg,V/2)
        =>:
            $witness_integral_relation(h,lower_arg,upper_arg,V,V)
    =>:
        $witness_integral_relation(f,a,b,I,2*integral(g,c,d))

# Reuse the strategy after opening an existence hypothesis, then close the result.
thm function_strategy_after_existential_choice:
    ? forall p,L R:
        exist f fn(t R) R st {$has_limit_at(f,p,L/2)}
        forall g fn(inner_t R) R, point_arg,V R:
            $has_limit_at(g,point_arg,V/2)
            =>:
                $witness_function_limit_relation(g,point_arg,V,V)
        =>:
            exist f fn(t R) R st {$has_limit_at(f,p,L/2) and $witness_function_limit_relation(f,p,L,L)}
    obtain picked_function from exist f fn(t R) R st {$has_limit_at(f,p,L/2)}
    $witness_function_limit_relation(picked_function,p,L,2*fn_lim(picked_function,p))
    fn_lim(picked_function,p)=L/2
    2*fn_lim(picked_function,p)=L
    $witness_function_limit_relation(picked_function,p,L,L)
    witness exist f fn(t R) R st {$has_limit_at(f,p,L/2) and $witness_function_limit_relation(f,p,L,L)} from picked_function

thm integral_strategy_after_existential_choice:
    ? forall a,b,I R:
        exist f fn(t R) R st {$has_riemann_integral(f,a,b,I/2)}
        forall g fn(inner_t R) R, lower_arg,upper_arg,V R:
            $has_riemann_integral(g,lower_arg,upper_arg,V/2)
            =>:
                $witness_integral_relation(g,lower_arg,upper_arg,V,V)
        =>:
            exist f fn(t R) R st {$has_riemann_integral(f,a,b,I/2) and $witness_integral_relation(f,a,b,I,I)}
    obtain picked_integrand from exist f fn(t R) R st {$has_riemann_integral(f,a,b,I/2)}
    $witness_integral_relation(picked_integrand,a,b,I,2*integral(picked_integrand,a,b))
    integral(picked_integrand,a,b)=I/2
    2*integral(picked_integrand,a,b)=I
    $witness_integral_relation(picked_integrand,a,b,I,I)
    witness exist f fn(t R) R st {$has_riemann_integral(f,a,b,I/2) and $witness_integral_relation(f,a,b,I,I)} from picked_integrand

# Ordered body clauses retain the certificate needed to form the later selector.
thm function_strategy_with_dependent_witness_body:
    ? forall p,L R:
        exist f fn(t R) R st {$has_limit_at(f,p,L/2)}
        forall g fn(inner_t R) R, point_arg,V R:
            $has_limit_at(g,point_arg,V/2)
            =>:
                $witness_function_limit_relation(g,point_arg,V,V)
        =>:
            exist f fn(t R) R st {$has_limit_at(f,p,L/2), $witness_function_limit_relation(f,p,L,2*fn_lim(f,p))}
    obtain picked_function from exist f fn(t R) R st {$has_limit_at(f,p,L/2)}
    $witness_function_limit_relation(picked_function,p,L,2*fn_lim(picked_function,p))
    witness exist f fn(t R) R st {$has_limit_at(f,p,L/2), $witness_function_limit_relation(f,p,L,2*fn_lim(f,p))} from picked_function

thm integral_strategy_with_dependent_witness_body:
    ? forall a,b,I R:
        exist f fn(t R) R st {$has_riemann_integral(f,a,b,I/2)}
        forall g fn(inner_t R) R, lower_arg,upper_arg,V R:
            $has_riemann_integral(g,lower_arg,upper_arg,V/2)
            =>:
                $witness_integral_relation(g,lower_arg,upper_arg,V,V)
        =>:
            exist f fn(t R) R st {$has_riemann_integral(f,a,b,I/2), $witness_integral_relation(f,a,b,I,2*integral(f,a,b))}
    obtain picked_integrand from exist f fn(t R) R st {$has_riemann_integral(f,a,b,I/2)}
    $witness_integral_relation(picked_integrand,a,b,I,2*integral(picked_integrand,a,b))
    witness exist f fn(t R) R st {$has_riemann_integral(f,a,b,I/2), $witness_integral_relation(f,a,b,I,2*integral(f,a,b))} from picked_integrand
"#;

fn selected(statement: &mut ExecStmtResult) -> &mut DetailedSearchProofByKnownStrategy {
    let atomic = super::atomic_proof_mut(&mut super::fact_statement_mut(statement).verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(
        SearchProofByKnownStrategy::Detailed(p),
    ) = &mut atomic.searched_proof
    else {
        panic!("actual selected KnownStrategy")
    };
    p
}

const DECLARATION: &str = "prop replay_zero(x R):\n    x = 0\nstrategy replay_use_zero:\n    ? forall x R:\n        x = 0\n        =>:\n            $replay_zero(x)\n    by def $replay_zero(x)\n";

fn declaration(statement: &mut ExecStmtResult) -> &mut ExecDefStrategyStmtSuccess {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
        ExecDefStrategyStmtResult::Success(proof),
    )) = statement
    else {
        panic!("actual strategy declaration")
    };
    proof
}

#[test]
fn strategy_declaration_replays_distinct_original_goal_and_body_headers() {
    let (mut run, compiler) = super::execute(DECLARATION);
    let p = declaration(&mut run.statement_results[1]);
    let VerifyFactWellDefinedResult::Success(FactWellDefinedProof::ForallFact(goal)) = &p.goal_wd
    else {
        panic!("original goal formation")
    };
    assert_ne!(
        goal.detailed_ref()
            .introduced_params
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id(),
        p.body
            .introduced_params
            .defined_params
            .store_and_infer_results[0]
            .primary_fact_id()
    );
    super::compile_run(&run, &compiler, "strategy_declaration").unwrap();
}

#[test]
fn strategy_declaration_rejects_missing_original_body_header_and_conclusions() {
    for change in ["parameters", "domain", "steps", "conclusions"] {
        let (mut run, compiler) = super::execute(DECLARATION);
        let p = declaration(&mut run.statement_results[1]);
        match change {
            "parameters" => p
                .body
                .introduced_params
                .defined_params
                .store_and_infer_results
                .clear(),
            "domain" => p.body.assumed_dom_facts.clear(),
            "steps" => p.body.proof_steps.clear(),
            "conclusions" => p.body.conclusion_proofs.clear(),
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn known_strategy_replays_original_clause_and_dependent_instantiation() {
    for (source, index, clause) in [
        (APPLICATION, 2, 0),
        (MULTIPLE, 3, 0),
        (MULTIPLE, 4, 1),
        (DEPENDENT, 2, 0),
    ] {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(
            selected(&mut run.statement_results[index]).then_index,
            clause
        );
        super::compile_run(&run, &compiler, "known_strategy").unwrap();
    }
}

#[test]
fn sequence_limit_strategy_replays_original_real_certificates_and_selected_application() {
    let (mut run, compiler) = super::execute(LIMIT_RELATION);
    let outer = super::forall_proof_mut(&mut run.statement_results[2]);
    let atomic = super::atomic_proof_mut(&mut outer.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(
        SearchProofByKnownStrategy::Detailed(application),
    ) = &atomic.searched_proof
    else {
        panic!("actual selected sequence-limit strategy")
    };
    assert_eq!(application.strategy_name, "sequence_limit_relation_rescale");
    assert_eq!(application.then_index, 0);
    assert_eq!(application.arg_match_proofs.len(), 3);
    assert_eq!(application.forall_parameters_match_what_args.len(), 2);
    assert_eq!(
        application
            .instantiation_requirements
            .detailed_ref()
            .proof_of_dom_facts
            .len(),
        2
    );
    super::compile_run(&run, &compiler, "sequence_limit_strategy").unwrap();
}

#[test]
fn strategy_first_carrier_is_available_only_after_its_declaration() {
    let (mut run, compiler) = super::execute(LIMIT_RELATION);
    let (carrier, local_value) = {
        let proof = declaration(&mut run.statement_results[1]);
        let ParamType::Obj(carrier) =
            &proof.statement.forall_fact.typed_parameters.groups[0].param_type
        else {
            panic!()
        };
        let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(candidate)) =
            &proof.statement.forall_fact.dom_facts[0]
        else {
            panic!()
        };
        (carrier.clone(), candidate.value.clone())
    };
    let before = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(compiler
        .compile_object_reference(&carrier, &before)
        .is_err());
    let completed = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    assert!(compiler
        .compile_object_reference(&carrier, &completed)
        .is_ok());
    assert!(compiler
        .compile_object_reference(&local_value, &completed)
        .is_err());
}

#[test]
fn strategy_outer_carrier_rejects_a_changed_declared_subject() {
    let (mut run, compiler) = super::execute(LIMIT_RELATION);
    let carrier = {
        let proof = declaration(&mut run.statement_results[1]);
        let group = &mut proof.statement.forall_fact.typed_parameters.groups[0];
        let ParamType::Obj(carrier) = &group.param_type else {
            panic!()
        };
        let carrier = carrier.clone();
        group.param_type = ParamType::Obj(Obj::StandardSet(StandardSet::C));
        carrier
    };
    let completed = SourcePosition::new(None, SourceOwner::Run(&run), 2);
    let error = compiler
        .compile_object_reference(&carrier, &completed)
        .err()
        .expect("the declaration no longer matches its original carrier formation");
    assert_eq!(error.route, "WD/OuterCarrierSubject");
}

#[test]
fn completed_quantifier_keeps_later_dependent_carriers_inside_its_binders() {
    let (run, compiler) = super::execute("forall A set, x A, f fn(t A) A:\n    =>:\n        f=f\n");
    super::compile_run(&run, &compiler, "dependent_carrier_scope").unwrap();
    let fact = &super::forall_proof(&run.statement_results[0]).fact;
    let ParamType::Obj(carrier) = &fact.typed_parameters.groups[2].param_type else {
        panic!()
    };
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(compiler
        .compile_object_reference(carrier, &outside)
        .is_err());
}

#[test]
fn obtained_selectors_replay_the_selected_local_application_and_close_witnesses() {
    for (source, applications) in [
        (
            LIMIT_RELATION,
            &[
                (3usize, 2usize, "sequence_limit_relation_rescale"),
                (4, 2, "sequence_limit_relation_rescale"),
            ][..],
        ),
        (
            ANALYSIS_RELATIONS,
            &[
                (6usize, 2usize, "finite_function_limit_relation_rescale"),
                (7, 5, "riemann_integral_relation_rescale"),
                (8, 2, "finite_function_limit_relation_rescale"),
                (9, 5, "riemann_integral_relation_rescale"),
            ][..],
        ),
    ] {
        let (mut run, compiler) = super::execute(source);
        for (index, original, strategy) in applications {
            let original = super::forall_proof(&run.statement_results[*original])
                .fact
                .fact_id;
            let theorem = super::named_theorem_mut(&mut run.statement_results[*index]);
            let ExecDefThmBodyProof::Forall(body) = &mut theorem.body else {
                panic!()
            };
            let result = &mut super::fact_statement_mut(&mut body.proof_steps[1]).verify_result;
            let atomic = super::atomic_proof_mut(result);
            match &atomic.searched_proof {
                AtomicExceptEqualityFactSearchedProof::ByKnownForallFact(application) => {
                    let application = application.detailed_ref();
                    assert_eq!(application.cite.fact_id, original);
                    assert!(matches!(
                        application.cite.location,
                        ForallConclusionLocation::DirectThenFact(DirectForallConclusionLocation {
                            then_fact_index: 0
                        })
                    ));
                    assert!(!application
                        .instantiation_requirements
                        .detailed_ref()
                        .proof_of_dom_facts
                        .is_empty());
                    eprintln!(
                        "SELECTED local theorem {index}: original forall {}",
                        original.value()
                    );
                }
                AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(
                    SearchProofByKnownStrategy::Detailed(application),
                ) => {
                    assert_eq!(application.strategy_name.as_str(), *strategy);
                    assert_eq!(application.then_index, 0);
                    assert!(!application
                        .instantiation_requirements
                        .detailed_ref()
                        .proof_of_dom_facts
                        .is_empty());
                    eprintln!(
                        "SELECTED local theorem {index}: strategy {}",
                        application.strategy_name
                    );
                }
                _ => panic!("retain the actual original lemma or strategy application"),
            }
        }
        if let Err(error) = super::compile_run(&run, &compiler, "obtained_strategy") {
            for (index, _, _) in applications {
                let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
                    ExecDefThmStmtResult::Success(theorem),
                )) = &run.statement_results[*index]
                else {
                    panic!()
                };
                let Fact::ForallFact(fact) = &theorem.statement.fact else {
                    panic!()
                };
                let ExecDefThmBodyProof::Forall(body) = &theorem.body else {
                    panic!()
                };
                let root = SourcePosition::new(None, SourceOwner::Run(&run), *index);
                let head = fact.typed_parameters.ordered_param_ids().len() + fact.dom_facts.len();
                for (step_index, step) in body.proof_steps.iter().enumerate() {
                    let scope = SourcePosition::new(
                        Some(&root),
                        SourceOwner::Named(theorem),
                        head + step_index,
                    );
                    if let Err(step_error) =
                        compiler.compile_statement_in_scope(step, &scope, step_index + 1, true)
                    {
                        eprintln!(
                            "LOCAL FAILURE theorem {index}, body step {step_index}: {step_error}"
                        );
                        break;
                    }
                }
            }
            panic!("{error}");
        }
    }
}

#[test]
fn obtained_membership_uses_only_the_published_witness_prefix() {
    let (run, compiler) = super::execute(LIMIT_RELATION);
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefThm(
        ExecDefThmStmtResult::Success(proof),
    )) = &run.statement_results[3]
    else {
        panic!()
    };
    let Fact::ForallFact(fact) = &proof.statement.fact else {
        panic!()
    };
    let Fact::ExistFact(existence) = &fact.dom_facts[0] else {
        panic!()
    };
    let QuantifierFreeFact::AtomicFact(AtomicFact::HasSequenceLimitFact(candidate)) =
        &existence.facts[0]
    else {
        panic!()
    };
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 3);
    let head = fact.typed_parameters.ordered_param_ids().len() + fact.dom_facts.len();
    let before = SourcePosition::new(Some(&root), SourceOwner::Named(proof), head);
    assert!(compiler
        .compile_real_membership_certificate(&candidate.value, &before)
        .is_err());
    let after = SourcePosition {
        before: head + 1,
        ..before
    };
    assert!(compiler
        .compile_real_membership_certificate(&candidate.value, &after)
        .is_ok());
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    assert!(compiler
        .compile_real_membership_certificate(&candidate.value, &outside)
        .is_err());
}

fn sequence_real_certificate(
    run: &RunLitexCodeResult,
    compiler: &crate::compile_to_lean::LitexToLeanCompiler,
    completed_domains: usize,
) -> Result<String, crate::compile_to_lean::LeanCompileError> {
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
        ExecDefStrategyStmtResult::Success(proof),
    )) = &run.statement_results[1]
    else {
        panic!()
    };
    let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(candidate)) =
        &proof.statement.forall_fact.dom_facts[0]
    else {
        panic!()
    };
    let parameters = proof
        .statement
        .forall_fact
        .typed_parameters
        .ordered_param_ids()
        .len();
    let root = SourcePosition::new(None, SourceOwner::Run(run), 1);
    let scope = SourcePosition::new(
        Some(&root),
        SourceOwner::Strategy(proof),
        parameters + completed_domains,
    );
    compiler.compile_real_membership_certificate(&candidate.value, &scope)
}

fn sequence_domain_mut(run: &mut RunLitexCodeResult) -> &mut SequenceLimitPredicateDomainProof {
    let proof = declaration(&mut run.statement_results[1]);
    let FactWellDefinedProof::AtomicExceptEquality(wd) =
        &mut proof.body.assumed_dom_facts[0].well_defined
    else {
        panic!()
    };
    let PredicateDomainProof::SequenceLimit(domain) =
        &mut wd.as_detailed_mut().unwrap().predicate_domain
    else {
        panic!()
    };
    domain
}

#[test]
fn structural_real_certificate_keeps_its_completed_header_stage_and_local_scope() {
    let (run, compiler) = super::execute(LIMIT_RELATION);
    assert!(sequence_real_certificate(&run, &compiler, 0).is_err());
    assert!(sequence_real_certificate(&run, &compiler, 1).is_ok());
    let ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
        ExecDefStrategyStmtResult::Success(proof),
    )) = &run.statement_results[1]
    else {
        panic!()
    };
    let Fact::AtomicFact(AtomicFact::HasSequenceLimitFact(candidate)) =
        &proof.statement.forall_fact.dom_facts[0]
    else {
        panic!()
    };
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    assert!(compiler
        .compile_real_membership_certificate(&candidate.value, &outside)
        .is_err());
}

#[test]
fn structural_real_certificate_rejects_a_changed_checked_argument_or_carrier() {
    let (mut run, compiler) = super::execute(LIMIT_RELATION);
    let original = {
        let membership = &mut sequence_domain_mut(&mut run).value_real;
        let Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) = &membership.element else {
            panic!()
        };
        let wrong = div.left.as_ref().clone();
        std::mem::replace(&mut membership.element, wrong)
    };
    let error = sequence_real_certificate(&run, &compiler, 1)
        .err()
        .expect("different checked argument");
    assert_eq!(error.route, "WD/DomainMembershipSubject");
    sequence_domain_mut(&mut run).value_real.element = original;

    let original = std::mem::replace(
        &mut sequence_domain_mut(&mut run).value_real.set,
        StandardSet::C,
    );
    let error = sequence_real_certificate(&run, &compiler, 1)
        .err()
        .expect("complex is not a real certificate");
    assert_eq!(error.route, "WD/DomainMembershipCarrier");
    sequence_domain_mut(&mut run).value_real.set = original;
    assert!(sequence_real_certificate(&run, &compiler, 1).is_ok());
}

#[test]
fn order_domains_use_the_shared_membership_stage_without_reading_future_evidence() {
    let (run, compiler) = super::execute(ARITHMETIC_DOMAINS);
    for index in 0..run.statement_results.len() {
        let outer = super::forall_proof(&run.statement_results[index]);
        let result = &outer.proved_then_facts[0].verify_result;
        let VerifyFactResult::AtomicExceptEquality(result) = result else {
            panic!()
        };
        let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_ref() else {
            panic!()
        };
        let wd = proof.well_defined_proof.detailed_ref();
        let PredicateDomainProof::ByRequirements(domains) = &wd.predicate_domain else {
            panic!("original checked comparison domains")
        };
        let value = wd.well_defined_of_each_parameter[0].obj();
        let root = SourcePosition::new(None, SourceOwner::Run(&run), index);
        let head =
            outer.fact.typed_parameters.ordered_param_ids().len() + outer.fact.dom_facts.len();
        let parent = SourcePosition::new(Some(&root), SourceOwner::Forall(outer), head);
        let VerifyFactResult::AtomicExceptEquality(_) = &outer.proved_then_facts[0].verify_result
        else {
            unreachable!()
        };
        let before = SourcePosition::new(
            Some(&parent),
            SourceOwner::Verify(&outer.proved_then_facts[0].verify_result),
            wd.well_defined_of_each_parameter.len(),
        );
        assert!(compiler
            .compile_real_membership_certificate(value, &before)
            .is_err());
        let after = SourcePosition {
            before: wd.well_defined_of_each_parameter.len() + domains.len(),
            ..before
        };
        assert!(compiler
            .compile_real_membership_certificate(value, &after)
            .is_ok());
    }
    super::compile_run(&run, &compiler, "arithmetic_domain_stages").unwrap();
}

#[test]
fn known_strategy_rejects_changed_name_clause_arguments_and_requirements() {
    for change in [
        "name",
        "clause",
        "matches",
        "arguments",
        "requirements",
        "domain",
    ] {
        let (mut run, compiler) = super::execute(APPLICATION);
        let p = selected(&mut run.statement_results[2]);
        match change {
            "name" => p.strategy_name = "missing_strategy".into(),
            "clause" => p.then_index = 10,
            "matches" => p.arg_match_proofs.clear(),
            "arguments" => p.forall_parameters_match_what_args.clear(),
            "requirements" => p
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .param_type_requirements
                .clear(),
            "domain" => p
                .instantiation_requirements
                .as_detailed_mut()
                .unwrap()
                .proof_of_dom_facts
                .clear(),
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn known_strategy_cannot_resolve_a_future_declaration_from_final_runtime() {
    let (mut run, compiler) = super::execute(APPLICATION);
    selected(&mut run.statement_results[2]);
    run.statement_results.swap(1, 2);
    let error = super::compile_run(&run, &compiler, "future_strategy").unwrap_err();
    assert_eq!(error.route, "Strategy/DeclarationProducer");
}

#[test]
fn local_strategy_replays_without_publishing_its_name_outside_the_claim() {
    let (run, compiler) = super::execute(LOCAL);
    super::compile_run(&run, &compiler, "local_strategy").unwrap();
    let root = SourcePosition::new(None, SourceOwner::Run(&run), run.statement_results.len());
    assert!(root.visible_strategy("replay_local_rule").is_err());
}

#[test]
fn strategy_nested_proof_replays_claim_witness_obtain_and_original_conclusion() {
    let (mut run, compiler) = super::execute(NESTED);
    assert_eq!(
        declaration(&mut run.statement_results[1])
            .body
            .proof_steps
            .len(),
        5
    );
    selected(&mut run.statement_results[2]);
    super::compile_run(&run, &compiler, "strategy_nested_body").unwrap();
}

#[test]
fn known_strategy_replays_guard_citation_and_rejects_missing_or_future_guard() {
    for future in [false, true] {
        let (mut run, compiler) = super::execute(GUARDED);
        selected(&mut run.statement_results[3]);
        super::compile_run(&run, &compiler, "original_strategy_guard").unwrap();
        let unavailable = if future {
            super::equality_proof_mut(
                &mut super::fact_statement_mut(&mut run.statement_results[4]).verify_result,
            )
            .fact
            .fact_id
        } else {
            FactId::new(u64::MAX)
        };
        let p = selected(&mut run.statement_results[3]);
        let requirements = p.instantiation_requirements.as_detailed_mut().unwrap();
        let path = super::equality_path_mut(&mut requirements.proof_of_dom_facts[0]);
        assert_eq!(path.path.len(), 1);
        path.path[0].2 = unavailable;
        let error = super::compile_run(&run, &compiler, "unavailable_strategy_guard").unwrap_err();
        assert_eq!(
            error.route,
            if future {
                "FactId/Producer"
            } else {
                "FactId/Resolution"
            }
        );
    }
}
