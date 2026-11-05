use crate::execute::execute_fact_stmt::function_domain::{CompleteFunctionDomainSourceProof as S, FunctionDomainNonemptyEvidence as E, FunctionDomainArgumentMembershipProof as A};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::FunctionGraphNonemptyFromDomainStrategySingleStep;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
const DOMAIN: &str = r#"# A function graph is nonempty when its complete input domain is nonempty.
forall replay_graph_A nonempty_set,replay_graph_B set,replay_graph_f fn(replay_graph_x replay_graph_A) replay_graph_B:
    $is_nonempty_set(replay_graph_f)
"#;
const GROUPS: &str = r#"# Nonempty parameter groups supply a complete input for the function graph.
forall replay_graph_group_A nonempty_set,replay_graph_group_B nonempty_set,replay_graph_group_C set,replay_graph_group_f fn(replay_graph_group_x,replay_graph_group_y replay_graph_group_A,replay_graph_group_z replay_graph_group_B) replay_graph_group_C:
    $is_nonempty_set(replay_graph_group_f)
"#;
const ARGS: &str = r#"# The ordered singleton inputs satisfy both guards of a three-argument function.
forall replay_graph_args_C set,replay_graph_args_f fn(replay_graph_args_x {2},replay_graph_args_y {3},replay_graph_args_z {4}:replay_graph_args_x<replay_graph_args_y,replay_graph_args_y<replay_graph_args_z) replay_graph_args_C:
    $is_nonempty_set(replay_graph_args_f)
"#;
const EXIST: &str = r#"# A joint guarded input witness supplies a point of a two-argument graph.
forall replay_graph_multi_A,replay_graph_multi_B set,replay_graph_multi_c,replay_graph_multi_d R,replay_graph_multi_f fn(replay_graph_multi_x replay_graph_multi_A,replay_graph_multi_y replay_graph_multi_B:replay_graph_multi_x!=replay_graph_multi_c,replay_graph_multi_y!=replay_graph_multi_d) R:
    exist replay_graph_multi_w replay_graph_multi_A,replay_graph_multi_z replay_graph_multi_B st {replay_graph_multi_w!=replay_graph_multi_c,replay_graph_multi_z!=replay_graph_multi_d}
    =>:
        $is_nonempty_set(replay_graph_multi_f)
"#;
const ALL: &[&str] = &[
    DOMAIN,
    GROUPS,
    ARGS,
    EXIST,
    r#"# The original admissible zero input supplies a point of the function graph.
forall replay_graph_guard_B set,replay_graph_guard_f fn(replay_graph_guard_x R: replay_graph_guard_x=0) replay_graph_guard_B:
    $is_nonempty_set(replay_graph_guard_f)
"#,
    r#"# An existing guarded input witness supplies a point of the function graph.
forall replay_graph_exist_A set,replay_graph_exist_B set,replay_graph_exist_c R,replay_graph_exist_f fn(replay_graph_exist_x replay_graph_exist_A: replay_graph_exist_x!=replay_graph_exist_c) replay_graph_exist_B:
    exist replay_graph_exist_w replay_graph_exist_A st {replay_graph_exist_w!=replay_graph_exist_c}
    =>:
        $is_nonempty_set(replay_graph_exist_f)
"#,
    r#"# The left endpoint of an ordered closed integer interval is an admissible input.
forall replay_graph_range_a,replay_graph_range_b Z,replay_graph_range_C set,replay_graph_range_f fn(replay_graph_range_x closed_range(replay_graph_range_a,replay_graph_range_b):replay_graph_range_x=replay_graph_range_x) replay_graph_range_C:
    replay_graph_range_a<=replay_graph_range_b
    =>:
        $is_nonempty_set(replay_graph_range_f)
"#,
    r#"# The left endpoint of a strictly ordered half-open integer interval is admissible.
forall replay_graph_half_a,replay_graph_half_b Z,replay_graph_half_C set,replay_graph_half_f fn(replay_graph_half_x range(replay_graph_half_a,replay_graph_half_b):replay_graph_half_x=replay_graph_half_x) replay_graph_half_C:
    replay_graph_half_a<replay_graph_half_b
    =>:
        $is_nonempty_set(replay_graph_half_f)
"#,
    r#"# The identity function on positive real inputs has a nonempty graph.
$is_nonempty_set(fn(replay_graph_anon_x R+) R {replay_graph_anon_x})
"#,
    r#"# The composition of real identity functions has a nonempty graph.
have fn replay_graph_identity(replay_graph_identity_x R) R = replay_graph_identity_x
$is_nonempty_set(replay_graph_identity ∘ replay_graph_identity)
"#,
    r#"# A positive-order identity matrix has a nonempty graph of entries.
$is_nonempty_set(identity_matrix(2))
"#,
    r#"# A returned function on the real line has a nonempty graph.
forall replay_graph_higher_f fn(replay_graph_higher_x R) fn(replay_graph_higher_y R) R,replay_graph_higher_p R:
    $is_nonempty_set(replay_graph_higher_f(replay_graph_higher_p))
"#,
    r#"# A selected two-coordinate gradient has a nonempty finite graph.
forall replay_graph_select_f fn(replay_graph_select_x cart_n(R,2)) R,replay_graph_select_p,replay_graph_select_g cart_n(R,2):
    $has_gradient_at(replay_graph_select_f,replay_graph_select_p,2,replay_graph_select_g)
    =>:
        $is_nonempty_set(gradient_at(replay_graph_select_f,replay_graph_select_p,2))
"#,
    r#"# Equality to an identity function transports graph nonemptiness.
forall replay_graph_alias_A nonempty_set,replay_graph_alias_f set:
    replay_graph_alias_f=fn(replay_graph_alias_x replay_graph_alias_A) replay_graph_alias_A {replay_graph_alias_x}
    =>:
        $is_nonempty_set(replay_graph_alias_f)
"#,
    r#"# An original function-space equality retains the nonempty input domain.
forall replay_graph_car_A nonempty_set,replay_graph_car_B set,replay_graph_car_S set,replay_graph_car_f replay_graph_car_S:
    replay_graph_car_S=fn(replay_graph_car_x replay_graph_car_A) replay_graph_car_B
    =>:
        $is_nonempty_set(replay_graph_car_f)
"#,
];
fn atom(statement: &mut ExecStmtResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = statement else {
        panic!("original graph fact")
    };
    let proof = match &mut p.verify_result {
        VerifyFactResult::ForallFact(p) => {
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                p.as_mut()
            else {
                panic!("local forall")
            };
            &mut p.proved_then_facts[0].verify_result
        }
        p => p,
    };
    super::atomic_proof_mut(proof)
}
fn selected(
    statement: &mut ExecStmtResult,
) -> &mut FunctionGraphNonemptyFromDomainStrategySingleStep {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionGraphNonemptyFromDomain(p),
    ) = &mut atom(statement).searched_proof
    else {
        panic!("actual selected graph-domain strategy")
    };
    p
}
fn carrier_leaf(statement: &mut ExecStmtResult) -> &mut VerifyFactResult {
    let E::ParameterCarriers(p) = &mut selected(statement).domain_nonempty.evidence else {
        panic!("original carrier proof")
    };
    &mut p[0]
}
fn existential(statement: &mut ExecStmtResult) -> &mut VerifyPlainExistFactSuccess {
    let E::ExistingWitness(p) = &mut selected(statement).domain_nonempty.evidence else {
        panic!("original existing witness")
    };
    let VerifyFactResult::ExistShapedFact(p) = p.as_mut() else {
        panic!()
    };
    let VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(p)) =
        p.as_mut()
    else {
        panic!()
    };
    p
}
fn reject(run: &RunLitexCodeResult, c: &crate::compile_to_lean::LitexToLeanCompiler, name: &str) {
    assert!(
        super::compile_run(run, c, name).is_err(),
        "changed original evidence accepted: {name}"
    );
}
#[test]
fn graph_nonempty_replays_three_domain_and_six_original_complete_source_forms() {
    let mut sources = std::collections::BTreeSet::new();
    let mut domains = std::collections::BTreeSet::new();
    for source in ALL {
        let (mut run, c) = super::execute(source);
        let index = run.statement_results.len() - 1;
        let p = selected(&mut run.statement_results[index]);
        sources.insert(match &p.source.source {
            S::Membership { .. } => "membership",
            S::AnonymousFunction { .. } => "anonymous",
            S::Composition(_) => "composition",
            S::Matrix(_) => "matrix",
            S::ApplicationReturn { .. } => "returned",
            S::MultivariableSelector(_) => "selector",
            _ => panic!("new unprofiled source"),
        });
        domains.insert(match &p.domain_nonempty.evidence {
            E::ParameterCarriers(_) => "carriers",
            E::ArgumentWitness { .. } => "arguments",
            E::ExistingWitness(_) => "exist",
        });
        let output = super::compile_run(&run, &c, "original_graph_nonempty").unwrap();
        assert!(output.contains("Litex.functionGraphNonemptyOfDomain"));
        assert_eq!(
            output,
            super::compile_run(&run, &c, "original_graph_nonempty").unwrap()
        );
    }
    assert_eq!(sources.len(), 6);
    assert_eq!(domains.len(), 3);
}
#[test]
fn graph_nonempty_preserves_both_original_signatures_and_parameter_identities() {
    for change in ["source", "domain", "both_ids", "return", "guards"] {
        let (mut run, c) = super::execute(DOMAIN);
        let p = selected(&mut run.statement_results[0]);
        match change {
            "source" => {
                p.source.signature.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::R))
            }
            "domain" => {
                p.domain_nonempty.signature.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::R))
            }
            "both_ids" => {
                p.source.signature.set_bound_parameters.groups[0].params[0].id =
                    IdentifierId::new(u64::MAX);
                p.domain_nonempty.signature.set_bound_parameters.groups[0].params[0].id =
                    IdentifierId::new(u64::MAX);
            }
            "return" => {
                p.domain_nonempty.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C))
            }
            _ => p
                .domain_nonempty
                .signature
                .set_bound_parameters
                .groups
                .clear(),
        };
        reject(&run, &c, change);
    }
}
#[test]
fn graph_nonempty_replays_carrier_groups_instead_of_inventing_parameter_witnesses() {
    for change in ["missing", "order"] {
        let (mut run, c) = super::execute(GROUPS);
        let E::ParameterCarriers(children) = &mut selected(&mut run.statement_results[0])
            .domain_nonempty
            .evidence
        else {
            panic!()
        };
        if change == "missing" {
            children.pop();
        } else {
            children.swap(0, 1);
        }
        reject(&run, &c, change);
    }
}
#[test]
fn graph_nonempty_carrier_leaf_needs_its_subject_wd_and_exact_prior_citation() {
    for change in ["subject", "wd", "missing", "future"] {
        let (mut run, c) = super::execute(DOMAIN);
        let p = super::atomic_proof_mut(carrier_leaf(&mut run.statement_results[0]));
        match change {
            "subject" => {
                let AtomicFact::IsNonemptySetFact(f) = &mut p.fact else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::R);
            }
            "wd" => {
                p.well_defined_proof
                    .as_detailed_mut()
                    .unwrap()
                    .well_defined_of_each_parameter
                    .pop();
            }
            _ => {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
                    &mut p.searched_proof
                else {
                    panic!()
                };
                cite.cite_fact_id = if change == "future" {
                    p.fact.fact_id()
                } else {
                    FactId::new(u64::MAX)
                };
            }
        }
        reject(&run, &c, change);
    }
}
#[test]
fn graph_nonempty_argument_witness_keeps_all_inputs_memberships_and_guards_in_order() {
    for change in [
        "argument_count",
        "member_count",
        "guard_count",
        "arguments",
        "members",
        "guards",
    ] {
        let (mut run, c) = super::execute(ARGS);
        let E::ArgumentWitness {
            arguments,
            memberships,
            guards,
        } = &mut selected(&mut run.statement_results[0])
            .domain_nonempty
            .evidence
        else {
            panic!()
        };
        match change {
            "argument_count" => {
                arguments.pop();
            }
            "member_count" => {
                memberships.pop();
            }
            "guard_count" => {
                guards.pop();
            }
            "arguments" => arguments.swap(0, 1),
            "members" => memberships.swap(0, 1),
            _ => guards.swap(0, 1),
        }
        reject(&run, &c, change);
    }
}
#[test]
fn graph_nonempty_argument_membership_retains_original_wd_and_citation() {
    for change in ["subject", "wd"] {
        let (mut run, c) = super::execute(ARGS);
        let E::ArgumentWitness { memberships, .. } = &mut selected(&mut run.statement_results[0])
            .domain_nonempty
            .evidence
        else {
            panic!()
        };
        let A::Verified(child) = &mut memberships[0] else {
            panic!()
        };
        let p = super::atomic_proof_mut(child);
        if change == "subject" {
            let AtomicFact::InFact(f) = &mut p.fact else {
                panic!()
            };
            f.set = Obj::StandardSet(StandardSet::R);
        } else {
            p.well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter
                .pop();
        }
        reject(&run, &c, change);
    }
}
#[test]
fn graph_nonempty_integer_range_start_retains_integer_order_and_carrier_evidence() {
    for source in [
        r#"# The left endpoint of an ordered closed integer interval is an admissible input.
forall replay_graph_range_a,replay_graph_range_b Z,replay_graph_range_C set,replay_graph_range_f fn(replay_graph_range_x closed_range(replay_graph_range_a,replay_graph_range_b):replay_graph_range_x=replay_graph_range_x) replay_graph_range_C:
    replay_graph_range_a<=replay_graph_range_b
    =>:
        $is_nonempty_set(replay_graph_range_f)
"#,
        r#"# The left endpoint of a strictly ordered half-open integer interval is admissible.
forall replay_graph_half_a,replay_graph_half_b Z,replay_graph_half_C set,replay_graph_half_f fn(replay_graph_half_x range(replay_graph_half_a,replay_graph_half_b):replay_graph_half_x=replay_graph_half_x) replay_graph_half_C:
    replay_graph_half_a<replay_graph_half_b
    =>:
        $is_nonempty_set(replay_graph_half_f)
"#,
    ] {
        for change in ["integer", "order", "wd"] {
            let (mut run, c) = super::execute(source);
            let E::ArgumentWitness { memberships, .. } =
                &mut selected(&mut run.statement_results[0])
                    .domain_nonempty
                    .evidence
            else {
                panic!()
            };
            let A::IntegerRangeStart {
                integer,
                endpoint_order,
            } = &mut memberships[0]
            else {
                panic!("original range-start fallback")
            };
            if change == "integer" {
                let AtomicFact::InFact(f) = &mut super::atomic_proof_mut(integer).fact else {
                    panic!()
                };
                f.set = Obj::StandardSet(StandardSet::R);
            } else {
                let p = super::atomic_proof_mut(endpoint_order);
                if change == "wd" {
                    p.well_defined_proof
                        .as_detailed_mut()
                        .unwrap()
                        .well_defined_of_each_parameter
                        .pop();
                } else {
                    match &mut p.fact {
                        AtomicFact::LessFact(f) => {
                            f.right = Obj::Literal(Literal::Number(Number::new("0".into())))
                        }
                        AtomicFact::LessEqualFact(f) => {
                            f.right = Obj::Literal(Literal::Number(Number::new("0".into())))
                        }
                        _ => panic!(),
                    }
                }
            }
            reject(&run, &c, change);
        }
    }
}
#[test]
fn graph_nonempty_existing_witness_keeps_original_binders_guards_and_formation() {
    for change in ["binder", "carrier", "guard", "wd"] {
        let (mut run, c) = super::execute(EXIST);
        let p = existential(&mut run.statement_results[0]);
        if change == "wd" {
            p.well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .introduced_params
                .param_type_well_defined
                .pop();
        } else {
            let ExistShapedFact::Exist(f) = &mut p.fact else {
                panic!()
            };
            match change {
                "binder" => f.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX),
                "carrier" => {
                    f.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::R))
                }
                _ => f.facts.swap(0, 1),
            }
        }
        reject(&run, &c, change);
    }
}
#[test]
fn graph_nonempty_existing_witness_cannot_replace_its_original_existential_citation() {
    let (mut run, c) = super::execute(EXIST);
    let p = existential(&mut run.statement_results[0]);
    let ExistShapedFactSearchedProof::ByKnownExistShapedFact(cite) = &mut p.searched_proof else {
        panic!("actual stored existential")
    };
    cite.cite_fact_id = FactId::new(u64::MAX);
    reject(&run, &c, "missing_existential");
}
#[test]
fn graph_nonempty_membership_source_needs_its_original_fact_and_subject() {
    for change in ["identity", "subject"] {
        let (mut run, c) = super::execute(DOMAIN);
        let S::Membership { membership, .. } =
            &mut selected(&mut run.statement_results[0]).source.source
        else {
            panic!()
        };
        if change == "identity" {
            membership.fact_id = FactId::new(u64::MAX);
        } else {
            membership.element = Obj::StandardSet(StandardSet::R);
        }
        reject(&run, &c, change);
    }
}
#[test]
fn graph_nonempty_transports_retain_the_actual_subject_and_carrier_paths() {
    for source in [
        r#"# Equality to an identity function transports graph nonemptiness.
forall replay_graph_alias_A nonempty_set,replay_graph_alias_f set:
    replay_graph_alias_f=fn(replay_graph_alias_x replay_graph_alias_A) replay_graph_alias_A {replay_graph_alias_x}
    =>:
        $is_nonempty_set(replay_graph_alias_f)
"#,
        r#"# An original function-space equality retains the nonempty input domain.
forall replay_graph_car_A nonempty_set,replay_graph_car_B set,replay_graph_car_S set,replay_graph_car_f replay_graph_car_S:
    replay_graph_car_S=fn(replay_graph_car_x replay_graph_car_A) replay_graph_car_B
    =>:
        $is_nonempty_set(replay_graph_car_f)
"#,
    ] {
        for change in ["missing", "citation"] {
            let (mut run, c) = super::execute(source);
            let path = match &mut selected(&mut run.statement_results[0]).source.source {
                S::AnonymousFunction { subject_equal, .. } => subject_equal,
                S::Membership { carrier_equal, .. } => carrier_equal,
                _ => panic!(),
            };
            assert!(!path.path.is_empty());
            if change == "missing" {
                path.path.clear();
            } else {
                path.path[0].2 = FactId::new(u64::MAX);
            }
            reject(&run, &c, change);
        }
    }
}
#[test]
fn graph_nonempty_returned_function_keeps_original_application_wd_and_signature() {
    for change in ["wd", "ret"] {
        let (mut run, c) = super::execute(
            r#"# A returned function on the real line has a nonempty graph.
forall replay_graph_higher_f fn(replay_graph_higher_x R) fn(replay_graph_higher_y R) R,replay_graph_higher_p R:
    $is_nonempty_set(replay_graph_higher_f(replay_graph_higher_p))
"#,
        );
        let S::ApplicationReturn {
            application_check,
            return_space,
            ..
        } = &mut selected(&mut run.statement_results[0]).source.source
        else {
            panic!()
        };
        if change == "wd" {
            application_check
                .as_detailed_mut()
                .unwrap()
                .child_obj_well_defined
                .pop();
        } else {
            *return_space = Obj::StandardSet(StandardSet::R);
        }
        reject(&run, &c, change);
    }
}
#[test]
fn graph_nonempty_matrix_and_selector_sources_keep_original_constructor_subjects() {
    let (mut run, c) = super::execute(
        r#"# A positive-order identity matrix has a nonempty graph of entries.
$is_nonempty_set(identity_matrix(2))
"#,
    );
    selected(&mut run.statement_results[0])
        .source
        .signature
        .ret_set = Box::new(Obj::StandardSet(StandardSet::C));
    reject(&run, &c, "matrix_signature");
    let (mut run, c) = super::execute(
        r#"# A selected two-coordinate gradient has a nonempty finite graph.
forall replay_graph_select_f fn(replay_graph_select_x cart_n(R,2)) R,replay_graph_select_p,replay_graph_select_g cart_n(R,2):
    $has_gradient_at(replay_graph_select_f,replay_graph_select_p,2,replay_graph_select_g)
    =>:
        $is_nonempty_set(gradient_at(replay_graph_select_f,replay_graph_select_p,2))
"#,
    );
    let S::MultivariableSelector(p) = &mut selected(&mut run.statement_results[0]).source.source
    else {
        panic!()
    };
    p.selector = Obj::StandardSet(StandardSet::R);
    reject(&run, &c, "selector_subject");
}
#[test]
fn graph_nonempty_does_not_borrow_a_sibling_quantifiers_private_carrier_fact() {
    // The first theorem's real codomain does not establish the second theorem
    // for an arbitrary codomain. Both retain independent local introductions.
    let first_source = "forall graph_scope_A nonempty_set, graph_scope_f fn(graph_scope_x graph_scope_A) R:\n    $is_nonempty_set(graph_scope_f)\n";
    let source = format!("{first_source}\n{DOMAIN}");
    let (mut run, c) = super::execute(&source);
    super::compile_run(&run, &c, "separate_graph_scopes").unwrap();
    let first = super::atomic_proof_mut(carrier_leaf(&mut run.statement_results[0]));
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &first.searched_proof
    else {
        panic!()
    };
    let foreign = cite.cite_fact_id;
    let second = super::atomic_proof_mut(carrier_leaf(&mut run.statement_results[1]));
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &mut second.searched_proof
    else {
        panic!()
    };
    assert_ne!(foreign, cite.cite_fact_id);
    cite.cite_fact_id = foreign;
    reject(&run, &c, "escaped_graph_carrier_fact");
}
