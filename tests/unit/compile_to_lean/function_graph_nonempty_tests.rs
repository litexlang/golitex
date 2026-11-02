use crate::execute::execute_fact_stmt::function_domain::{CompleteFunctionDomainSourceProof as S, FunctionDomainNonemptyEvidence as E, FunctionDomainArgumentMembershipProof as A};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::FunctionGraphNonemptyFromDomainStrategySingleStep;
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
macro_rules! source {
    ($s:literal) => {
        include_str!(concat!(
            "../../../lean/examples/function_graph_nonempty_",
            $s,
            "/statement.lit"
        ))
    };
}
const DOMAIN: &str = source!("domain");
const GROUPS: &str = source!("groups");
const ARGS: &str = source!("arguments");
const EXIST: &str = source!("multiple_exist");
const ALL: &[&str] = &[
    DOMAIN,
    GROUPS,
    ARGS,
    EXIST,
    source!("guard"),
    source!("exist"),
    source!("closed_range"),
    source!("half_open"),
    source!("anonymous"),
    source!("composition"),
    source!("matrix"),
    source!("application"),
    source!("selector"),
    source!("subject_transport"),
    source!("carrier_transport"),
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
    for source in [source!("closed_range"), source!("half_open")] {
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
    for source in [source!("subject_transport"), source!("carrier_transport")] {
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
        let (mut run, c) = super::execute(source!("application"));
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
    let (mut run, c) = super::execute(source!("matrix"));
    selected(&mut run.statement_results[0])
        .source
        .signature
        .ret_set = Box::new(Obj::StandardSet(StandardSet::C));
    reject(&run, &c, "matrix_signature");
    let (mut run, c) = super::execute(source!("selector"));
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
