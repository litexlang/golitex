use crate::execute::execute_fact_stmt::function_domain::{CompleteFunctionDomainSourceProof as S, FunctionDomainNonemptyEvidence as E, FunctionDomainArgumentMembershipProof as A};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::by_equality_identities_wave13::FnRangeOfConstantAnonymousFnBuiltinRuleProof;
use crate::compile_to_lean::source_position::{SourceOwner,SourcePosition};
use crate::prelude::*;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchedProof;
const DOMAIN: &str =
    "forall replay33_A nonempty_set:\n    fn_range(fn(replay33_cx replay33_A) R {1})={1}\n";
const GROUPS: &str = "forall replay33_GA,replay33_GB nonempty_set:\n    fn_range(fn(replay33_g1 replay33_GA,replay33_g2 replay33_GB) R {1})={1}\n";
const ARGS: &str = "2 $in {2}\n3 $in {3}\n4 $in {4}\nfn_range(fn(replay33_asx {2},replay33_asy {3},replay33_asz {4}:replay33_asx<replay33_asy,replay33_asy<replay33_asz) R {1})={1}\n";
const EXIST: &str = "forall replay33_ma,replay33_mb set,replay33_mc,replay33_md R:\n    exist replay33_mw replay33_ma,replay33_mz replay33_mb st {replay33_mw!=replay33_mc,replay33_mz!=replay33_md}\n    =>:\n        fn_range(fn(replay33_mx replay33_ma,replay33_my replay33_mb:replay33_mx!=replay33_mc,replay33_my!=replay33_md) R {1})={1}\n";
const CLOSED: &str = "forall replay33_ca,replay33_cb Z:\n    replay33_ca<=replay33_cb\n    =>:\n        fn_range(fn(replay33_cz closed_range(replay33_ca,replay33_cb):replay33_cz=replay33_cz) R {1})={1}\n";
const HALF: &str = "forall replay33_ra,replay33_rb Z:\n    replay33_ra<replay33_rb\n    =>:\n        fn_range(fn(replay33_rz range(replay33_ra,replay33_rb):replay33_rz=replay33_rz) R {1})={1}\n";
const ALIAS: &str = "forall replay33_aa nonempty_set,replay33_af set:\n    replay33_af=fn(replay33_alx replay33_aa) R {1}\n    =>:\n        fn_range(replay33_af)={1}\n";
const ALL: &[&str] = &[
"fn_range(fn(replay33_x R) R {1})={1}\n",
"forall replay33_A nonempty_set:\n    fn_range(fn(replay33_cx replay33_A) R {1})={1}\n",
"fn_range(fn(replay33_gx R:replay33_gx=0) R {1})={1}\n",
"forall replay33_GA,replay33_GB nonempty_set:\n    fn_range(fn(replay33_g1 replay33_GA,replay33_g2 replay33_GB) R {1})={1}\n",
"fn_range(fn(replay33_ix closed_range(2,3)) R {1})={1}\n",
"forall replay33_EA set,replay33_ec R:\n    exist replay33_ew replay33_EA st {replay33_ew!=replay33_ec}\n    =>:\n        fn_range(fn(replay33_ex replay33_EA:replay33_ex!=replay33_ec) R {1})={1}\n",
"{1}=fn_range(fn(replay33_rx R) R {1})\n",
"forall replay33_ma,replay33_mb set,replay33_mc,replay33_md R:\n    exist replay33_mw replay33_ma,replay33_mz replay33_mb st {replay33_mw!=replay33_mc,replay33_mz!=replay33_md}\n    =>:\n        fn_range(fn(replay33_mx replay33_ma,replay33_my replay33_mb:replay33_mx!=replay33_mc,replay33_my!=replay33_md) R {1})={1}\n",
"forall replay33_ra,replay33_rb Z:\n    replay33_ra<replay33_rb\n    =>:\n        fn_range(fn(replay33_rz range(replay33_ra,replay33_rb):replay33_rz=replay33_rz) R {1})={1}\n",
"forall replay33_aa nonempty_set,replay33_af set:\n    replay33_af=fn(replay33_alx replay33_aa) R {1}\n    =>:\n        fn_range(replay33_af)={1}\n",
"2 $in {2}\n3 $in {3}\n4 $in {4}\nfn_range(fn(replay33_asx {2},replay33_asy {3},replay33_asz {4}:replay33_asx<replay33_asy,replay33_asy<replay33_asz) R {1})={1}\n",
"forall replay33_ca,replay33_cb Z:\n    replay33_ca<=replay33_cb\n    =>:\n        fn_range(fn(replay33_cz closed_range(replay33_ca,replay33_cb):replay33_cz=replay33_cz) R {1})={1}\n"
];
fn atom(statement: &mut ExecStmtResult) -> &mut VerifyEqualitySuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = statement else {
        panic!("original constant-range fact")
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
    super::equality_proof_mut(proof)
}
fn selected(statement: &mut ExecStmtResult) -> &mut FnRangeOfConstantAnonymousFnBuiltinRuleProof {
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::FnRangeOfConstantAnonymousFn(p),
    ) = &mut atom(statement).searched_proof
    else {
        panic!("actual selected constant-range rule")
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
fn constant_range_replays_three_actual_domain_forms_and_both_orientations() {
    let mut domains = std::collections::BTreeSet::new();
    for source in ALL {
        let (mut run, c) = super::execute(source);
        let p = selected(run.statement_results.last_mut().unwrap());
        assert!(matches!(p.source.source, S::AnonymousFunction { .. }));
        domains.insert(match &p.domain_nonempty.evidence {
            E::ParameterCarriers(_) => "carrier",
            E::ArgumentWitness { .. } => "arguments",
            E::ExistingWitness(_) => "exist",
        });
        let output = super::compile_run(&run, &c, "constant_original").unwrap();
        assert!(output.contains("Litex.fnRangeSingletonOfConstantCalls"));
        assert_eq!(
            output,
            super::compile_run(&run, &c, "constant_original").unwrap()
        );
    }
    assert_eq!(domains.len(), 3);
}

#[test]
fn constant_range_preserves_both_original_signatures_and_parameter_identities() {
    for change in ["source", "domain", "both_ids", "return", "guards"] {
        let (mut run, c) = super::execute(DOMAIN);
        let p = selected(run.statement_results.last_mut().unwrap());
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
fn constant_range_replays_carrier_groups_instead_of_inventing_parameter_witnesses() {
    for change in ["missing", "order"] {
        let (mut run, c) = super::execute(GROUPS);
        let E::ParameterCarriers(children) =
            &mut selected(run.statement_results.last_mut().unwrap())
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
fn constant_range_carrier_leaf_needs_its_subject_wd_and_exact_prior_citation() {
    for change in ["subject", "wd", "missing", "future"] {
        let (mut run, c) = super::execute(DOMAIN);
        let p = super::atomic_proof_mut(carrier_leaf(run.statement_results.last_mut().unwrap()));
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
fn constant_range_argument_witness_keeps_all_inputs_memberships_and_guards_in_order() {
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
        } = &mut selected(run.statement_results.last_mut().unwrap())
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
fn constant_range_argument_membership_retains_original_wd_and_citation() {
    for change in ["subject", "wd"] {
        let (mut run, c) = super::execute(ARGS);
        let E::ArgumentWitness { memberships, .. } =
            &mut selected(run.statement_results.last_mut().unwrap())
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
fn constant_range_integer_range_start_retains_integer_order_and_carrier_evidence() {
    for source in [CLOSED, HALF] {
        for change in ["integer", "order", "wd"] {
            let (mut run, c) = super::execute(source);
            let E::ArgumentWitness { memberships, .. } =
                &mut selected(run.statement_results.last_mut().unwrap())
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
fn constant_range_existing_witness_keeps_original_binders_guards_and_formation() {
    for change in ["binder", "carrier", "guard", "wd"] {
        let (mut run, c) = super::execute(EXIST);
        let p = existential(run.statement_results.last_mut().unwrap());
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
fn constant_range_existing_witness_cannot_replace_its_original_existential_citation() {
    let (mut run, c) = super::execute(EXIST);
    let p = existential(run.statement_results.last_mut().unwrap());
    let ExistShapedFactSearchedProof::ByKnownExistShapedFact(cite) = &mut p.searched_proof else {
        panic!("actual stored existential")
    };
    cite.cite_fact_id = FactId::new(u64::MAX);
    reject(&run, &c, "missing_existential");
}
#[test]
fn constant_range_transports_retain_the_actual_subject_path() {
    for source in [ALIAS] {
        for change in ["missing", "citation"] {
            let (mut run, c) = super::execute(source);
            let path = match &mut selected(run.statement_results.last_mut().unwrap())
                .source
                .source
            {
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
fn constant_range_does_not_borrow_a_sibling_quantifiers_private_carrier_fact() {
    // The first theorem uses constant0; the second theorem uses constant1.
    // Their carrier introductions remain private to their own quantifiers.
    let first_source = "forall graph_scope_A nonempty_set:\n    fn_range(fn(graph_scope_x graph_scope_A) R {0})={0}\n";
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

#[test]
fn constant_range_keeps_original_closed_body_and_singleton_value() {
    for change in ["body", "open"] {
        let (mut run, c) = super::execute(ALL[0]);
        let S::AnonymousFunction { function, .. } =
            &mut selected(run.statement_results.last_mut().unwrap())
                .source
                .source
        else {
            panic!()
        };
        function.equal_to = Box::new(if change == "body" {
            Obj::Literal(Literal::Number(Number::new("2".into())))
        } else {
            Obj::Identifier(IdentifierObj::from_bound_name(
                &function.body.set_bound_parameters.groups[0].params[0],
            ))
        });
        reject(&run, &c, change);
    }
}
#[test]
fn constant_range_cannot_rename_all_recorded_binders_away_from_original_literal() {
    let (mut run, c) = super::execute(ALL[0]);
    let p = selected(run.statement_results.last_mut().unwrap());
    let S::AnonymousFunction { function, .. } = &mut p.source.source else {
        panic!()
    };
    function.body.set_bound_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX);
    p.source.signature = function.body.clone();
    p.domain_nonempty.signature = function.body.clone();
    reject(&run, &c, "all_original_binders");
}
#[test]
fn constant_range_needs_original_endpoint_formation() {
    let (mut run, c) = super::execute(ALL[0]);
    let p = atom(run.statement_results.last_mut().unwrap())
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    std::mem::swap(&mut p.left, &mut p.right);
    reject(&run, &c, "endpoint_wd");
}
#[test]
fn constant_range_borrows_only_actual_domain_child_after_endpoint_wd() {
    let (mut run, _) = super::execute(DOMAIN);
    let statement = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let result = &statement.proved_then_facts[0].verify_result;
    let VerifyFactResult::Equality(eq) = result else {
        panic!()
    };
    let VerifyEqualityResult::Success(eq) = eq.as_ref() else {
        panic!()
    };
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::FnRangeOfConstantAnonymousFn(p),
    ) = &eq.searched_proof
    else {
        panic!()
    };
    let E::ParameterCarriers(children) = &p.domain_nonempty.evidence else {
        panic!()
    };
    let pos = SourcePosition::new(None, SourceOwner::Verify(result), 2);
    assert_eq!(pos.search_verify_prior(&children[0]).unwrap().before, 2);
    assert!(pos.search_verify_prior(result).is_err());
}
#[test]
fn constant_range_retains_integer_then_order_then_guard_stages() {
    let (mut run, _) = super::execute(HALF);
    let statement = super::forall_proof_mut(run.statement_results.last_mut().unwrap());
    let result = &statement.proved_then_facts[0].verify_result;
    let VerifyFactResult::Equality(eq) = result else {
        panic!()
    };
    let VerifyEqualityResult::Success(eq) = eq.as_ref() else {
        panic!()
    };
    let EqualFactSearchedProof::ByBuiltinRule(
        EqualitySearchProofByBuiltinRule::FnRangeOfConstantAnonymousFn(p),
    ) = &eq.searched_proof
    else {
        panic!()
    };
    let E::ArgumentWitness {
        memberships,
        guards,
        ..
    } = &p.domain_nonempty.evidence
    else {
        panic!()
    };
    let A::IntegerRangeStart {
        integer,
        endpoint_order,
    } = &memberships[0]
    else {
        panic!()
    };
    let pos = SourcePosition::new(None, SourceOwner::Verify(result), 2);
    assert_eq!(pos.search_verify_prior(integer).unwrap().before, 2);
    assert_eq!(pos.search_verify_prior(endpoint_order).unwrap().before, 3);
    assert_eq!(pos.search_verify_prior(&guards[0]).unwrap().before, 4);
}
#[test]
fn constant_range_does_not_claim_singletons_on_empty_effective_domains() {
    for source in [
        "fn_range(fn(x {}) R {1})={1}\n",
        "fn_range(fn(x R:x!=x) R {1})={1}\n",
    ] {
        let command =
            parse_launch_command(&["-strict".to_string(), "-e".to_string(), source.to_string()])
                .unwrap();
        let mut rt =
            Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
        assert!(!rt.run_litex_code(source).unwrap().success);
    }
}
