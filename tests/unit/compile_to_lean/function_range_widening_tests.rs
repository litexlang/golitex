use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof as Source;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::subset::{FunctionRangeCodomainContainment as Containment, FunctionRangeInCodomainProof, SubsetFactSearchProofByBuiltinRule as SubsetRule};
use crate::prelude::*;

const GENERAL: &str = include_str!("../../../lean/examples/function_range_widening/statement.lit");
macro_rules! source {
    ($s:literal) => {
        include_str!(concat!(
            "../../../lean/examples/function_range_widening_",
            $s,
            "/statement.lit"
        ))
    };
}
const ALL: &[&str] = &[
    GENERAL,
    source!("finite"),
    source!("returned"),
    source!("anonymous"),
    source!("composition"),
    source!("matrix"),
    source!("selector"),
    source!("union"),
    source!("carrier_alias"),
    source!("guard"),
    source!("binary_guard"),
    source!("function_alias"),
    source!("named"),
    source!("native_matrix"),
];
const EXACT: &str =
    include_str!("../../../lean/examples/finite_function_graph_range/statement.lit");

fn atom(statement: &mut ExecStmtResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = statement else {
        panic!("original fact")
    };
    let proof = match &mut p.verify_result {
        VerifyFactResult::ForallFact(p) => {
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                p.as_mut()
            else {
                panic!("original local forall")
            };
            &mut p.proved_then_facts.last_mut().unwrap().verify_result
        }
        p => p,
    };
    super::atomic_proof_mut(proof)
}
fn selected(statement: &mut ExecStmtResult) -> &mut FunctionRangeInCodomainProof {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(
            SubsetRule::FunctionRangeInCodomain(p),
        ),
    ) = &mut atom(statement).searched_proof
    else {
        panic!("actual original range-codomain rule")
    };
    p
}
fn child(statement: &mut ExecStmtResult) -> &mut VerifyFactResult {
    let Containment::Subset(p) = &mut selected(statement).containment else {
        panic!("actual original subset child")
    };
    p
}
fn last(run: &mut RunLitexCodeResult) -> &mut ExecStmtResult {
    run.statement_results.last_mut().unwrap()
}
fn reject(run: &RunLitexCodeResult, c: &crate::compile_to_lean::LitexToLeanCompiler, label: &str) {
    assert!(
        super::compile_run(run, c, label).is_err(),
        "altered original range evidence accepted:{label}"
    );
}

#[test]
fn range_widening_replays_seven_actual_complete_source_variants_and_original_children() {
    let mut sources = std::collections::BTreeSet::new();
    for source in ALL {
        let (mut run, c) = super::execute(source);
        let p = selected(last(&mut run));
        sources.insert(match p.source.source {
            Source::Membership { .. } => "membership",
            Source::FiniteFunction(_) => "finite",
            Source::AnonymousFunction { .. } => "anonymous",
            Source::Composition(_) => "composition",
            Source::Matrix(_) => "matrix",
            Source::ApplicationReturn { .. } => "returned",
            Source::MultivariableSelector(_) => "selector",
            _ => panic!("unprofiled source"),
        });
        assert!(matches!(p.containment, Containment::Subset(_)));
        let text = super::compile_run(&run, &c, "range_widening_original").unwrap();
        assert!(text.contains("have _codomain_subset : Litex.Subset"));
        assert_eq!(
            text,
            super::compile_run(&run, &c, "range_widening_original").unwrap()
        );
    }
    assert_eq!(
        sources.len(),
        7,
        "source syntax alone does not count a selected evidence variant"
    );
}

#[test]
fn range_widening_validates_both_original_child_endpoints() {
    for side in ["left", "right"] {
        let (mut run, c) = super::execute(GENERAL);
        let AtomicFact::SubsetFact(p) = &mut super::atomic_proof_mut(child(last(&mut run))).fact
        else {
            panic!()
        };
        if side == "left" {
            p.left = Obj::StandardSet(StandardSet::R)
        } else {
            p.right = Obj::StandardSet(StandardSet::C)
        };
        reject(&run, &c, side);
    }
}

#[test]
fn range_widening_keeps_original_child_formation_and_matching_evidence() {
    for change in ["wd", "matching"] {
        let (mut run, c) = super::execute(GENERAL);
        let p = super::atomic_proof_mut(child(last(&mut run)));
        if change == "wd" {
            p.well_defined_proof
                .as_detailed_mut()
                .unwrap()
                .well_defined_of_each_parameter
                .pop();
        } else {
            let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) = &mut p.searched_proof
            else {
                panic!()
            };
            p.why_parameters_of_known_fact_are_equal_to_givens.pop();
        }
        reject(&run, &c, change);
    }
}

#[test]
fn range_widening_needs_the_exact_prior_citation_of_its_original_child() {
    for kind in ["missing", "future"] {
        let (mut run, c) = super::execute(GENERAL);
        let stmt = last(&mut run);
        let future = atom(stmt).fact.fact_id();
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
            &mut super::atomic_proof_mut(child(stmt)).searched_proof
        else {
            panic!()
        };
        p.cite_fact_id = if kind == "future" {
            future
        } else {
            FactId::new(u64::MAX)
        };
        reject(&run, &c, kind);
    }
}

#[test]
fn range_widening_keeps_the_original_child_predicate_domain_citation() {
    let (mut run, c) = super::execute(GENERAL);
    let p = super::atomic_proof_mut(child(last(&mut run)))
        .well_defined_proof
        .as_detailed_mut()
        .unwrap();
    let PredicateDomainProof::ByKnownFact(p) = &mut p.predicate_domain else {
        panic!("actual known predicate-domain citation")
    };
    p.cite_fact_id = FactId::new(u64::MAX);
    reject(&run, &c, "child_predicate_domain");
}

#[test]
fn range_widening_keeps_parent_range_formation_before_truth() {
    let (mut run, c) = super::execute(GENERAL);
    atom(last(&mut run))
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter
        .remove(0);
    reject(&run, &c, "parent_range_wd");
}

#[test]
fn range_widening_preserves_the_original_complete_source_signature_and_membership() {
    for change in ["signature", "citation", "subject"] {
        let (mut run, c) = super::execute(GENERAL);
        let p = selected(last(&mut run));
        if change == "signature" {
            p.source.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            let Source::Membership { membership, .. } = &mut p.source.source else {
                panic!()
            };
            if change == "citation" {
                membership.fact_id = FactId::new(u64::MAX);
            } else {
                membership.element = Obj::StandardSet(StandardSet::R);
            }
        }
        reject(&run, &c, change);
    }
}

#[test]
fn range_widening_replays_original_carrier_alias_argument_paths() {
    for change in ["citation", "endpoint", "missing"] {
        let (mut run, c) = super::execute(source!("carrier_alias"));
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
            &mut super::atomic_proof_mut(child(last(&mut run))).searched_proof
        else {
            panic!()
        };
        let path = p
            .why_parameters_of_known_fact_are_equal_to_givens
            .iter_mut()
            .find_map(|eq| match eq {
                EqualFactSearchedProof::ByEquivalenceClass(
                    EqualFactSearchedProofByEquivalenceClass::KnownPath(p),
                ) if !p.path.is_empty() => Some(p),
                _ => None,
            })
            .expect("actual carrier equality argument path");
        match change {
            "citation" => path.path[0].2 = FactId::new(u64::MAX),
            "endpoint" => path.path[0].1 = Obj::StandardSet(StandardSet::R),
            _ => path.path.clear(),
        }
        reject(&run, &c, change);
    }
}

#[test]
fn range_widening_named_source_keeps_the_actual_function_equality_path() {
    for change in ["path", "citation"] {
        let (mut run, c) = super::execute(source!("named"));
        let Source::AnonymousFunction { subject_equal, .. } =
            &mut selected(last(&mut run)).source.source
        else {
            panic!()
        };
        assert!(!subject_equal.path.is_empty());
        if change == "path" {
            subject_equal.path.clear();
        } else {
            subject_equal.path[0].2 = FactId::new(u64::MAX);
        }
        reject(&run, &c, change);
    }
}

#[test]
fn range_widening_returned_source_keeps_all_original_application_stages() {
    for change in ["argument", "requirement"] {
        let (mut run, c) = super::execute(source!("returned"));
        let Source::ApplicationReturn {
            application_check, ..
        } = &mut selected(last(&mut run)).source.source
        else {
            panic!()
        };
        let p = application_check.as_detailed_mut().unwrap();
        if change == "argument" {
            p.child_obj_well_defined.pop();
        } else {
            p.requirement_fact_verified.pop();
        }
        reject(&run, &c, change);
    }
}

#[test]
fn range_widening_retains_selector_subject_and_original_wd_identity() {
    for change in ["subject", "wd"] {
        let (mut run, c) = super::execute(source!("selector"));
        let Source::MultivariableSelector(p) = &mut selected(last(&mut run)).source.source else {
            panic!()
        };
        if change == "subject" {
            p.selector = Obj::StandardSet(StandardSet::R);
        } else {
            let DetailedObjWellDefinedProof::ByKnown { wd_id, .. } =
                p.well_defined.as_detailed_mut().unwrap()
            else {
                panic!("original reused selector WD")
            };
            *wd_id = WellDefinednessId::new(u64::MAX);
        }
        reject(&run, &c, change);
    }
}

#[test]
fn range_widening_keeps_the_original_ordered_finite_return_domain() {
    let (mut run, c) = super::execute(source!("finite"));
    let stmt = last(&mut run);
    let p = selected(stmt);
    p.source.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
    let Source::FiniteFunction(finite) = &mut p.source.source else {
        panic!()
    };
    finite.signature.ret_set = p.source.signature.ret_set.clone();
    let AtomicFact::SubsetFact(p) = &mut super::atomic_proof_mut(child(stmt)).fact else {
        panic!()
    };
    p.left = Obj::StandardSet(StandardSet::C);
    reject(&run, &c, "changed_ordered_finite_return");
}

#[test]
fn range_widening_and_exact_containment_do_not_replace_each_others_selected_route() {
    let (mut widened, wc) = super::execute(GENERAL);
    let (mut exact, ec) = super::execute(EXACT);
    assert!(matches!(
        selected(last(&mut widened)).containment,
        Containment::Subset(_)
    ));
    assert!(matches!(
        selected(last(&mut exact)).containment,
        Containment::Exact(_)
    ));
    let old = super::compile_run(&exact, &ec, "exact_range").unwrap();
    assert!(!old.contains("have _codomain_subset"));
    std::mem::swap(
        &mut selected(last(&mut widened)).containment,
        &mut selected(last(&mut exact)).containment,
    );
    reject(&widened, &wc, "wrong_exact_route");
    reject(&exact, &ec, "wrong_widened_route");
}

#[test]
fn range_widening_child_cannot_borrow_a_sibling_foralls_private_subset() {
    let source="forall sibling_B,sibling_C set,sibling_f fn(sibling_x N) sibling_B:\n    sibling_B $subset sibling_C\n    =>:\n        fn_range(sibling_f) $subset sibling_C\nforall current_A,current_B,current_C set,current_f fn(current_x current_A) current_B:\n    current_B $subset current_C\n    =>:\n        fn_range(current_f) $subset current_C\n";
    let (mut run, c) = super::execute(source);
    let private = super::forall_proof_mut(&mut run.statement_results[0])
        .fact
        .dom_facts[0]
        .fact_id();
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(p) =
        &mut super::atomic_proof_mut(child(&mut run.statement_results[1])).searched_proof
    else {
        panic!()
    };
    p.cite_fact_id = private;
    reject(&run, &c, "sibling_subset");
}

#[test]
fn range_widening_original_child_cursor_follows_all_complete_source_stages() {
    let (mut run, _) = super::execute(source!("returned"));
    let atomic = atom(last(&mut run));
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact(
            SubsetRule::FunctionRangeInCodomain(p),
        ),
    ) = &atomic.searched_proof
    else {
        panic!()
    };
    let Source::ApplicationReturn {
        application_check, ..
    } = &p.source.source
    else {
        panic!()
    };
    let original = application_check.detailed_ref();
    let Containment::Subset(original_child) = &p.containment else {
        panic!()
    };
    let current = SourcePosition::new(None, SourceOwner::AtomicVerify(atomic), 0);
    let formation = current.atomic_search_prior(0).unwrap();
    let prior = current.atomic_search_verify_prior(original_child).unwrap();
    assert_eq!(
        prior.before,
        formation.before
            + original.child_obj_well_defined.len()
            + original.requirement_fact_verified.len()
    );
    let (mut foreign, _) = super::execute(GENERAL);
    let foreign = child(last(&mut foreign));
    assert!(
        current.atomic_search_verify_prior(foreign).is_err(),
        "another run is not an original owned child"
    );
}
