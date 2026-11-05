use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::finite_function::FiniteFunctionSignatureProof;
use crate::execute::execute_fact_stmt::function_domain::CompleteFunctionDomainSourceProof;
use crate::execute::execute_fact_stmt::known_tuple::KnownTupleShapeProof as Shape;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::FunctionGraphNonemptyFromDomainStrategySingleStep;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::SignatureCodomainUseProof as Use;
use crate::prelude::*;
const CART: &str = r#"# A member of a two-factor Cartesian product has a nonempty finite graph.
forall replay_fin_A,replay_fin_B set,replay_fin_p cart(replay_fin_A,replay_fin_B):
    $is_nonempty_set(replay_fin_p)
"#;
const RETURNED: &str = r#"# A Cartesian-valued function returns a nonempty finite graph.
forall replay_fin_ret_A,replay_fin_ret_B set,replay_fin_ret_f fn(replay_fin_ret_x R) cart(replay_fin_ret_A,replay_fin_ret_B),replay_fin_ret_t R:
    $is_nonempty_set(replay_fin_ret_f(replay_fin_ret_t))
"#;
const COORD: &str = r#"# A Cartesian coordinate of a returned function is a nonempty finite graph.
forall replay_fin_coord_A,replay_fin_coord_B,replay_fin_coord_C set,replay_fin_coord_f fn(replay_fin_coord_x R) cart(cart(replay_fin_coord_A,replay_fin_coord_B),replay_fin_coord_C),replay_fin_coord_t R:
    $is_nonempty_set(replay_fin_coord_f(replay_fin_coord_t)(1))
"#;
const MULTI: &str = r#"# Original simultaneous Cartesian return contracts certify a nonempty coordinate graph.
forall replay_fin_multi_A,replay_fin_multi_B,replay_fin_multi_C,replay_fin_multi_D,replay_fin_multi_E,replay_fin_multi_F set,replay_fin_multi_h set,replay_fin_multi_t R:
    replay_fin_multi_h $in fn(replay_fin_multi_x R) cart(cart(replay_fin_multi_A,replay_fin_multi_B),replay_fin_multi_C)
    replay_fin_multi_h $in fn(replay_fin_multi_y R) cart(cart(replay_fin_multi_D,replay_fin_multi_E),replay_fin_multi_F)
    =>:
        $is_nonempty_set(replay_fin_multi_h(replay_fin_multi_t)(1))
"#;
const ALL: &[&str] = &[
    r#"# A two-coordinate finite function has a nonempty graph.
$is_nonempty_set((2,3))
"#,
    CART,
    RETURNED,
    COORD,
    r#"# Repeated generic coordinates still form a nonempty finite graph.
forall replay_fin_lit_A,replay_fin_lit_B set,replay_fin_lit_x replay_fin_lit_A,replay_fin_lit_y replay_fin_lit_B:
    $is_nonempty_set(tuple(replay_fin_lit_x,replay_fin_lit_x,replay_fin_lit_y))
"#,
    MULTI,
    r#"# Equality to a literal finite function preserves graph nonemptiness.
forall replay_fin_path_p set:
    replay_fin_path_p=tuple(2,3)
    =>:
        $is_nonempty_set(replay_fin_path_p)
"#,
    r#"# An original Cartesian carrier equality certifies a nonempty finite graph.
forall replay_fin_alias_A,replay_fin_alias_B,replay_fin_alias_S set,replay_fin_alias_p replay_fin_alias_S:
    replay_fin_alias_S=cart(replay_fin_alias_A,replay_fin_alias_B)
    =>:
        $is_nonempty_set(replay_fin_alias_p)
"#,
    r#"# A four-factor Cartesian member has its complete nonempty finite graph.
forall replay_fin_dim_A,replay_fin_dim_B,replay_fin_dim_C,replay_fin_dim_D set,replay_fin_dim_p cart(replay_fin_dim_A,replay_fin_dim_B,replay_fin_dim_C,replay_fin_dim_D):
    $is_nonempty_set(replay_fin_dim_p)
"#,
    r#"# The range of a finite Cartesian function lies in the union of its coordinate carriers.
forall replay_fin_range_A,replay_fin_range_B set,replay_fin_range_p cart(replay_fin_range_A,replay_fin_range_B):
    fn_range(replay_fin_range_p) $subset union(replay_fin_range_A,replay_fin_range_B)
"#,
    r#"# An original coordinate carrier equality preserves finite graph nonemptiness.
forall replay_fin_ca_A,replay_fin_ca_B,replay_fin_ca_C,replay_fin_ca_S set,replay_fin_ca_f fn(replay_fin_ca_x R) cart(replay_fin_ca_S,replay_fin_ca_C),replay_fin_ca_t R:
    replay_fin_ca_S=cart(replay_fin_ca_A,replay_fin_ca_B)
    =>:
        $is_nonempty_set(replay_fin_ca_f(replay_fin_ca_t)(1))
"#,
    r#"# An earlier completed Cartesian call supports a later return contract in its original scope.
have replay_fin_pc_A,replay_fin_pc_B,replay_fin_pc_C,replay_fin_pc_S set
have replay_fin_pc_h fn(replay_fin_pc_x R) cart({tuple(2,3)},R)
replay_fin_pc_h(0)(1)=replay_fin_pc_h(0)(1)
forall replay_fin_pc_unused R:
    replay_fin_pc_h $in fn(replay_fin_pc_y R) cart(cart(replay_fin_pc_A,replay_fin_pc_B),replay_fin_pc_C)
    =>:
        $is_nonempty_set(replay_fin_pc_h(0)(1))
"#,
];
fn atom(statement: &mut ExecStmtResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = statement else {
        panic!("original fact")
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
        panic!("actual graph-domain strategy")
    };
    p
}
fn finite(statement: &mut ExecStmtResult) -> &mut FiniteFunctionSignatureProof {
    let CompleteFunctionDomainSourceProof::FiniteFunction(p) =
        &mut selected(statement).source.source
    else {
        panic!("actual finite source")
    };
    p
}
fn returned(
    shape: &mut Shape,
) -> &mut crate::execute::execute_fact_stmt::known_tuple::KnownFunctionCartesianTupleProof {
    match shape {
        Shape::FunctionCodomain(p) => p,
        Shape::CartesianCoordinate(p) => returned(&mut p.receiver),
        _ => panic!("original returned shape"),
    }
}
fn reject(run: &RunLitexCodeResult, c: &crate::compile_to_lean::LitexToLeanCompiler, label: &str) {
    assert!(
        super::compile_run(run, c, label).is_err(),
        "changed original evidence accepted: {label}"
    );
}
fn last(run: &mut RunLitexCodeResult) -> &mut ExecStmtResult {
    run.statement_results.last_mut().unwrap()
}

#[test]
fn finite_complete_domain_replays_all_four_original_shape_sources_and_range() {
    let mut shapes = std::collections::BTreeSet::new();
    for source in ALL {
        let (mut run, c) = super::execute(source);
        if !source.contains("fn_range(") {
            shapes.insert(match finite(last(&mut run)).source {
                Shape::CartesianMembership(_) => "membership",
                Shape::TupleEquality(_) => "tuple",
                Shape::FunctionCodomain(_) => "return",
                Shape::CartesianCoordinate(_) => "coordinate",
            });
        }
        let generated = super::compile_run(&run, &c, "finite_complete_source").unwrap();
        assert!(generated.contains("Litex.cartMemberInCompleteSignature"));
        assert_eq!(
            generated,
            super::compile_run(&run, &c, "finite_complete_source").unwrap()
        );
    }
    assert_eq!(shapes.len(), 4);
}

#[test]
fn finite_complete_domain_validates_the_original_complete_signature_after_parent_agreement() {
    for change in ["domain", "return", "parameter_count", "guard"] {
        let (mut run, c) = super::execute(CART);
        let stmt = last(&mut run);
        let guard = atom(stmt).fact.clone();
        let f = finite(stmt);
        match change {
            "domain" => {
                f.signature.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::R))
            }
            "return" => f.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C)),
            "parameter_count" => f.signature.set_bound_parameters.groups[0].params.clear(),
            _ => f
                .signature
                .dom_facts
                .push(QuantifierFreeFact::AtomicFact(guard)),
        }
        let signature = f.signature.clone();
        let graph = selected(stmt);
        graph.source.signature = signature.clone();
        graph.domain_nonempty.signature = signature;
        reject(&run, &c, change);
    }
}

#[test]
fn finite_complete_domain_rejects_disagreement_between_original_parent_and_finite_signatures() {
    for change in ["parent", "child", "parameter_identity"] {
        let (mut run, c) = super::execute(CART);
        let stmt = last(&mut run);
        if change == "parent" {
            selected(stmt).source.signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else if change == "child" {
            finite(stmt).signature.ret_set = Box::new(Obj::StandardSet(StandardSet::C));
        } else {
            finite(stmt).signature.set_bound_parameters.groups[0].params[0].id =
                IdentifierId::new(u64::MAX);
        }
        reject(&run, &c, change);
    }
}

#[test]
fn finite_complete_domain_keeps_all_factors_in_their_original_order() {
    for source in [
        CART,
        r#"# A four-factor Cartesian member has its complete nonempty finite graph.
forall replay_fin_dim_A,replay_fin_dim_B,replay_fin_dim_C,replay_fin_dim_D set,replay_fin_dim_p cart(replay_fin_dim_A,replay_fin_dim_B,replay_fin_dim_C,replay_fin_dim_D):
    $is_nonempty_set(replay_fin_dim_p)
"#,
    ] {
        for change in ["missing", "order"] {
            let (mut run, c) = super::execute(source);
            let Shape::CartesianMembership(p) = &mut finite(last(&mut run)).source else {
                panic!()
            };
            if change == "missing" {
                p.cart.args.pop();
            } else {
                p.cart.args.swap(0, 1);
            }
            reject(&run, &c, change);
        }
    }
}

#[test]
fn finite_complete_domain_needs_the_exact_visible_cartesian_membership() {
    for change in ["missing", "future", "subject", "carrier"] {
        let (mut run, c) = super::execute(CART);
        let stmt = last(&mut run);
        let future = atom(stmt).fact.fact_id();
        let Shape::CartesianMembership(p) = &mut finite(stmt).source else {
            panic!()
        };
        match change {
            "missing" => p.membership.fact_id = FactId::new(u64::MAX),
            "future" => p.membership.fact_id = future,
            "subject" => p.membership.element = Obj::StandardSet(StandardSet::R),
            _ => p.membership.set = Obj::StandardSet(StandardSet::R),
        }
        reject(&run, &c, change);
    }
}

#[test]
fn finite_complete_domain_replays_literal_tuple_transport_instead_of_dropping_the_path() {
    for change in ["path", "citation", "order", "length"] {
        let (mut run, c) = super::execute(
            r#"# Equality to a literal finite function preserves graph nonemptiness.
forall replay_fin_path_p set:
    replay_fin_path_p=tuple(2,3)
    =>:
        $is_nonempty_set(replay_fin_path_p)
"#,
        );
        let Shape::TupleEquality(p) = &mut finite(last(&mut run)).source else {
            panic!()
        };
        assert!(!p.tuple_equal.path.is_empty());
        match change {
            "path" => p.tuple_equal.path.clear(),
            "citation" => p.tuple_equal.path[0].2 = FactId::new(u64::MAX),
            "order" => p.value.args.swap(0, 1),
            _ => {
                p.value.args.pop();
            }
        }
        reject(&run, &c, change);
    }
}

#[test]
fn finite_complete_domain_requires_original_cartesian_carrier_transport() {
    for change in ["path", "citation", "endpoint"] {
        let (mut run, c) = super::execute(
            r#"# An original Cartesian carrier equality certifies a nonempty finite graph.
forall replay_fin_alias_A,replay_fin_alias_B,replay_fin_alias_S set,replay_fin_alias_p replay_fin_alias_S:
    replay_fin_alias_S=cart(replay_fin_alias_A,replay_fin_alias_B)
    =>:
        $is_nonempty_set(replay_fin_alias_p)
"#,
        );
        let Shape::CartesianMembership(p) = &mut finite(last(&mut run)).source else {
            panic!()
        };
        assert!(!p.carrier_equal.path.is_empty());
        match change {
            "path" => p.carrier_equal.path.clear(),
            "citation" => p.carrier_equal.path[0].2 = FactId::new(u64::MAX),
            _ => p.carrier_equal.path[0].1 = Obj::StandardSet(StandardSet::R),
        }
        reject(&run, &c, change);
    }
}

#[test]
fn finite_complete_domain_checks_the_actual_coordinate_index_and_parent_factor() {
    for change in ["zero", "bounds", "other_index", "parent_factors"] {
        let (mut run, c) = super::execute(COORD);
        let Shape::CartesianCoordinate(p) = &mut finite(last(&mut run)).source else {
            panic!()
        };
        match change {
            "zero" => p.index = 0,
            "bounds" => p.index = p.receiver.dimension() + 1,
            "other_index" => p.index = 2,
            _ => {
                let Shape::FunctionCodomain(parent) = p.receiver.as_mut() else {
                    panic!()
                };
                parent.cart.args.swap(0, 1);
            }
        }
        reject(&run, &c, change);
    }
}

#[test]
fn finite_complete_domain_needs_original_coordinate_carrier_equality() {
    for change in ["path", "citation"] {
        let (mut run, c) = super::execute(
            r#"# An original coordinate carrier equality preserves finite graph nonemptiness.
forall replay_fin_ca_A,replay_fin_ca_B,replay_fin_ca_C,replay_fin_ca_S set,replay_fin_ca_f fn(replay_fin_ca_x R) cart(replay_fin_ca_S,replay_fin_ca_C),replay_fin_ca_t R:
    replay_fin_ca_S=cart(replay_fin_ca_A,replay_fin_ca_B)
    =>:
        $is_nonempty_set(replay_fin_ca_f(replay_fin_ca_t)(1))
"#,
        );
        let Shape::CartesianCoordinate(p) = &mut finite(last(&mut run)).source else {
            panic!()
        };
        assert!(!p.carrier_equal.path.is_empty());
        if change == "path" {
            p.carrier_equal.path.clear();
        } else {
            p.carrier_equal.path[0].2 = FactId::new(u64::MAX);
        }
        reject(&run, &c, change);
    }
}

#[test]
fn finite_complete_domain_needs_the_exact_original_return_citation_and_all_signature_rows() {
    for source in [
        RETURNED,
        MULTI,
        r#"# An earlier completed Cartesian call supports a later return contract in its original scope.
have replay_fin_pc_A,replay_fin_pc_B,replay_fin_pc_C,replay_fin_pc_S set
have replay_fin_pc_h fn(replay_fin_pc_x R) cart({tuple(2,3)},R)
replay_fin_pc_h(0)(1)=replay_fin_pc_h(0)(1)
forall replay_fin_pc_unused R:
    replay_fin_pc_h $in fn(replay_fin_pc_y R) cart(cart(replay_fin_pc_A,replay_fin_pc_B),replay_fin_pc_C)
    =>:
        $is_nonempty_set(replay_fin_pc_h(0)(1))
"#,
    ] {
        for change in ["cite", "missing_row", "row_cite"] {
            let (mut run, c) = super::execute(source);
            let p = &mut returned(&mut finite(last(&mut run)).source).membership_proof;
            match change {
                "cite" => p.cite_property_fact_id = FactId::new(u64::MAX),
                "missing_row" => {
                    let main = p.cite_property_fact_id;
                    p.signature_uses.retain(|row| match row {
                        Use::ReturnSetMatch(row) => row.cite_signature_fact_id != main,
                        Use::SameCallDomains {
                            cite_signature_fact_id,
                            ..
                        } => *cite_signature_fact_id != main,
                    });
                }
                _ => match &mut p.signature_uses[0] {
                    Use::ReturnSetMatch(p) => p.cite_signature_fact_id = FactId::new(u64::MAX),
                    Use::SameCallDomains {
                        cite_signature_fact_id,
                        ..
                    } => *cite_signature_fact_id = FactId::new(u64::MAX),
                },
            }
            reject(&run, &c, change);
        }
    }
}

#[test]
fn finite_complete_domain_checks_original_alternative_signature_domain_layers() {
    for source in [
        MULTI,
        r#"# An earlier completed Cartesian call supports a later return contract in its original scope.
have replay_fin_pc_A,replay_fin_pc_B,replay_fin_pc_C,replay_fin_pc_S set
have replay_fin_pc_h fn(replay_fin_pc_x R) cart({tuple(2,3)},R)
replay_fin_pc_h(0)(1)=replay_fin_pc_h(0)(1)
forall replay_fin_pc_unused R:
    replay_fin_pc_h $in fn(replay_fin_pc_y R) cart(cart(replay_fin_pc_A,replay_fin_pc_B),replay_fin_pc_C)
    =>:
        $is_nonempty_set(replay_fin_pc_h(0)(1))
"#,
    ] {
        for change in ["missing_layer", "signature"] {
            let (mut run, c) = super::execute(source);
            let p = &mut returned(&mut finite(last(&mut run)).source).membership_proof;
            let domains = p
                .signature_uses
                .iter_mut()
                .find_map(|row| match row {
                    Use::SameCallDomains { domains, .. } => Some(domains),
                    _ => None,
                })
                .expect("actual same-domain row");
            assert_eq!(domains.layers.len(), 1);
            if change == "missing_layer" {
                domains.layers.clear();
            } else {
                domains.layers[0].alternative.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::C));
            }
            reject(&run, &c, change);
        }
    }
}

fn full_call_mut(statement: &mut ExecStmtResult) -> &mut crate::execute::execute_fact_stmt::well_defined_results::verify_obj::FnObjObjWellDefinedProof{
    let atomic = atom(statement);
    let wd = &mut atomic
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter[0];
    let DetailedObjWellDefinedProof::ByDef {
        proof: ObjWellDefinedProofByDef::FnObj(p),
        ..
    } = wd.as_detailed_mut().unwrap()
    else {
        panic!("original complete call WD")
    };
    p
}

#[test]
fn checked_call_prefix_requires_the_whole_original_constructor_including_its_tail() {
    for change in ["argument", "requirement", "tail_subject"] {
        let (mut run, c) = super::execute(COORD);
        let p = full_call_mut(last(&mut run));
        match change {
            "argument" => {
                p.child_obj_well_defined.pop();
            }
            "requirement" => {
                p.requirement_fact_verified.pop();
            }
            _ => {
                let child = p.child_obj_well_defined.last_mut().unwrap();
                match child.as_detailed_mut().unwrap() {
                    DetailedObjWellDefinedProof::ByDef { obj, .. } => {
                        *obj = Obj::StandardSet(StandardSet::R)
                    }
                    DetailedObjWellDefinedProof::ByKnown { wd_id, .. } => {
                        *wd_id = WellDefinednessId::new(u64::MAX)
                    }
                }
            }
        }
        reject(&run, &c, change);
    }
}

#[test]
fn checked_call_prefix_obeys_original_completion_and_closed_forall_scope() {
    let (run, _) = super::execute(COORD);
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &run.statement_results[0]
    else {
        panic!()
    };
    let VerifyFactResult::ForallFact(result) = &statement.verify_result else {
        panic!()
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
        result.as_ref()
    else {
        panic!()
    };
    let VerifyFactResult::AtomicExceptEquality(result) = &p.proved_then_facts[0].verify_result
    else {
        panic!()
    };
    let VerifyAtomicExceptEqualityFactResult::Success(atomic) = result.as_ref() else {
        panic!()
    };
    let wd = &atomic
        .well_defined_proof
        .as_detailed()
        .unwrap()
        .well_defined_of_each_parameter[0];
    let Obj::FnObj(whole) = wd.obj() else {
        panic!()
    };
    let mut prefix = whole.clone();
    prefix.body.pop();
    let prefix = Obj::FnObj(prefix);
    let root = SourcePosition::new(None, SourceOwner::Run(&run), 0);
    let head = p
        .fact
        .typed_parameters
        .groups
        .iter()
        .map(|g| g.params.len())
        .sum::<usize>()
        + p.assumed_dom_facts.len();
    let header = SourcePosition::new(Some(&root), SourceOwner::Forall(p), head);
    let direct = SourcePosition::new(Some(&header), SourceOwner::AtomicVerify(atomic), 0);
    assert!(direct
        .with_visible_call_prefix(&prefix, &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
    let completed = direct.atomic_search_prior(0).unwrap();
    assert!(completed
        .with_visible_call_prefix(&prefix, &mut |original, _| {
            assert!(std::ptr::eq(original, wd));
            Ok(())
        })
        .unwrap()
        .is_some());
    let outside = SourcePosition::new(None, SourceOwner::Run(&run), 1);
    assert!(outside
        .with_visible_call_prefix(&prefix, &mut |_, _| Ok(()))
        .unwrap()
        .is_none());
    assert!(
        completed
            .with_visible_call_prefix(wd.obj(), &mut |_, _| Ok(()))
            .unwrap()
            .is_none(),
        "exact calls are not proper prefixes"
    );
}

#[test]
fn finite_complete_domain_rejects_duplicate_original_return_rows() {
    let (mut run, c) = super::execute(MULTI);
    let p = &mut returned(&mut finite(last(&mut run)).source).membership_proof;
    let main = p.cite_property_fact_id;
    let duplicate = p
        .signature_uses
        .iter_mut()
        .find_map(|row| match row {
            Use::SameCallDomains {
                cite_signature_fact_id,
                ..
            } => Some(cite_signature_fact_id),
            _ => None,
        })
        .expect("actual distinct alternative row");
    assert_ne!(*duplicate, main);
    *duplicate = main;
    reject(&run, &c, "duplicate_return_row");
}
