use crate::execute::execute_fact_stmt::function_domain::{
    FunctionDomainEmptyCarrierEvidence as E, FunctionDomainEmptyProof as D,
    FunctionSpaceNonemptyProof as P,
};
use crate::prelude::*;
const GENERIC: &str = r#"# A nonempty codomain supplies a constant function on any domain.
forall replay_space_domain set, replay_space_codomain nonempty_set:
    $is_nonempty_set(fn(replay_space_arg replay_space_domain) replay_space_codomain)
"#;
const GUARDED: &str = r#"# A constant function exists on the guarded domain when the codomain is nonempty.
forall replay_ne_guard_A set, replay_ne_guard_B nonempty_set:
    $is_nonempty_set(fn(replay_ne_guard_x replay_ne_guard_A: replay_ne_guard_x=replay_ne_guard_x) replay_ne_guard_B)
"#;
const NESTED: &str = r#"# Nonempty codomains give nonempty nested function spaces.
forall replay_ne_nested_A set, replay_ne_nested_B nonempty_set:
    $is_nonempty_set(fn(replay_ne_nested_x replay_ne_nested_A) fn(replay_ne_nested_y replay_ne_nested_A) replay_ne_nested_B)
"#;
const CART: &str = r#"# A function space with a product of nonempty codomain factors is nonempty.
forall replay_ne_cart_A set, replay_ne_cart_B,replay_ne_cart_C nonempty_set:
    $is_nonempty_set(fn(replay_ne_cart_x replay_ne_cart_A) cart(replay_ne_cart_B,replay_ne_cart_C))
"#;
const TRANSPORT: &str = r#"# A carrier equal to a nonempty function space is a valid nonempty codomain.
forall replay_ne_path_A,replay_ne_path_B set, replay_ne_path_C nonempty_set:
    replay_ne_path_B = fn(replay_ne_path_y replay_ne_path_A) replay_ne_path_C
    =>:
        $is_nonempty_set(fn(replay_ne_path_x replay_ne_path_A) replay_ne_path_B)
"#;
const NESTED_EMPTY: &str = r#"# An empty-domain function space can serve as a nonempty codomain.
forall replay_ne_void_A set:
    $is_nonempty_set(fn(replay_ne_void_x replay_ne_void_A) fn(replay_ne_void_y {}) {})
"#;
const EMPTY: &str = r#"# A function from the empty set to the empty set exists.
$is_nonempty_set(fn(replay_ne_empty_x {}) {})
"#;
const ALIAS: &str = r#"# A parameter carrier equal to the empty set gives an empty complete domain.
forall replay_ne_alias_A set:
    replay_ne_alias_A = {}
    =>:
        $is_nonempty_set(fn(replay_ne_alias_x replay_ne_alias_A) {})
"#;
const CHECKED: &str = r#"# An empty parameter carrier permits a function with an empty codomain.
forall replay_ne_checked_A set:
    not $is_nonempty_set(replay_ne_checked_A)
    =>:
        $is_nonempty_set(fn(replay_ne_checked_x replay_ne_checked_A) {})
"#;
const GUARDS: &str = r#"# Incompatible input guards permit the empty function into an empty carrier.
$is_nonempty_set(fn(replay_ne_other_x R: replay_ne_other_x=replay_ne_other_x, replay_ne_other_x!=replay_ne_other_x) {})
"#;
const SEQUENCES: &str = r#"# Finite and infinite sequences exist over every nonempty carrier.
forall replay_ne_seq_B nonempty_set, replay_ne_seq_n N:
    $is_nonempty_set(finite_seq(replay_ne_seq_B,replay_ne_seq_n))
    $is_nonempty_set(seq(replay_ne_seq_B))
"#;
const SCOPES: &str = r#"# Independent quantified sequence and function spaces have their own nonempty carriers.
forall replay_ne_scope_B nonempty_set:
    $is_nonempty_set(seq(replay_ne_scope_B))

forall replay_space_domain set, replay_space_codomain nonempty_set:
    $is_nonempty_set(fn(replay_space_arg replay_space_domain) replay_space_codomain)
"#;
const CHAIN: &str = r#"# Transitive carrier equalities give a nonempty codomain after the equality is proved.
forall replay_ne_chain_A,replay_ne_chain_B,replay_ne_chain_D set,replay_ne_chain_C nonempty_set:
    replay_ne_chain_B = replay_ne_chain_D
    replay_ne_chain_D = fn(replay_ne_chain_y replay_ne_chain_A) replay_ne_chain_C
    =>:
        replay_ne_chain_B = fn(replay_ne_chain_y replay_ne_chain_A) replay_ne_chain_C
        $is_nonempty_set(fn(replay_ne_chain_x replay_ne_chain_A) replay_ne_chain_B)
"#;
const ALL: &[&str] = &[
    GENERIC,
    GUARDED,
    NESTED,
    CART,
    TRANSPORT,
    NESTED_EMPTY,
    EMPTY,
    ALIAS,
    CHECKED,
    GUARDS,
    SEQUENCES,
    SCOPES,
    CHAIN,
    r#"# Empty half-open and closed integer ranges permit functions into the empty set.
$is_nonempty_set(fn(replay_ne_range_x range(2,2)) {})
$is_nonempty_set(fn(replay_ne_range_y closed_range(2,1)) {})
"#,
    r#"# An impossible input guard permits a function with empty output carrier.
$is_nonempty_set(fn(replay_ne_excluded_x R: replay_ne_excluded_x!=replay_ne_excluded_x) {})
"#,
    r#"# The empty finite sequence exists over an empty carrier.
$is_nonempty_set(finite_seq({},0))
"#,
    r#"# A matrix with zero rows and two columns exists over the empty entry carrier.
$is_nonempty_set(matrix({},0,2))
"#,
    r#"# A nonempty sequence space can serve as a function codomain.
forall replay_ne_ns_A set,replay_ne_ns_B nonempty_set:
    $is_nonempty_set(fn(replay_ne_ns_x replay_ne_ns_A) seq(replay_ne_ns_B))
"#,
    r#"# A strictly self-greater input guard gives an empty complete domain.
$is_nonempty_set(fn(replay_ne_positive_exclusion_x R: replay_ne_positive_exclusion_x>replay_ne_positive_exclusion_x) R)
"#,
    r#"# An impossible guard on positive real inputs leaves a nonempty function space.
$is_nonempty_set(fn(replay_ne_positive_x R+: replay_ne_positive_x!=replay_ne_positive_x) R)
"#,
    r#"# Unary, binary and ternary real function spaces are nonempty.
$is_nonempty_set(fn(replay_ne_std_x R) R)
$is_nonempty_set(fn(replay_ne_std_x, replay_ne_std_y R) R)
$is_nonempty_set(fn(replay_ne_std_x, replay_ne_std_y, replay_ne_std_z R) R)
"#,
    r#"# One empty parameter carrier makes a ternary complete domain empty.
$is_nonempty_set(fn(replay_ne_three_x R,replay_ne_three_y {},replay_ne_three_z R) {})
"#,
    r#"# Nonempty sequence, matrix and function spaces form a nonempty product codomain.
forall replay_ne_mix_A set,replay_ne_mix_B nonempty_set,replay_ne_mix_m,replay_ne_mix_n N:
    $is_nonempty_set(fn(replay_ne_mix_x replay_ne_mix_A) cart(replay_ne_mix_B,seq(replay_ne_mix_B),finite_seq(replay_ne_mix_B,replay_ne_mix_n),matrix(replay_ne_mix_B,replay_ne_mix_m,replay_ne_mix_n)))
"#,
    r#"# Nonempty sequence, matrix and function spaces form a nonempty product codomain.
forall replay_ne_mix_empty_A set:
    $is_nonempty_set(fn(replay_ne_mix_empty_x replay_ne_mix_empty_A) cart(fn(replay_ne_mix_empty_y {}) {},finite_seq({},0),matrix({},0,2)))
"#,
];

fn atom(
    statement: &mut ExecStmtResult,
    index: usize,
) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(p)) = statement else {
        panic!("original fact statement")
    };
    let proof = match &mut p.verify_result {
        VerifyFactResult::ForallFact(result) => {
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(p)) =
                result.as_mut()
            else {
                panic!("local forall")
            };
            &mut p.proved_then_facts[index].verify_result
        }
        proof => {
            assert_eq!(index, 0);
            proof
        }
    };
    super::atomic_proof_mut(proof)
}
fn strategy(
    statement: &mut ExecStmtResult,
    index: usize,
) -> &mut AtomicExceptEqualityFactSearchProofByBuiltinStrategy {
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(p) =
        &mut atom(statement, index).searched_proof
    else {
        panic!("actual selected builtin strategy")
    };
    p
}
fn nonempty(p: &mut AtomicExceptEqualityFactSearchProofByBuiltinStrategy) -> &mut P {
    use AtomicExceptEqualityFactSearchProofByBuiltinStrategy as S;
    match p {
        S::FnSetNonemptyFromCodomain(p) => &mut p.codomain_nonempty,
        S::FiniteSeqSetNonemptyFromCodomain(p) => &mut p.codomain_nonempty,
        S::SeqSetNonemptyFromCodomain(p) => &mut p.codomain_nonempty,
        _ => panic!("actual codomain certificate"),
    }
}
fn signature(p: &mut AtomicExceptEqualityFactSearchProofByBuiltinStrategy) -> &mut FnSet {
    use AtomicExceptEqualityFactSearchProofByBuiltinStrategy as S;
    match p {
        S::FnSetNonemptyFromCodomain(p) => &mut p.signature,
        S::FiniteSeqSetNonemptyFromCodomain(p) => &mut p.signature,
        S::SeqSetNonemptyFromCodomain(p) => &mut p.signature,
        _ => panic!(),
    }
}
fn empty(p: &mut AtomicExceptEqualityFactSearchProofByBuiltinStrategy) -> &mut D {
    let AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FunctionSpaceNonemptyFromEmptyDomain(
        p,
    ) = p
    else {
        panic!("actual empty-domain certificate")
    };
    &mut p.domain_empty
}
fn leaf(p: &mut P) -> &mut VerifyFactResult {
    match p {
        P::BaseSet(p) => p,
        P::CarrierTransport { nonempty, .. } => leaf(nonempty),
        P::ConstantFunction {
            return_nonempty, ..
        } => leaf(return_nonempty),
        P::FiniteCartesianProduct {
            factors_nonempty, ..
        } => leaf(&mut factors_nonempty[0]),
        P::EmptyDomain(_) => panic!("expected original base-set leaf"),
    }
}
fn variants(p: &P, out: &mut std::collections::BTreeSet<&'static str>) {
    match p {
        P::BaseSet(_) => {
            out.insert("base");
        }
        P::EmptyDomain(_) => {
            out.insert("empty");
        }
        P::CarrierTransport { nonempty, .. } => {
            out.insert("transport");
            variants(nonempty, out);
        }
        P::ConstantFunction {
            return_nonempty, ..
        } => {
            out.insert("constant");
            variants(return_nonempty, out);
        }
        P::FiniteCartesianProduct {
            factors_nonempty, ..
        } => {
            out.insert("cartesian");
            for p in factors_nonempty {
                variants(p, out);
            }
        }
    }
}

#[test]
fn nonempty_replays_four_distinct_strategies_and_five_recursive_certificate_variants() {
    for source in ALL {
        let (run, compiler) = super::execute(source);
        let output = super::compile_run(&run, &compiler, "original_nonempty").unwrap();
        assert_eq!(
            output,
            super::compile_run(&run, &compiler, "original_nonempty").unwrap()
        );
    }
    let mut seen = std::collections::BTreeSet::new();
    for source in [GENERIC, NESTED, CART, TRANSPORT, NESTED_EMPTY] {
        let (mut run, _) = super::execute(source);
        variants(
            nonempty(strategy(&mut run.statement_results[0], 0)),
            &mut seen,
        );
    }
    assert_eq!(
        seen,
        std::collections::BTreeSet::from(["base", "cartesian", "constant", "empty", "transport"])
    );
    let (mut run, _) = super::execute(SEQUENCES);
    assert!(matches!(
        strategy(&mut run.statement_results[0], 0),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::FiniteSeqSetNonemptyFromCodomain(_)
    ));
    assert!(matches!(
        strategy(&mut run.statement_results[0], 1),
        AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SeqSetNonemptyFromCodomain(_)
    ));
}

#[test]
fn nonempty_preserves_original_signature_ids_domains_guards_and_return_carriers() {
    for change in ["id", "parameter", "domain", "return", "guards"] {
        let source = if change == "guards" { GUARDED } else { GENERIC };
        let (mut run, compiler) = super::execute(source);
        let p = signature(strategy(&mut run.statement_results[0], 0));
        match change {
            "id" => p.set_bound_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX),
            "parameter" => p.set_bound_parameters.groups[0].params.clear(),
            "domain" => {
                p.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::R))
            }
            "return" => p.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
            "guards" => p.dom_facts.clear(),
            _ => unreachable!(),
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn nonempty_does_not_exchange_function_and_sequence_strategy_contracts() {
    for index in 0..2 {
        let (mut run, compiler) = super::execute(GENERIC);
        let (mut other, _) = super::execute(SEQUENCES);
        std::mem::swap(
            &mut atom(&mut run.statement_results[0], 0).searched_proof,
            &mut atom(&mut other.statement_results[0], index).searched_proof,
        );
        let error = super::compile_run(&run, &compiler, "wrong_original_strategy").unwrap_err();
        assert!(error.route.contains("SelectedStrategyCarrier"), "{error}");
    }
}

#[test]
fn nonempty_base_leaf_requires_original_subject_wd_and_preceding_citation() {
    for change in ["subject", "wd", "missing_citation", "self_citation"] {
        let (mut run, compiler) = super::execute(GENERIC);
        let p = super::atomic_proof_mut(leaf(nonempty(strategy(&mut run.statement_results[0], 0))));
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
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(c) =
                    &mut p.searched_proof
                else {
                    panic!("original nonempty parameter citation")
                };
                c.cite_fact_id = if change == "self_citation" {
                    p.fact.fact_id()
                } else {
                    FactId::new(u64::MAX)
                };
            }
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn nonempty_cartesian_replays_all_factors_in_the_original_order() {
    for change in ["missing", "proof_order", "factor_order"] {
        let (mut run, compiler) = super::execute(CART);
        let P::FiniteCartesianProduct {
            cart,
            factors_nonempty,
        } = nonempty(strategy(&mut run.statement_results[0], 0))
        else {
            panic!("original Cartesian return proof")
        };
        match change {
            "missing" => {
                factors_nonempty.pop();
            }
            "proof_order" => factors_nonempty.swap(0, 1),
            _ => cart.args.swap(0, 1),
        };
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn nonempty_nested_constant_preserves_its_original_signature_and_return_proof() {
    for change in ["domain", "return", "parameter"] {
        let (mut run, compiler) = super::execute(NESTED);
        let P::ConstantFunction { signature, .. } =
            nonempty(strategy(&mut run.statement_results[0], 0))
        else {
            panic!("original nested constant function")
        };
        match change {
            "domain" => {
                signature.set_bound_parameters.groups[0].param_type =
                    Box::new(Obj::StandardSet(StandardSet::R))
            }
            "return" => signature.ret_set = Box::new(Obj::StandardSet(StandardSet::R)),
            _ => signature.set_bound_parameters.groups[0].params.clear(),
        };
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn nonempty_transport_requires_the_original_carrier_and_equality_citations() {
    for change in ["missing", "citation", "carrier"] {
        let (mut run, compiler) = super::execute(TRANSPORT);
        let P::CarrierTransport {
            carrier,
            carrier_equal,
            ..
        } = nonempty(strategy(&mut run.statement_results[0], 0))
        else {
            panic!("original carrier transport")
        };
        assert!(!carrier_equal.path.is_empty());
        match change {
            "missing" => carrier_equal.path.clear(),
            "citation" => carrier_equal.path[0].2 = FactId::new(u64::MAX),
            _ => *carrier = Obj::StandardSet(StandardSet::R),
        };
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn nonempty_empty_carrier_retains_the_group_identity_path_and_selected_evidence() {
    for source in [
        EMPTY,
        ALIAS,
        r#"# Empty half-open and closed integer ranges permit functions into the empty set.
$is_nonempty_set(fn(replay_ne_range_x range(2,2)) {})
$is_nonempty_set(fn(replay_ne_range_y closed_range(2,1)) {})
"#,
        r#"# The empty finite sequence exists over an empty carrier.
$is_nonempty_set(finite_seq({},0))
"#,
        r#"# A matrix with zero rows and two columns exists over the empty entry carrier.
$is_nonempty_set(matrix({},0,2))
"#,
    ] {
        for change in ["group", "carrier", "evidence"] {
            let (mut run, compiler) = super::execute(source);
            let D::ParameterCarrier(p) = empty(strategy(&mut run.statement_results[0], 0)) else {
                panic!("original empty carrier")
            };
            match change {
                "group" => p.parameter_group_index = usize::MAX,
                "carrier" => p.empty_carrier = Obj::StandardSet(StandardSet::R),
                _ => {
                    p.evidence = if matches!(p.evidence, E::EmptyList) {
                        E::EmptyIntegerRange
                    } else {
                        E::EmptyList
                    }
                }
            }
            assert!(super::compile_run(&run, &compiler, change).is_err());
        }
    }
    let (mut run, compiler) = super::execute(ALIAS);
    let D::ParameterCarrier(p) = empty(strategy(&mut run.statement_results[0], 0)) else {
        panic!()
    };
    assert!(!p.carrier_equal.path.is_empty());
    p.carrier_equal.path[0].2 = FactId::new(u64::MAX);
    assert!(super::compile_run(&run, &compiler, "missing_empty_carrier_path").is_err());
}

#[test]
fn nonempty_checked_empty_replays_the_original_equality_and_nonempty_condition() {
    for change in ["subject", "condition", "select_literal"] {
        let (mut run, compiler) = super::execute(CHECKED);
        let D::ParameterCarrier(p) = empty(strategy(&mut run.statement_results[0], 0)) else {
            panic!()
        };
        if change == "select_literal" {
            p.evidence = E::EmptyList;
        } else {
            let E::CheckedEquality(child) = &mut p.evidence else {
                panic!("actual checked empty equality")
            };
            let eq = super::equality_proof_mut(child);
            if change == "subject" {
                eq.fact.right = super::number_object("0");
            } else {
                let EqualFactSearchedProof::ByBuiltinRule(
                    EqualitySearchProofByBuiltinRule::EmptySetFromNotNonempty(p),
                ) = &mut eq.searched_proof
                else {
                    panic!("original negative-nonempty rule")
                };
                p.proof_of_requirement_facts.clear();
            }
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn nonempty_guard_exclusion_retains_index_fresh_binders_other_guards_and_actual_proof() {
    for change in [
        "index",
        "binder",
        "carrier",
        "guards",
        "conclusion",
        "proof",
    ] {
        let (mut run, compiler) = super::execute(GUARDS);
        let D::GuardExclusion(p) = empty(strategy(&mut run.statement_results[0], 0)) else {
            panic!("original exclusion forall")
        };
        if change == "index" {
            p.excluded_guard_index = usize::MAX;
        } else {
            let VerifyFactResult::ForallFact(result) = p.exclusion.as_mut() else {
                panic!()
            };
            let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(f)) =
                result.as_mut()
            else {
                panic!()
            };
            match change {
                "binder" => {
                    f.fact.typed_parameters.groups[0].params[0].id = IdentifierId::new(u64::MAX)
                }
                "carrier" => {
                    f.fact.typed_parameters.groups[0].param_type =
                        ParamType::Obj(Obj::StandardSet(StandardSet::C))
                }
                "guards" => f.fact.dom_facts.clear(),
                "conclusion" => f.fact.then_facts.clear(),
                "proof" => f.proved_then_facts.clear(),
                _ => unreachable!(),
            }
        }
        assert!(super::compile_run(&run, &compiler, change).is_err());
    }
}

#[test]
fn nonempty_nested_empty_replays_its_inner_domain_certificate() {
    let (mut run, compiler) = super::execute(NESTED_EMPTY);
    let P::EmptyDomain(D::ParameterCarrier(p)) =
        nonempty(strategy(&mut run.statement_results[0], 0))
    else {
        panic!("original recursive empty domain")
    };
    p.parameter_group_index = usize::MAX;
    assert!(super::compile_run(&run, &compiler, "missing_inner_domain").is_err());
}

#[test]
fn nonempty_does_not_borrow_a_sibling_quantifiers_private_nonempty_fact() {
    let (mut run, compiler) = super::execute(SCOPES);
    super::compile_run(&run, &compiler, "separate_nonempty_scopes").unwrap();
    let first = super::atomic_proof_mut(leaf(nonempty(strategy(&mut run.statement_results[0], 0))));
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &first.searched_proof
    else {
        panic!("first private nonempty premise")
    };
    let foreign = cite.cite_fact_id;
    let second =
        super::atomic_proof_mut(leaf(nonempty(strategy(&mut run.statement_results[1], 0))));
    let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) = &mut second.searched_proof
    else {
        panic!("second private nonempty premise")
    };
    assert_ne!(cite.cite_fact_id, foreign);
    cite.cite_fact_id = foreign;
    assert!(super::compile_run(&run, &compiler, "escaped_nonempty_fact").is_err());
}

#[test]
fn nonempty_does_not_skip_the_executed_carrier_equality_intermediate() {
    let (mut run, compiler) = super::execute(CHAIN);
    super::compile_run(&run, &compiler, "original_carrier_intermediate").unwrap();
    super::forall_proof_mut(&mut run.statement_results[0])
        .proved_then_facts
        .remove(0);
    assert!(super::compile_run(&run, &compiler, "skipped_carrier_intermediate").is_err());
}
