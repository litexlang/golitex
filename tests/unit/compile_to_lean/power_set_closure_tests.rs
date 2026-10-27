use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_known_special_property::{
    AtomicExceptEqualityFactSearchProofByKnownSpecialProperty, InFactSearchProofByKnownSpecialProperty,
};
use crate::prelude::*;

const UNION: &str = "forall X set, A,B power_set(X):\n    union(A,B) $in power_set(X)";
const COMPLEMENT_ALIAS: &str =
    "forall X,Y set,B set:\n    X = Y\n    =>:\n        set_minus(X,B) $in power_set(Y)";

#[test]
fn complement_event_carrier_replays_the_original_carrier_equality() {
    for source in [
        "forall X set,B set:\n    set_minus(X,B) $in power_set(X)",
        COMPLEMENT_ALIAS,
    ] {
        let (run, compiler) = super::execute(source);
        let generated = compiler.compile_run(&run, "complement_carrier").unwrap();
        assert!(
            generated.contains("Litex.subsetOfSame")
                && generated.contains("Litex.setMinusSubsetOfLeft")
        );
    }
}

#[test]
fn complement_event_carrier_replay_refuses_missing_alias_equality() {
    let (mut run, compiler) = super::execute(COMPLEMENT_ALIAS);
    let body = super::forall_proof_mut(&mut run.statement_results[0]);
    let atom = super::atomic_proof_mut(&mut body.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
        AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
            InFactSearchProofByKnownSpecialProperty::SetMinusInPowerSetOfLeft(p),
        ),
    ) = &mut atom.searched_proof
    else {
        panic!("actual carrier equality")
    };
    assert!(!p.left_equal_carrier.path.is_empty());
    p.left_equal_carrier.path.clear();
    let error = compiler
        .compile_run(&run, "missing_carrier_equality")
        .unwrap_err();
    assert_eq!(error.route, "Equality/PathEndpoint");
}

#[test]
fn power_set_closure_replays_all_four_checked_routes() {
    for (source, expected) in [
        (UNION, "Litex.unionSubsetOfBoth"),
        (
            "forall X set, A power_set(X), B set:\n    intersect(A,B) $in power_set(X)",
            "Litex.intersectSubsetOfLeft",
        ),
        (
            "forall X set, A set, B power_set(X):\n    intersect(A,B) $in power_set(X)",
            "Litex.intersectSubsetOfRight",
        ),
        (
            "forall X set, A power_set(X), B set:\n    set_minus(A,B) $in power_set(X)",
            "Litex.setMinusSubsetOfLeft",
        ),
    ] {
        let (run, compiler) = super::execute(source);
        let generated = compiler.compile_run(&run, "power_set_closure").unwrap();
        assert!(generated.contains(expected), "{generated}");
        assert!(generated.contains("Litex.inPowerSet_iff"));
        assert!(!generated.contains("sorry"));
    }
}

#[test]
fn power_set_closure_replay_rejects_changed_operands_and_carriers() {
    for wrong_carrier in [false, true] {
        let (mut run, compiler) = super::execute(UNION);
        let body = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut body.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
            AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
                InFactSearchProofByKnownSpecialProperty::UnionInPowerSet(proof),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("actual power-set closure evidence");
        };
        if wrong_carrier {
            let AtomicFact::InFact(member) = &mut proof.right.fact else {
                panic!("membership");
            };
            member.set = Obj::StandardSet(StandardSet::R);
        } else {
            proof.right.fact = proof.left.fact.clone();
        }
        let error = compiler
            .compile_run(&run, "changed_power_set_closure")
            .unwrap_err();
        assert!(
            format!("{error:?}").contains("PowerSetClosure/Premise"),
            "{error:?}"
        );
    }
}

const LITERAL_PAIR: &str =
    "forall X set,a,b X:\n    a != b\n    =>:\n        {a,b} $in power_set(X)";

#[test]
fn literal_event_carrier_replays_each_original_member() {
    for source in [
        "forall X set,a X:\n    {a} $in power_set(X)",
        LITERAL_PAIR,
        "forall X,Y set,a X:\n    X = Y\n    =>:\n        {a} $in power_set(Y)",
    ] {
        let (run, compiler) = super::execute(source);
        let lean = compiler.compile_run(&run, "literal_event").unwrap();
        assert!(lean.contains("Litex.insertSubset") && lean.contains("Litex.inPowerSet_iff"));
    }
}

#[test]
fn literal_event_carrier_replay_rejects_missing_or_reordered_member_evidence() {
    for missing in [false, true] {
        let (mut run, compiler) = super::execute(LITERAL_PAIR);
        let all = super::forall_proof_mut(&mut run.statement_results[0]);
        let atom = super::atomic_proof_mut(&mut all.proved_then_facts[0].verify_result);
        let AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty(
            AtomicExceptEqualityFactSearchProofByKnownSpecialProperty::InFact(
                InFactSearchProofByKnownSpecialProperty::ListSetInPowerSetFromMembers(p),
            ),
        ) = &mut atom.searched_proof
        else {
            panic!("actual literal bound")
        };
        if missing {
            p.members.pop();
        } else {
            p.members.swap(0, 1);
        }
        assert!(compiler.compile_run(&run, "bad_literal_event").is_err());
    }
}
