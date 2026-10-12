use crate::prelude::*;

const SOURCE: &str = "forall A set, x A:\n    A $subset R\n    =>:\n        x $in R\n";

#[test]
fn subset_membership_consumes_both_original_atomic_citations() {
    let (result, compiler) = super::execute(SOURCE);
    let body = super::forall_proof(&result.statement_results[0]);
    let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) =
        &super::phase2_atomic(&body.proved_then_facts[0].verify_result).searched_proof
    else {
        panic!("the selected structural membership");
    };
    let StructuralMembershipReason::KnownSubset(known) = &proof.reason else {
        panic!("the actual known member/subset route");
    };
    let member_id = known.member_proof.cite_fact_id().unwrap();
    let subset_id = known.subset_proof.cite_fact_id().unwrap();
    assert_ne!(member_id, subset_id);
    let output = super::compile_run(&result, &compiler, "subset_numeric_member").unwrap();
    assert!(output.contains(&format!("h_{}", member_id.value())));
    assert!(output.contains(&format!("h_{}", subset_id.value())));
    assert!(output.contains("Litex.denote"));
}

#[test]
fn subset_member_justifies_order_formation_without_changing_the_host() {
    let source = "forall A set, x A:\n    A $subset R\n    =>:\n        x<=x\n";
    let (result, compiler) = super::execute(source);
    let output = super::compile_run(&result, &compiler, "subset_order_wd").unwrap();
    assert!(output.contains("Litex.leRefl"));
    assert!(output.contains("Litex.Representation M"));
    assert!(output.contains("Litex.Subset"));
    assert!(output.contains("_Host_i"));
}

#[test]
fn subset_membership_replays_element_and_carrier_equality_transport() {
    for source in [
        "forall A,B set, x A:\n    A=B\n    B $subset R\n    =>:\n        x $in R\n",
        "have Target set=R\nforall A set, x A:\n    A $subset Target\n    =>:\n        x $in R\n",
    ] {
        let (result, compiler) = super::execute(source);
        let output = super::compile_run(&result, &compiler, "subset_alias_transport").unwrap();
        assert!(output.contains("Litex.inOfSame") || output.contains("Litex.subsetOfSame"));
    }
}

#[test]
fn subset_membership_rejects_disconnected_premise_subjects() {
    for change in ["member", "source", "target", "reversed"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let body = super::forall_proof_mut(&mut result.statement_results[0]);
        let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) =
            &mut super::atomic_proof_mut(&mut body.proved_then_facts[0].verify_result)
                .searched_proof
        else {
            panic!("the original structural proof");
        };
        let StructuralMembershipReason::KnownSubset(known) = &mut proof.reason else {
            panic!("the original subset membership proof");
        };
        match change {
            "member" => {
                let AtomicFact::InFact(member) = &mut known.member_proof.fact else {
                    unreachable!()
                };
                member.element = super::number_object("23");
            }
            "source" | "target" | "reversed" => {
                let AtomicFact::SubsetFact(subset) = &mut known.subset_proof.fact else {
                    unreachable!()
                };
                match change {
                    "source" => subset.left = Obj::StandardSet(StandardSet::C),
                    "target" => subset.right = Obj::StandardSet(StandardSet::C),
                    "reversed" => std::mem::swap(&mut subset.left, &mut subset.right),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
        let error = super::compile_run(&result, &compiler, "wrong_subset_subject").unwrap_err();
        assert_eq!(error.route, "StructuralMembership/SubsetSubject");
    }
}

#[test]
fn subset_membership_rejects_missing_original_citation() {
    for missing in ["member", "subset"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let body = super::forall_proof_mut(&mut result.statement_results[0]);
        let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(proof) =
            &mut super::atomic_proof_mut(&mut body.proved_then_facts[0].verify_result)
                .searched_proof
        else {
            panic!("the original structural proof");
        };
        let StructuralMembershipReason::KnownSubset(known) = &mut proof.reason else {
            unreachable!()
        };
        let selected = if missing == "member" {
            &mut known.member_proof
        } else {
            &mut known.subset_proof
        };
        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(cite) =
            selected.searched_proof.as_mut()
        else {
            unreachable!()
        };
        cite.cite_fact_id = FactId::new(u64::MAX);
        let error = super::compile_run(&result, &compiler, "missing_subset_cite")
            .expect_err("both original member and subset citations are required");
        assert_eq!(error.route, "FactId/Resolution");
    }
}
