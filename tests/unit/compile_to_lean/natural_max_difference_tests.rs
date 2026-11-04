use crate::execute::execute_fact_stmt::verify_atomic_fact::structural_membership_proof::{
    StructuralMembershipProof, StructuralMembershipReason,
};
use crate::prelude::*;

fn selected(run: &mut RunLitexCodeResult) -> &mut StructuralMembershipProof {
    let root = super::forall_proof_mut(&mut run.statement_results[0]);
    let atomic = super::atomic_proof_mut(&mut root.proved_then_facts[0].verify_result);
    let AtomicExceptEqualityFactSearchedProof::ByStructuralMembership(p) =
        &mut atomic.searched_proof
    else {
        panic!("original structural membership");
    };
    assert!(matches!(
        p.reason,
        StructuralMembershipReason::NaturalMaxDifference { .. }
    ));
    p
}

#[test]
fn natural_max_difference_replays_both_original_operand_selections() {
    for operand in ["m", "n"] {
        let source = format!("forall m, n N:\n    max(m,n)-{operand} $in N\n");
        let (mut run, compiler) = super::execute(&source);
        let p = selected(&mut run);
        let StructuralMembershipReason::NaturalMaxDifference { right_operand, .. } = p.reason
        else {
            unreachable!()
        };
        assert_eq!(right_operand, operand == "n");
        let output = compiler
            .compile_run(&run, "natural_max_difference")
            .unwrap();
        assert!(output.contains("Litex.naturalMaxDifference"));
        assert_eq!(
            output,
            compiler
                .compile_run(&run, "natural_max_difference")
                .unwrap()
        );
    }
}

#[test]
fn natural_max_difference_rejects_changed_selected_operands_and_carriers() {
    for operand in ["m", "n"] {
        for change in [
            "selection",
            "maximum",
            "subtrahend",
            "maximum_carrier",
            "subtrahend_carrier",
            "carrier",
        ] {
            let source = format!("forall m, n N:\n    max(m,n)-{operand} $in N\n");
            let (mut run, compiler) = super::execute(&source);
            let p = selected(&mut run);
            if change == "carrier" {
                p.set = StandardSet::Z;
            } else {
                let StructuralMembershipReason::NaturalMaxDifference {
                    maximum,
                    subtrahend,
                    right_operand,
                } = &mut p.reason
                else {
                    unreachable!()
                };
                match change {
                    "selection" => *right_operand = !*right_operand,
                    "maximum" => maximum.element = super::number_object("0"),
                    "subtrahend" => subtrahend.element = super::number_object("0"),
                    "maximum_carrier" => maximum.set = StandardSet::Z,
                    _ => subtrahend.set = StandardSet::Z,
                }
            }
            compiler
                .compile_run(&run, change)
                .expect_err("exact original maximum, selected subtrahend and natural carriers");
        }
    }
}
