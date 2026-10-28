use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
    search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::{
        NotEqualFactSearchProofByBuiltinRule, PowNonzeroFromBaseBuiltinRuleProof,
    },
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::prelude::*;

fn selected_rule(run: &mut RunLitexCodeResult) -> &mut PowNonzeroFromBaseBuiltinRuleProof {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        &mut run.statement_results[1]
    else {
        panic!("successful fact")
    };
    let VerifyFactResult::AtomicExceptEquality(result) = &mut statement.verify_result else {
        panic!("atomic fact")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
        panic!("verified fact")
    };
    let AtomicExceptEqualityFactSearchedProof::ByBuiltinRule(
        AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact(
            NotEqualFactSearchProofByBuiltinRule::PowNonzeroFromBase(rule),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("selected power nonzero rule")
    };
    rule
}

#[test]
fn power_nonzero_replays_selected_rule_in_both_orientations() {
    for source in ["have z Z\n2^z != 0", "have z Z\n0 != 2^z"] {
        let (mut run, compiler) = super::execute(source);
        assert_eq!(selected_rule(&mut run).proof_of_requirement_facts.len(), 2);
        let lean = compiler.compile_run(&run, "power_nonzero").expect(source);
        assert!(lean.contains("Litex.powNonzeroOfBase"));
    }
}

#[test]
fn power_nonzero_rejects_missing_and_reordered_original_premises() {
    for change in ["missing_exponent", "missing_base", "reordered"] {
        let (mut run, compiler) = super::execute("have z Z\n2^z != 0");
        let requirements = &mut selected_rule(&mut run).proof_of_requirement_facts;
        match change {
            "missing_exponent" => {
                requirements.remove(0);
            }
            "missing_base" => {
                requirements.pop();
            }
            _ => requirements.swap(0, 1),
        }
        compiler
            .compile_run(&run, "invalid_power_nonzero")
            .expect_err(change);
    }
}

#[test]
fn power_nonzero_rejects_premises_about_other_subjects() {
    for change in ["wrong_carrier", "wrong_base"] {
        let (mut run, compiler) = super::execute("have z Z\n2^z != 0");
        let requirements = &mut selected_rule(&mut run).proof_of_requirement_facts;
        let index = usize::from(change == "wrong_base");
        let VerifyFactResult::AtomicExceptEquality(result) = &mut requirements[index] else {
            panic!("atomic premise")
        };
        let VerifyAtomicExceptEqualityFactResult::Success(proof) = result.as_mut() else {
            panic!("verified premise")
        };
        match &mut proof.fact {
            AtomicFact::InFact(member) if change == "wrong_carrier" => {
                member.set = Obj::StandardSet(StandardSet::C);
            }
            AtomicFact::NotEqualFact(nonzero) if change == "wrong_base" => {
                nonzero.left = Obj::Literal(Literal::Number(Number::new("3".into())));
            }
            _ => panic!("expected premise"),
        }
        compiler
            .compile_run(&run, "wrong_power_nonzero_premise")
            .expect_err(change);
    }
}
