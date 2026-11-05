use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::{
    result::{AtomicExceptEqualityFactSearchedProof, VerifyAtomicExceptEqualityFactResult},
    search_atomic_except_equality_fact_proof_by_builtin_rules::not_equal::{
        NotEqualFactSearchProofByBuiltinRule, ProductComponentNonzeroBuiltinRuleProof,
    },
    AtomicExceptEqualityFactSearchProofByBuiltinRule,
};
use crate::execute::execute_proof_block_stmt::{
    ExecClaimBodyProof, ExecClaimStmtResult, ExecProofBlockStmtResult,
};
use crate::prelude::*;

const SOURCE: &str = r#"# A nonzero complex product has nonzero factors.
claim:
    ? forall a C, b C:
        a*b != 0
        =>:
            a != 0
            b != 0
    a != 0
    b != 0
"#;
const REVERSED: &str = r#"# A nonzero product gives its right factor in reverse orientation.
claim:
    ? forall a C, b C:
        0 != a*b
        =>:
            0 != b
    0 != b
"#;
const COMPUTED_ZERO: &str = r#"# Nonzero products and factors can be compared to a calculated zero.
claim:
    ? forall a C, b C:
        a*b != 1-1
        =>:
            a != 1-1
    a != 1-1
"#;
const ZERO_PRODUCT: &str = r#"# A zero product on the left is distinct from a nonzero product.
claim:
    ? forall a C, b C:
        0*1 != a*b
        =>:
            0*1 != b
    0*1 != b
"#;

fn selected_rule(run: &mut RunLitexCodeResult) -> &mut ProductComponentNonzeroBuiltinRuleProof {
    let ExecStmtResult::ProofBlock(ExecProofBlockStmtResult::Claim(ExecClaimStmtResult::Success(
        claim,
    ))) = &mut run.statement_results[0]
    else {
        panic!("successful claim")
    };
    let ExecClaimBodyProof::Forall(body) = &mut claim.body else {
        panic!("forall body")
    };
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = &mut body.proof_steps[0]
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
            NotEqualFactSearchProofByBuiltinRule::ProductComponentNonzero(rule),
        ),
    ) = &mut proof.searched_proof
    else {
        panic!("selected product factor rule")
    };
    rule
}

#[test]
fn product_nonzero_replays_exact_original_fact_citation() {
    for source in [SOURCE, REVERSED, COMPUTED_ZERO, ZERO_PRODUCT] {
        let (mut run, compiler) = super::execute(source);
        let id = selected_rule(&mut run)
            .product_nonzero_proof
            .cite_fact_id()
            .expect("fact id");
        let lean = compiler.compile_run(&run, "product_nonzero").expect(source);
        assert!(lean.contains("Litex.productNonzeroFactors"));
        assert!(lean.contains(&format!("h_{}", id.value())));
    }
}

#[test]
fn product_nonzero_rejects_wrong_fact_or_component() {
    for change in ["citation", "component", "zero"] {
        let (mut run, compiler) = super::execute(SOURCE);
        let premise = &mut selected_rule(&mut run).product_nonzero_proof;
        match change {
            "citation" => {
                let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(known) =
                    premise.searched_proof.as_mut()
                else {
                    panic!("known fact")
                };
                known.cite_fact_id = FactId::new(u64::MAX);
            }
            "component" => {
                let AtomicFact::NotEqualFact(fact) = &mut premise.fact else {
                    panic!("nonzero")
                };
                let Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)) = &mut fact.left
                else {
                    panic!("product")
                };
                product.left = Box::new(Obj::Literal(Literal::Number(Number::new("3".into()))));
            }
            _ => {
                let AtomicFact::NotEqualFact(fact) = &mut premise.fact else {
                    panic!("nonzero")
                };
                fact.right = Obj::Literal(Literal::Number(Number::new("1".into())));
            }
        }
        compiler
            .compile_run(&run, "wrong_product_nonzero")
            .expect_err(change);
    }
}

#[test]
fn product_factor_nonzero_requires_the_product_premise() {
    let source = "claim:\n    ? forall a C, b C:\n        =>:\n            a != 0\n    a != 0\n";
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.into()]).unwrap();
    let mut runtime = Runtime::new(command);
    assert!(!runtime.run_litex_code(source).unwrap().success);
}
