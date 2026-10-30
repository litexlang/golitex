use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_builtin_strategy_result::FiniteSetProductPointwiseEqualityStrategySingleStep;
use crate::prelude::*;

const SOURCE: &str = include_str!("../../../lean/examples/finite_product_pointwise/statement.lit");
const MIXED: &str =
    include_str!("../../../lean/examples/finite_product_mixed_domains/statement.lit");
const REAL: &str = include_str!("../../../lean/examples/finite_product_real_factors/statement.lit");

fn selected(
    result: &mut RunLitexCodeResult,
) -> &mut FiniteSetProductPointwiseEqualityStrategySingleStep {
    selected_statement(&mut result.statement_results[0])
}

fn selected_statement(
    statement: &mut ExecStmtResult,
) -> &mut FiniteSetProductPointwiseEqualityStrategySingleStep {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(fact)) = statement else {
        panic!("forall source")
    };
    let VerifyFactResult::ForallFact(forall) = &mut fact.verify_result else {
        panic!("forall verification")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(forall)) =
        forall.as_mut()
    else {
        panic!("local introduction")
    };
    let proof = super::equality_proof_mut(&mut forall.proved_then_facts[0].verify_result);
    let EqualFactSearchedProof::ByBuiltinStrategy(
        EqualitySearchProofByBuiltinStrategy::FiniteSetProductPointwiseEquality(proof),
    ) = &mut proof.searched_proof
    else {
        panic!("the real source must select finite-product pointwise equality")
    };
    proof
}

#[test]
fn finite_product_rejects_a_pointwise_proof_from_a_sibling_scope() {
    let source = format!("{SOURCE}\n{REAL}");
    let (mut result, compiler) = super::execute(&source);
    super::compile_run(&result, &compiler, "two_finite_product_scopes").unwrap();
    let (left, right) = result.statement_results.split_at_mut(1);
    let left = selected_statement(&mut left[0]);
    let right = selected_statement(&mut right[0]);
    std::mem::swap(&mut left.pointwise_equality, &mut right.pointwise_equality);
    super::phase2_rejected(
        &result,
        &compiler,
        "sibling pointwise proof",
        &["FiniteProductPointwise/"],
    );
}

#[test]
fn finite_product_preserves_both_original_function_domains() {
    let (mut result, compiler) = super::execute(MIXED);
    selected(&mut result);
    let output = super::compile_run(&result, &compiler, "finite_product_mixed").unwrap();
    assert!(output.contains("finiteAggregateOn"));
    assert!(output.contains("Litex.finiteAggregate true"));
    assert!(output.contains("domain_mem_iff"));
}

#[test]
fn finite_product_replays_actual_local_member_and_pointwise_proof() {
    let (mut result, compiler) = super::execute(SOURCE);
    let proof = selected(&mut result);
    assert_eq!(proof.introduced_parameter.store_and_infer_results.len(), 1);
    let output = super::compile_run(&result, &compiler, "finite_product_scoped").unwrap();
    assert!(output.contains("finiteAggregateValue_congr"));
    assert!(output.contains("call_graphValue"));
    assert!(output.contains("_product_pointwise"));
    assert!(!output.contains("sorry") && !output.contains("admit"));
}

#[test]
fn finite_product_rejects_missing_or_changed_parameter_capture() {
    for changed in ["store", "ids", "binder"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = selected(&mut result);
        if changed == "store" {
            proof.introduced_parameter.store_and_infer_results.clear();
        } else if changed == "ids" {
            proof.introduced_parameter.stored_fact_ids[0] = FactId::new(u64::MAX);
        } else {
            let store =
                std::rc::Rc::get_mut(&mut proof.introduced_parameter.store_and_infer_results[0])
                    .unwrap();
            let StoreFactResult::AtomicFact(stored) = &mut store.store else {
                unreachable!()
            };
            let AtomicFact::InFact(member) = &mut stored.fact else {
                unreachable!()
            };
            let Obj::Identifier(IdentifierObj::Plain { id, .. }) = &mut member.element else {
                unreachable!()
            };
            *id = IdentifierId::new(u64::MAX);
        }
        super::phase2_rejected(
            &result,
            &compiler,
            changed,
            &["FiniteProductPointwise/", "Parameters/StoreCapture"],
        );
    }
}

#[test]
fn finite_product_rejects_changed_set_and_pointwise_endpoints() {
    for changed in ["set", "body"] {
        let (mut result, compiler) = super::execute(SOURCE);
        let proof = selected(&mut result);
        if changed == "set" {
            let eq = super::equality_proof_mut(&mut proof.set_equality);
            eq.fact.right = Obj::StandardSet(StandardSet::Z);
        } else {
            let eq = super::equality_proof_mut(&mut proof.pointwise_equality);
            eq.fact.right = eq.fact.left.clone();
        }
        super::phase2_rejected(&result, &compiler, changed, &["FiniteProductPointwise/"]);
    }
}

#[test]
fn finite_product_member_is_visible_only_after_introduction_in_its_own_scope() {
    let (mut result, compiler) = super::execute(SOURCE);
    let (parameter, member_id) = {
        let proof = selected(&mut result);
        let (parameter, _, store) =
            crate::compile_to_lean::helper::finite_product_parameter(proof).unwrap();
        let (id, member) = (parameter.id, store.primary_fact_id());
        let future = SourcePosition::new(None, SourceOwner::FiniteProductPointwise(proof), 0);
        assert_eq!(
            future
                .visible_parameter(id, &compiler.runtime)
                .unwrap_err()
                .route,
            "Identifier/FutureProducer"
        );
        assert_eq!(
            future
                .visible_fact(member, &compiler.runtime)
                .unwrap_err()
                .route,
            "Scope/FutureProducer"
        );
        let local = SourcePosition {
            before: 1,
            ..future
        };
        assert!(local.visible_parameter(id, &compiler.runtime).is_ok());
        assert!(local.visible_fact(member, &compiler.runtime).is_ok());
        (id, member)
    };
    let outside = SourcePosition::new(None, SourceOwner::Run(&result), usize::MAX);
    assert!(outside
        .visible_parameter(parameter, &compiler.runtime)
        .is_err());
    assert!(outside.visible_fact(member_id, &compiler.runtime).is_err());
}

#[test]
fn finite_product_rejects_false_pointwise_source() {
    let source = SOURCE.replace("{x + 0}", "{x + 1}");
    let command = parse_launch_command(&["-strict".into(), "-e".into(), source.clone()]).unwrap();
    let mut runtime =
        Runtime::new_with_result_detail(command, crate::result_detail::OutputDetail::Detailed);
    assert!(!runtime.run_litex_code(&source).unwrap().success);
}
