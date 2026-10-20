use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferInFactResult, InferResult};

const SQUARE: &str =
    include_str!("../../../../examples/proof_nodes/equal/by_builtin_rule/sqrt_square.lit");
const POSITIVE_CLAIM: &str = "claim:\n    ? forall x R+:\n        x + 0 = x\n    x + 0 = x\n";

fn positive_sign(
    store: &StoreFactAndInferResult,
) -> &crate::store_fact_and_infer::InferInFactSignedStandardSetSignResult {
    let Some(InferResult::AtomicFact(InferAtomicFactResult::InFact(rules))) = &store.infer else {
        panic!("the captured positive-real membership inference")
    };
    rules
        .iter()
        .find_map(|rule| match rule {
            InferInFactResult::SignedStandardSetSign(sign) => Some(sign),
            _ => None,
        })
        .expect("the original three sign projections")
}

#[test]
fn global_positive_signs_cite_the_original_applied_strict_producer() {
    let (result, compiler) = super::execute(SQUARE);
    let have = super::ordinary_have(&result.statement_results[0]);
    let store = &have.store_and_infer_result.store_and_infer_results[0];
    let sign = positive_sign(store);
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 0);
    let introduced = SourcePosition::new(
        Some(&run),
        SourceOwner::Statement(&result.statement_results[0]),
        1,
    );
    let seed = introduced
        .source_fact(store.primary_fact_id(), &compiler.runtime)
        .unwrap();
    let Some(InferResult::AtomicFact(infer)) = &store.infer else {
        unreachable!()
    };
    let pending = SourcePosition::new(
        Some(&introduced),
        SourceOwner::AtomicInference(seed, infer),
        0,
    );
    let strict_id = sign.derived[0].primary_fact_id();
    assert!(
        pending.visible_fact(strict_id, &compiler.runtime).is_err(),
        "the strict projection cannot be cited before its actual store"
    );
    let ready = SourcePosition {
        before: 1,
        ..pending
    };
    let (_, reference) = ready.visible_fact(strict_id, &compiler.runtime).unwrap();
    let parameter = &have.statement.param_def.groups[0].params[0];
    let id = parameter.id.value();
    let expected = format!(
        "(h_{} (M := M) (_Host_i{id} := _Host_i{id}) (_rep_i{id} := _rep_i{id}) _value_i{id} h_{})",
        strict_id.value(),
        store.primary_fact_id().value(),
    );
    assert_eq!(reference, expected);
    let output = compiler
        .compile_run(&result, "global_positive_sign_context")
        .expect("all recorded sign and square proofs compile");
    assert!(output.contains(&format!(
        "(Litex.ltToLe (Litex.number (M := M) 0) _value_i{id} {expected})"
    )));
    assert!(output.contains(&format!(
        "(Litex.ltNotSame (Litex.number (M := M) 0) _value_i{id} {expected})"
    )));
}

#[test]
fn global_equality_inference_seed_uses_named_host_and_representation_arguments() {
    let (result, compiler) = super::execute(SQUARE);
    let statement = &result.statement_results[2];
    let store = &super::fact_statement(statement).store_and_infer_result;
    let Some(InferResult::AtomicFact(infer)) = &store.infer else {
        panic!("the original equality inference")
    };
    let run = SourcePosition::new(None, SourceOwner::Run(&result), 2);
    let published = SourcePosition::new(Some(&run), SourceOwner::Statement(statement), 1);
    let seed = published
        .source_fact(store.primary_fact_id(), &compiler.runtime)
        .unwrap();
    let inference = SourcePosition::new(
        Some(&published),
        SourceOwner::AtomicInference(seed, infer),
        0,
    );
    let (_, reference) = inference
        .visible_fact(store.primary_fact_id(), &compiler.runtime)
        .unwrap();
    assert_eq!(
        reference,
        published.context_application(&format!("h_{}", store.primary_fact_id().value()))
    );
    assert!(reference.contains("(M := M) (_Host_i"));
    assert!(reference.contains(" := _Host_i"));
    assert!(reference.contains(" := _rep_i"));
    let output = compiler
        .compile_run(&result, "global_equality_inference_context")
        .unwrap();
    assert!(
        !output.contains(&format!("(h_{} _Host_", store.primary_fact_id().value())),
        "implicit carrier parameters must never become positional object arguments"
    );
}

#[test]
fn local_positive_signs_keep_the_original_local_strict_hypothesis() {
    let (result, compiler) = super::execute(POSITIVE_CLAIM);
    let output = compiler
        .compile_run(&result, "local_positive_sign_context")
        .expect("local original sign inference");
    let strict_line = output
        .lines()
        .find(|line| line.contains("Litex.ltToLe (Litex.number (M := M) 0)"))
        .expect("the weak projection of the local strict sign");
    assert!(
        strict_line.contains(" h_"),
        "the strict producer remains a local proof hypothesis"
    );
    assert!(!strict_line.contains("(_Host_"));
}
