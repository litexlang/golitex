use super::LitexToLeanCompiler;
use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferAtomicFactResult, InferEqualFactPositiveRealPowerResult, InferEqualFactResult,
    InferPositiveRealPowerPositivityResult, InferResult,
};

const FORWARD: &str = "forall a R+, n N, y R:\n    a^(n+0)=y\n    =>:\n        y $in R+\n";
const REVERSE: &str = "forall a R+, n N, y R:\n    y=a^(n+0)\n    =>:\n        y $in R+\n";
const DOUBLE: &str = "forall a R+, n N:\n    a^(n+0)=a^n\n    =>:\n        a^n $in R+\n";
const SQUARE: &str = "forall a R, y R:\n    a!=0\n    a^2=y\n    =>:\n        y $in R+\n";
const BASE: &str = "have fn inference_positive_constant(t R) R+ = 1\n\
forall t R, y R:\n    0 < inference_positive_constant(t)\n    inference_positive_constant(t)^2=y\n    =>:\n        y $in R+\n";

fn checked(source: &str) -> (RunLitexCodeResult, LitexToLeanCompiler) {
    let mut runtime = Runtime::new_with_result_detail(
        LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: true,
            language: OutputLanguage::English,
        },
        crate::result_detail::OutputDetail::Detailed,
    );
    let result = runtime.run_litex_code(source).expect("original source run");
    assert!(result.success && result.session_error.is_none(), "{source}");
    (result, LitexToLeanCompiler::new(runtime))
}

fn original(result: &mut RunLitexCodeResult) -> &mut InferEqualFactPositiveRealPowerResult {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) =
        result.statement_results.last_mut().unwrap()
    else {
        panic!("original forall statement")
    };
    let VerifyFactResult::ForallFact(proof) = &mut statement.verify_result else {
        panic!("original forall result")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        proof.as_mut()
    else {
        panic!("original local introduction")
    };
    let Some(InferResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) = &mut proof
        .assumed_dom_facts
        .last_mut()
        .unwrap()
        .store_and_infer
        .infer
    else {
        panic!("original equality inference group")
    };
    rules
        .iter_mut()
        .find_map(|rule| match rule {
            InferEqualFactResult::PositiveRealPower(power) => Some(power),
            _ => None,
        })
        .expect("actual selected positive-power inference")
}

fn positivity(rule: &mut InferEqualFactPositiveRealPowerResult) -> &mut VerifyFactResult {
    match &mut rule.transports[0].positivity {
        InferPositiveRealPowerPositivityResult::BasePositive(proof)
        | InferPositiveRealPowerPositivityResult::PowerPositive(proof) => proof,
    }
}

fn atomic(result: &mut VerifyFactResult) -> &mut VerifyAtomicExceptEqualityFactSuccess {
    let VerifyFactResult::AtomicExceptEquality(proof) = result else {
        panic!("original atomic proof")
    };
    let VerifyAtomicExceptEqualityFactResult::Success(proof) = proof.as_mut() else {
        panic!("original successful child")
    };
    proof
}

fn reject(result: &RunLitexCodeResult, compiler: &LitexToLeanCompiler, route: &str) {
    assert_eq!(
        compiler
            .compile_run(result, "changed_positive_power_evidence")
            .unwrap_err()
            .route,
        route
    );
}

#[test]
fn positive_power_inference_replays_both_equality_orientations_and_original_children() {
    for (source, count, base_selected) in [
        (FORWARD, 1, false),
        (REVERSE, 1, false),
        (DOUBLE, 2, false),
        (SQUARE, 1, false),
        (BASE, 1, true),
    ] {
        let (mut result, compiler) = checked(source);
        let rule = original(&mut result);
        assert_eq!(rule.transports.len(), count);
        assert_eq!(
            matches!(
                rule.transports[0].positivity,
                InferPositiveRealPowerPositivityResult::BasePositive(_)
            ),
            base_selected,
            "retain the actual selected positivity variant"
        );
        let original_children = rule
            .transports
            .iter_mut()
            .map(|transport| {
                let positive = match &mut transport.positivity {
                    InferPositiveRealPowerPositivityResult::BasePositive(proof)
                    | InferPositiveRealPowerPositivityResult::PowerPositive(proof) => proof,
                };
                (
                    atomic(positive).fact.fact_id(),
                    atomic(&mut transport.exponent_real).fact.fact_id(),
                    transport.derived.primary_fact_id(),
                )
            })
            .collect::<Vec<_>>();
        let lean = compiler
            .compile_run(&result, "original_positive_power_transport")
            .expect("replay the actual selected inference");
        assert!(lean.contains("Litex.inRPos_intro"));
        if source == REVERSE {
            assert!(lean.contains("(Eq.symm h_"));
        }
        for (positive, exponent, derived) in original_children {
            assert!(lean.contains(&format!("have h_{} :", positive.value())));
            assert!(lean.contains(&format!("have h_{} :", exponent.value())));
            assert!(lean.contains(&format!("have h_{} :", derived.value())));
        }
    }
}

#[test]
fn positive_power_inference_rejects_changed_seed_and_power_subject() {
    let (mut result, compiler) = checked(FORWARD);
    original(&mut result).transports[0].source_fact_id = FactId::new(u64::MAX);
    reject(&result, &compiler, "Inference/PositivePowerSeed");

    let (mut result, compiler) = checked(REVERSE);
    original(&mut result).transports[0].power =
        Obj::Literal(Literal::Number(Number::new("2".into())));
    reject(&result, &compiler, "Inference/PositivePowerSource");
}

#[test]
fn positive_power_inference_rejects_missing_and_reordered_original_transports() {
    let (mut result, compiler) = checked(FORWARD);
    original(&mut result).transports.clear();
    reject(&result, &compiler, "Inference/PositivePowerArity");

    let (mut result, compiler) = checked(DOUBLE);
    original(&mut result).transports.swap(0, 1);
    assert!(compiler
        .compile_run(&result, "reordered_positive_power_transports")
        .is_err());
}

#[test]
fn positive_power_inference_rejects_weakened_and_wrong_positivity() {
    let (mut result, compiler) = checked(FORWARD);
    let child = atomic(positivity(original(&mut result)));
    let AtomicFact::LessFact(bound) = &child.fact else {
        panic!("original strict zero lower bound")
    };
    child.fact = AtomicFact::LessEqualFact(LessEqualFact {
        fact_id: bound.fact_id,
        left: bound.left.clone(),
        right: bound.right.clone(),
        line_file: bound.line_file.clone(),
    });
    reject(
        &result,
        &compiler,
        "Inference/PositivePowerPositivitySubject",
    );

    let (mut result, compiler) = checked(SQUARE);
    let AtomicFact::LessFact(bound) = &mut atomic(positivity(original(&mut result))).fact else {
        panic!("original strict power positivity")
    };
    bound.right = Obj::Literal(Literal::Number(Number::new("2".into())));
    reject(
        &result,
        &compiler,
        "Inference/PositivePowerPositivitySubject",
    );
}

#[test]
fn positive_power_inference_rejects_changed_exponent_and_missing_child_wd() {
    let (mut result, compiler) = checked(FORWARD);
    let AtomicFact::InFact(member) =
        &mut atomic(&mut original(&mut result).transports[0].exponent_real).fact
    else {
        panic!("original exponent real membership")
    };
    member.set = Obj::StandardSet(StandardSet::C);
    reject(&result, &compiler, "Inference/PositivePowerExponentSubject");

    let (mut result, compiler) = checked(SQUARE);
    atomic(positivity(original(&mut result)))
        .well_defined_proof
        .as_detailed_mut()
        .unwrap()
        .well_defined_of_each_parameter
        .clear();
    assert!(compiler
        .compile_run(&result, "missing_positive_power_child_wd")
        .is_err());
}

#[test]
fn positive_power_inference_rejects_changed_derived_subject_and_identity() {
    let (mut result, compiler) = checked(REVERSE);
    let StoreFactResult::AtomicFact(stored) =
        &mut original(&mut result).transports[0].derived.store
    else {
        panic!("original direct membership store")
    };
    let AtomicFact::InFact(member) = &mut stored.fact else {
        panic!("original target membership")
    };
    member.element = Obj::Literal(Literal::Number(Number::new("2".into())));
    reject(
        &result,
        &compiler,
        "Inference/PositivePowerConclusionSubject",
    );

    let (mut result, compiler) = checked(FORWARD);
    let StoreFactResult::AtomicFact(stored) =
        &mut original(&mut result).transports[0].derived.store
    else {
        panic!("original direct membership store")
    };
    stored.fact_id = FactId::new(u64::MAX);
    assert!(compiler
        .compile_run(&result, "changed_positive_power_store_identity")
        .is_err());
}
