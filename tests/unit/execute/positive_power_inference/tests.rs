use crate::prelude::*;
use crate::store_fact_and_infer::{InferAtomicFactResult, InferEqualityResult, InferFactResult};

fn runtime() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: true,
        language: OutputLanguage::English,
    })
}

fn exec(rt: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize(code, rt.current_file.clone())
        .unwrap();
    let statements = rt.parse(&tokens).unwrap();
    assert_eq!(statements.len(), 1);
    rt.exec_stmt(&statements[0]).unwrap()
}

fn seed_rules(result: &ExecStmtResult) -> &[InferEqualityResult] {
    let ExecStmtResult::Fact(ExecFactStmtResult::Success(statement)) = result else {
        panic!("successful forall statement expected")
    };
    let VerifyFactResult::ForallFact(forall) = &statement.verify_result else {
        panic!("forall proof expected")
    };
    let VerifyForallFactResult::Success(VerifyForallFactProof::ByLocalIntroduction(proof)) =
        forall.as_ref()
    else {
        panic!("local introduction expected")
    };
    let seed = &proof.assumed_dom_facts.last().unwrap().store_and_infer;
    let Some(InferFactResult::AtomicFact(InferAtomicFactResult::EqualFact(rules))) = &seed.infer
    else {
        panic!("equality inference expected")
    };
    rules
}

#[test]
fn positive_power_inference_retains_positive_bases_and_nonzero_real_squares() {
    for source in [
        "forall a R+, n, y R:\n    a^n=y\n    =>:\n        y $in R+",
        "forall a R*, y R:\n    a^2=y\n    =>:\n        y $in R+",
        "forall a R-, y R:\n    a^2=y\n    =>:\n        y $in R+",
        "forall a R+, n, y R:\n    y=a^n\n    =>:\n        y $in R+",
    ] {
        let mut rt = runtime();
        let result = exec(&mut rt, source);
        assert!(!result.is_failed(), "{source}");
        let power = seed_rules(&result)
            .iter()
            .find_map(|r| match r {
                InferEqualityResult::PositiveRealPower(power) => Some(power),
                _ => None,
            })
            .expect("positive membership must actually be inferred");
        assert!(!power.derived.is_empty());
        assert!(power.derived.iter().all(|d| d.store.atomic_components().iter().any(|(_, fact)| {
            matches!(fact, AtomicFact::InFact(member) if matches!(member.set, Obj::StandardSet(StandardSet::RPos)) && member.element.readable_string() == "y")
        })), "retain the actual transported positive membership");
    }
}

#[test]
fn positive_power_inference_leaves_definition_search_to_explicit_proof() {
    let mut rt = runtime();
    for source in [
        "have fn constant_positive(t R) R = 1",
        "have t R",
        "have value R = constant_positive(t)^3",
    ] {
        assert!(!exec(&mut rt, source).is_failed(), "{source}");
    }
    let tokens = crate::tokenize::Tokenizer::new()
        .tokenize("value $in R+", rt.current_file.clone())
        .unwrap();
    let parsed = rt.parse(&tokens).unwrap();
    let Stmt::Fact(Fact::AtomicFact(member)) = &parsed[0] else {
        panic!("membership")
    };
    assert!(
        !rt.execution_environments_stack.iter().any(|env| env
            .facts
            .facts_by_id
            .values()
            .any(|known| { matches!(known, Fact::AtomicFact(atom) if atom.ir() == member.ir()) })),
        "optional inference must not unfold unrelated definitions"
    );
    for source in [
        "constant_positive(t) = 1",
        "constant_positive(t) > 0",
        "have proved_value R = constant_positive(t)^3",
        "proved_value $in R+",
    ] {
        assert!(
            !exec(&mut rt, source).is_failed(),
            "explicit proof remains usable: {source}"
        );
    }
}

#[test]
fn positive_power_inference_does_not_publish_unsupported_positive_membership() {
    for source in [
        "forall a, y R:\n    a^2=y\n    =>:\n        y=y",
        "forall a R-, y R:\n    a^3=y\n    =>:\n        y=y",
        "forall y R:\n    0^2=y\n    =>:\n        y=y",
        "forall a, y C:\n    a^2=y\n    =>:\n        y=y",
    ] {
        let mut rt = runtime();
        let result = exec(&mut rt, source);
        assert!(!result.is_failed(), "the seed remains valid: {source}");
        assert!(
            !seed_rules(&result)
                .iter()
                .any(|r| matches!(r, InferEqualityResult::PositiveRealPower(_))),
            "no unsupported inference: {source}"
        );
    }
    for source in [
        "forall a, y R:\n    a^2=y\n    =>:\n        y $in R+",
        "forall a R-, y R:\n    a^3=y\n    =>:\n        y $in R+",
        "forall y R:\n    0^2=y\n    =>:\n        y $in R+",
    ] {
        assert!(
            exec(&mut runtime(), source).is_failed(),
            "false conclusion remains rejected: {source}"
        );
    }
}

#[test]
fn run_examples_positive_power_inference_bounded_premises() {
    for source in [
        include_str!("../../../../examples/infer/equal/positive_real_power_bounded_premises.lit"),
        include_str!("../../../../examples/infer/equal/positive_real_power.lit"),
        include_str!("../../../../examples/infer/equal/nonzero_real_square.lit"),
    ] {
        assert!(runtime().run_litex_code(source).unwrap().success);
    }
}
