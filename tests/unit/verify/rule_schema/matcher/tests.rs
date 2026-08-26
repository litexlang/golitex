use super::*;
use crate::parse::Tokenizer;
use crate::verify::local_builtin_catalog::registered_local_builtin_rules;
use std::rc::Rc;

#[test]
fn catalog_conclusions_match_positive_and_reject_nearest_wrong_shape() {
    std::thread::Builder::new()
        .name("local-builtin-catalog-match".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let rules = registered_local_builtin_rules().expect("compile catalog");
            let abs_nonnegative = rules
                .iter()
                .find(|rule| rule.id().as_str() == "order.abs_nonnegative")
                .expect("abs rule");
            let matched = match_conclusion(
                abs_nonnegative.schema(),
                &abs_nonnegative.schema().conclusion,
                MatchLimits::default(),
            )
            .expect("match");
            assert!(matched.is_some());

            let AtomicFact::LessEqualFact(conclusion) = &abs_nonnegative.schema().conclusion else {
                panic!("expected <= conclusion")
            };
            let wrong: AtomicFact = EqualFact::new(
                conclusion.left.clone(),
                conclusion.right.clone(),
                conclusion.line_file.clone(),
            )
            .into();
            assert!(
                match_conclusion(abs_nonnegative.schema(), &wrong, MatchLimits::default())
                    .expect("mismatch")
                    .is_none()
            );
        })
        .expect("spawn catalog matcher")
        .join()
        .expect("catalog matcher panicked");
}

#[test]
fn sum_single_schema_matches_two_alpha_equivalent_anonymous_occurrences() {
    std::thread::Builder::new()
        .name("local-builtin-sum-single-match".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let rules = registered_local_builtin_rules().expect("compile catalog");
            let sum_single = rules
                .iter()
                .find(|rule| rule.id().as_str() == "aggregate.sum_single")
                .expect("sum-single rule");
            let mut runtime = Runtime::new();
            runtime.start_isolated_source("sum-single-matcher-test.lit");
            let (_, setup_error) = execute_source("have fn odd(k Z) Z = 2 * k - 1", &mut runtime);
            assert!(setup_error.is_none(), "{setup_error:?}");
            let mut blocks = Tokenizer::new()
                .parse_blocks(
                    "sum(1, 1, fn(k Z) Z {odd(k)}) = fn(j Z) Z {odd(j)}(1)",
                    Rc::from("sum-single-matcher-test.lit"),
                )
                .expect("tokenize target");
            let fact = runtime.parse_fact(&mut blocks[0]).expect("parse target");
            let Fact::AtomicFact(target) = fact else {
                panic!("expected atomic equality")
            };
            let matched = match_conclusion(sum_single.schema(), &target, MatchLimits::default())
                .expect("match sum-single target");
            assert!(matched.is_some(), "sum-single target must match its schema");
        })
        .expect("spawn sum-single matcher")
        .join()
        .expect("sum-single matcher panicked");
}
