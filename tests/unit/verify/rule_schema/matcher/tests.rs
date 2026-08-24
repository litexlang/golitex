use super::*;
use crate::verify::local_builtin_catalog::registered_local_builtin_rules;

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
