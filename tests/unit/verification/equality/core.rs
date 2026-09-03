//! Tests for equality verification and evidence selection.

use crate::fact::EqualFact;
use crate::object::{Abs, Add, AtomicName, Identifier, Mul, Number, Obj, StructObj, Sub, Union};
use crate::runtime::Runtime;
use crate::syntax::source_conventions::default_line_file;
use crate::test_support::execute_source;
use crate::verification::VerifyState;

#[test]
fn zero_premise_structural_equality_still_requires_known_equal_leaves() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("zero_premise_structural_boundary.lit");

    let x: Obj = Identifier::new("x".to_string()).into();
    let y: Obj = Identifier::new("y".to_string()).into();
    let one: Obj = Number::new("1".to_string()).into();
    let two: Obj = Number::new("2".to_string()).into();
    let left: Obj = Mul::new(
        Add::new(x.clone(), one.clone()).into(),
        Add::new(x, two.clone()).into(),
    )
    .into();
    let right: Obj = Mul::new(Add::new(y.clone(), one).into(), Add::new(y, two).into()).into();
    let equal_fact = EqualFact::new(left, right, default_line_file());

    assert!(runtime
        .verify_equal_fact_with_zero_premise_verification(&equal_fact, &VerifyState::initial())
        .expect("zero-premise equality boundary must not error")
        .is_unknown());
}

#[test]
fn structural_equality_runs_only_from_the_outer_round() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("structural_equality_outer_round");

    let (_, setup_error) = execute_source(
        "struct Box<s set>:\n    value s\nhave A, B set\n",
        &mut runtime,
    );
    assert!(
        setup_error.is_none(),
        "fixture definitions: {setup_error:?}"
    );

    let a_binding = runtime
        .resolved_identifier_symbol("A")
        .expect("fixture A binding");
    let b_binding = runtime
        .resolved_identifier_symbol("B")
        .expect("fixture B binding");
    let a: Obj = Identifier::new_bound("A".to_string(), a_binding).into();
    let b: Obj = Identifier::new_bound("B".to_string(), b_binding).into();
    let union_ab: Obj = Union::new(a.clone(), b.clone()).into();
    let union_ba: Obj = Union::new(b, a).into();
    let left: Obj =
        StructObj::new(AtomicName::WithoutMod("Box".to_string()), vec![union_ab]).into();
    let right: Obj =
        StructObj::new(AtomicName::WithoutMod("Box".to_string()), vec![union_ba]).into();
    let equal_fact = EqualFact::new(left, right, default_line_file());
    assert!(runtime
        .verify_equal_fact_by_known_equality(&equal_fact)
        .is_unknown());
    assert!(runtime
        .verify_equal_fact(&equal_fact, &VerifyState::initial().with_next_round())
        .expect("later-round equality verification")
        .is_unknown());
    assert!(runtime
        .verify_equal_fact(&equal_fact, &VerifyState::initial())
        .expect("outer-round equality verification")
        .is_success());
}

#[test]
fn checked_definition_reduction_has_no_candidate_graph_or_ambient_mode() {
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/equality/core.rs"
    ));
    let reduction_impl = source
        .split("fn try_reduce_one_checked_definition_side(")
        .nth(1)
        .expect("direct checked-definition reduction must exist")
        .split("fn checked_function_definition_reduction_source(")
        .next()
        .expect("definition source lookup must follow direct reduction");

    assert!(reduction_impl.contains("verify_equal_fact_with_bounded_builtin_routes"));
    assert!(reduction_impl.contains("complete_proven_fact_candidate"));
    assert!(reduction_impl.contains("reduced_equality_result"));
    assert!(reduction_impl.contains(", verify_state)?"));
    assert!(!reduction_impl.contains("VerifyState::initial()"));
    assert!(!source.contains("well_definedness_verified"));
    let obsolete_depth = ["known_equality_candidate_", "replay_depth"].concat();
    let obsolete_collector = ["collect_known_equality_", "pairs_from_envs"].concat();
    let obsolete_pair_attempt = ["try_verify_one_equality_", "representative_pair"].concat();
    assert!(!source.contains(&obsolete_depth));
    assert!(!source.contains(&obsolete_collector));
    assert!(!source.contains(&obsolete_pair_attempt));
    assert!(!reduction_impl.contains("verify_atomic_fact_with_known_forall"));
    assert!(!reduction_impl.contains("verify_equal_fact("));

    let structural_source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/builtin_rules/equality_structural.rs"
    ));
    let terminating_comparator = structural_source
        .split("fn equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(")
        .nth(1)
        .expect("terminating structural comparator must exist")
        .split("pub fn same_shape_and_corresponding_args_match")
        .next()
        .expect("central structural matcher must follow the terminating comparator");
    assert!(terminating_comparator.contains("verify_equal_fact_with_known_fact"));
    assert!(terminating_comparator.contains("verify_equal_fact_by_direct_evaluation"));
    assert!(!terminating_comparator.contains("verify_equal_fact_with_zero_premise_verification"));
    assert!(terminating_comparator.contains("beta_reduce_complete_anonymous_application_once"));
    let obsolete_one_rule = ["verify_atomic_fact_with_one_", "builtin_rule"].concat();
    assert!(!terminating_comparator.contains(&obsolete_one_rule));
    let obsolete_inner = ["verify_atomic_fact_with_builtin_rules_", "inner"].concat();
    assert!(!terminating_comparator.contains(&obsolete_inner));
    assert!(!terminating_comparator.contains("resolve_obj"));
    assert!(!terminating_comparator.contains("verify_atomic_fact_with_known_forall"));
    assert!(!terminating_comparator.contains("verify_equal_fact("));

    let atomic_source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/atomic/core.rs"
    ));
    assert!(!atomic_source.contains(&obsolete_depth));
    let forall_source = crate::verification::universal_search_source::SOURCE;
    assert!(!forall_source.contains(&obsolete_depth));

    let equality_builtin_source = crate::verification::equality_dispatch_source::SOURCE;
    assert!(!equality_builtin_source.contains(&obsolete_depth));

    let set_membership_source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/verification/builtin_rules/in_fact_builtin/set_membership.rs"
    ));
    assert!(!set_membership_source.contains(&obsolete_depth));
}

#[test]
fn terminating_comparator_allows_computation_and_bounded_symbolic_normalization() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("terminating_structural_computation");
    let one: Obj = Number::new("1".to_string()).into();
    let two: Obj = Number::new("2".to_string()).into();
    let one_plus_one: Obj = Add::new(one.clone(), one).into();

    assert!(
        runtime.equal_fact_sides_are_congruent_by_known_equalities(&EqualFact::new_from_refs(
            &one_plus_one,
            &two,
            default_line_file()
        ),)
    );
    assert!(runtime
        .equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(
            &EqualFact::new_from_refs(&one_plus_one, &two, default_line_file()),
        )
        .expect("terminating structural comparison"));

    let x: Obj = Identifier::new("x".to_string()).into();
    let zero: Obj = Number::new("0".to_string()).into();
    let x_plus_zero: Obj = Add::new(x.clone(), zero).into();
    assert!(runtime
        .equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(
            &EqualFact::new_from_refs(&x_plus_zero, &x, default_line_file()),
        )
        .expect("bounded symbolic normalization"));

    let y: Obj = Identifier::new("y".to_string()).into();
    let x_minus_y: Obj = Sub::new(x.clone(), y.clone()).into();
    let y_minus_x: Obj = Sub::new(y.clone(), x.clone()).into();
    let abs_x_minus_y: Obj = Abs::new(x_minus_y).into();
    let abs_y_minus_x: Obj = Abs::new(y_minus_x).into();
    assert!(runtime
        .equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(
            &EqualFact::new_from_refs(&abs_x_minus_y, &abs_y_minus_x, default_line_file(),),
        )
        .expect("absolute-value sign normalization"));

    let abs_x: Obj = Abs::new(x).into();
    let abs_y: Obj = Abs::new(y).into();
    assert!(!runtime
        .equal_fact_sides_are_equal_by_terminating_reduction_and_congruence(
            &EqualFact::new_from_refs(&abs_x, &abs_y, default_line_file()),
        )
        .expect("unrelated absolute values must not compare equal"));
}
