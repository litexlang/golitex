use super::*;
use crate::execute::execute_fact_stmt::VerifyStateLevel;

#[test]
fn stored_equality_precedes_calculation_and_special_property_in_both_entries() {
    for (setup, code) in [
        (vec!["1 + 1 = 2"], "1 + 1 = 2"),
        (
            vec!["have p cart(R,R)", "p = (p(1),p(2))"],
            "p = (p(1),p(2))",
        ),
    ] {
        let mut rt = runtime();
        for statement in setup {
            exec_ok(&mut rt, statement);
        }
        for strategy in [false, true] {
            let goal = equal(&mut rt, code);
            let before = store_sizes(&rt);
            let result = if strategy {
                rt.verify_fact(
                    &Fact::AtomicFact(goal.clone().into()),
                    VerifyState::new(
                        crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule,
                    ),
                )
            } else {
                rt.verify_equal_fact(&goal, VerifyState::top_level())
            }
            .unwrap();
            let VerifyFactResult::Equality(result) = result else {
                panic!("equality")
            };
            let VerifyEqualityResult::Success(result) = *result else {
                panic!("{code}")
            };
            let EqualFactSearchedProof::ByEquivalenceClass(
                EqualFactSearchedProofByEquivalenceClass::KnownPath(path),
            ) = result.searched_proof
            else {
                panic!("already proved goal must cite its stored path: {code}, strategy={strategy}")
            };
            check_path(&rt, &path, &goal.left, &goal.right);
            assert_eq!(
                store_sizes(&rt),
                before,
                "known hit must not publish new evidence"
            );
        }
    }
}

#[test]
fn raw_known_equality_does_not_prove_a_new_structural_or_numeric_goal() {
    let mut rt = runtime();
    exec_ok(&mut rt, "have p cart(R,R)");
    let before = store_sizes(&rt);
    for code in ["p = (p(1),p(2))", "1 + 1 = 2", "1 + 1 = 3"] {
        let goal = equal(&mut rt, code);
        assert!(
            rt.lookup_known_obj_equality(&goal.left, &goal.right)
                .is_none(),
            "{code}"
        );
    }
    assert_eq!(store_sizes(&rt), before);
    assert!(verify(&mut rt, "1 + 1 = 3", VerifyState::top_level()).is_failed());
    assert!(verify(&mut rt, "1 / 0 = 1 / 0", VerifyState::top_level()).is_failed());
}

#[test]
fn run_examples_stored_equality_before_builtin() {
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/examples/proof_nodes/equal/by_equivalence_class/stored_equality_before_builtin.lit"
    ));
    let result = runtime().run_litex_code(source).unwrap();
    assert!(result.success, "released geo equality must be reusable");
}
