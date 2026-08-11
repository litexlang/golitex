use super::compile_to_lean_from_source;

const ZERO_ONE_TWO_PREMISE_SOURCE: &str = r#"
forall x R:
    0 <= abs(x)

forall x R:
    0 <= x
    =>:
        abs(x) = x

forall a, b R:
    a != 0
    b != 0
    =>:
        a / b != 0
"#;

const CATALOG_ACCEPTANCE_SOURCE: &str =
    include_str!("../../examples/05_compiler_interop/compile_to_lean_local_builtin_catalog.lit");

fn on_large_stack(test_name: &str, test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name(test_name.to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(test)
        .expect("spawn Litex-to-Lean catalog test")
        .join()
        .expect("Litex-to-Lean catalog test panicked");
}

#[test]
fn catalog_acceptance_source_emits_all_registered_wrappers() {
    on_large_stack("litex-to-lean-local-builtin-catalog", || {
        let lean = compile_to_lean_from_source(
            CATALOG_ACCEPTANCE_SOURCE,
            "compile_to_lean_local_builtin_catalog.lit",
        )
        .expect("compile complete registered local builtin catalog");
        for theorem in [
            "algebra_abs_mul",
            "order_abs_add_le",
            "order_abs_eq_neg_of_nonpositive",
            "order_abs_positive_of_nonzero",
            "order_abs_sub_abs_le_abs_add",
            "order_abs_sub_le_sum",
            "order_add_le_add",
            "order_add_le_add_left",
            "order_add_lt_add",
            "order_add_lt_add_left",
            "order_add_lt_add_of_le_of_lt",
            "order_add_lt_add_of_lt_of_le",
            "order_add_nonnegative",
            "order_add_positive",
            "order_add_positive_of_nonnegative_positive",
            "order_add_positive_of_positive_nonnegative",
            "order_div_nonnegative",
            "order_div_positive",
            "order_greater_equal_of_greater",
            "order_neg_abs_le",
            "order_le_max_left",
            "order_le_max_right",
            "order_le_add_of_nonnegative_right",
            "order_less_equal_of_less",
            "order_max_absorb_min_left",
            "order_max_associative",
            "order_max_commutative",
            "order_max_eq_left_of_le",
            "order_max_eq_right_of_le",
            "order_max_idempotent",
            "order_max_monotone",
            "order_min_absorb_max_left",
            "order_min_associative",
            "order_min_commutative",
            "order_min_eq_left_of_le",
            "order_min_eq_right_of_le",
            "order_min_idempotent",
            "order_min_le_left",
            "order_min_le_right",
            "order_min_monotone",
            "order_mul_nonnegative",
            "order_mul_positive",
            "order_self_le_abs",
            "order_sub_le_of_le_of_nonnegative",
            "order_sub_nonnegative_of_less_equal",
            "order_sub_positive_of_less",
            "set_intersect_associative",
            "set_empty_subset",
            "set_intersect_finite",
            "set_intersect_eq_left_of_subset",
            "set_intersect_eq_right_of_subset",
            "set_intersect_membership",
            "set_intersect_subset_left",
            "set_intersect_subset_right",
            "set_intersect_union_distributive",
            "set_set_minus_intersect_de_morgan",
            "set_set_minus_membership",
            "set_set_minus_finite_left",
            "set_set_minus_infinite_of_infinite_finite",
            "set_set_minus_recover_subset",
            "set_set_minus_subset_left",
            "set_set_minus_union_de_morgan",
            "set_subset_union_left",
            "set_subset_union_right",
            "set_subset_eq_set_minus_recovery",
            "set_power_set_finite",
            "set_power_set_membership_of_subset",
            "set_power_set_nonempty",
            "set_union_associative",
            "set_union_empty_left",
            "set_union_empty_right",
            "set_union_membership_left",
            "set_union_membership_right",
            "set_union_finite",
            "set_union_nonempty_left",
            "set_union_nonempty_right",
            "set_union_subset",
            "nonzero_mul",
        ] {
            assert!(lean.contains(&format!("theorem {theorem}")), "{lean}");
            assert!(
                lean.contains(&format!("_root_.Litex.BuiltinRules.{theorem}")),
                "{lean}"
            );
        }
        assert_eq!(
            lean.matches("_root_.Litex.BuiltinRules.").count(),
            86,
            "{lean}"
        );
        assert!(
            lean.contains("(min (min a b) c) = (min a (min b c))"),
            "{lean}"
        );
        assert!(lean.contains("(max a (min a b)) = a"), "{lean}");
        assert!(!lean.contains("sorry"), "{lean}");
        assert!(!lean.contains("admit"), "{lean}");
    });
}

#[test]
fn zero_one_and_two_premise_local_builtins_emit_registered_wrappers() {
    on_large_stack("litex-to-lean-local-builtins", || {
        let lean =
            compile_to_lean_from_source(ZERO_ONE_TWO_PREMISE_SOURCE, "local_builtin_catalog.lit")
                .expect("compile registered local builtin examples");
        for theorem in [
            "order_abs_nonnegative",
            "order_abs_eq_self_of_nonnegative",
            "nonzero_div",
        ] {
            assert!(lean.contains(&format!("theorem {theorem}")), "{lean}");
            assert!(
                lean.contains(&format!("_root_.Litex.BuiltinRules.{theorem}")),
                "{lean}"
            );
        }
        assert!(!lean.contains("sorry"), "{lean}");
        assert!(!lean.contains("admit"), "{lean}");
    });
}

#[test]
#[ignore = "requires a real Mathlib project; set LITEX_LEAN_PROJECT"]
fn registered_local_builtin_output_compiles_with_real_mathlib() {
    on_large_stack("litex-to-lean-local-builtins-mathlib", || {
        let project = std::env::var("LITEX_LEAN_PROJECT")
            .expect("set LITEX_LEAN_PROJECT to a real Mathlib project");
        let lake = std::env::var("LITEX_LAKE").unwrap_or_else(|_| "lake".to_string());
        let lean = compile_to_lean_from_source(
            CATALOG_ACCEPTANCE_SOURCE,
            "compile_to_lean_local_builtin_catalog.lit",
        )
        .expect("compile complete registered local builtin catalog");
        let path = std::env::temp_dir().join(format!(
            "litex-local-builtin-catalog-{}.lean",
            std::process::id()
        ));
        std::fs::write(&path, lean).expect("write temporary Lean module");
        let output = std::process::Command::new(lake)
            .current_dir(project)
            .args(["env", "lean"])
            .arg(&path)
            .output()
            .expect("run Lean kernel");
        let _ = std::fs::remove_file(&path);
        assert!(
            output.status.success(),
            "Lean failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    });
}
