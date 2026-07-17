use super::*;

#[test]
fn requested_numeric_builtin_rules_verify_with_explicit_provenance() {
    run_with_large_stack(
        "requested_numeric_builtin_rules_verify_with_explicit_provenance",
        || {
            let source_code = r#"
forall a, b R:
    =>:
        a = 0 and b = 0
    <=>:
        a ^ 2 + b ^ 2 = 0

forall a, b R:
    a * b != 0
    =>:
        a != 0 and b != 0

forall a R_pos, b R_nz:
    a = (a ^ b) ^ (1 / b)
    a = (a ^ (1 / b)) ^ b

forall n Z, k N_pos:
    (-n) % k = (k - (n % k)) % k

forall n Z, m Z:
    n >= m or n <= m - 1

forall n Z, m N_pos, k N_pos:
    n ^ m % k = ((n % k) ^ m) % k

have x, y R
trust x ^ 2 + y ^ 2 = 0
x = 0
y = 0

have p, q R
trust p * q != 0
p != 0
q != 0
"#;

            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope(
                "requested_numeric_builtin_rules_verify_with_explicit_provenance",
            );
            let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
            let (run_succeeded, run_output) =
                render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);

            assert!(
                run_succeeded,
                "requested numeric builtin rules should verify directly:\n{run_output}"
            );
            for rule in [
                "equality: a = 0 from a^2 + b^2 = 0 over R",
                "product_nonzero_component: a * b != 0 gives a != 0 and b != 0",
                "equality: (a^m)^n = a^(m*n) for real exponents over positive real bases",
                "equality: (-n) % k = (k - n % k) % k for n in Z and k in N_pos",
                "or: integer discrete split x >= n or x <= n - 1",
                "equality: n^m % k = ((n % k)^m) % k for n in Z, m in N, and k in N_pos",
            ] {
                assert!(
                    run_output.contains(rule),
                    "missing builtin provenance `{rule}`:\n{run_output}"
                );
            }
        },
    );
}

#[test]
fn requested_numeric_builtin_rules_preserve_their_boundaries() {
    run_with_large_stack(
        "requested_numeric_builtin_rules_preserve_their_boundaries",
        || {
            let cases = [
                (
                    "square_sum_does_not_prove_a_nonzero_component",
                    r#"
have a, b R
trust a ^ 2 + b ^ 2 = 0
a = 1
"#,
                ),
                (
                    "product_nonzero_does_not_prove_a_zero_component",
                    r#"
have a, b R
trust a * b != 0
a = 0
"#,
                ),
                (
                    "power_of_power_requires_reciprocal_exponents",
                    r#"
(2 ^ 2) ^ (1 / 3) = 2
"#,
                ),
                (
                    "integer_mod_negation_does_not_accept_a_wrong_residue",
                    r#"
(-7) % 3 = 1
"#,
                ),
                (
                    "integer_predecessor_split_does_not_apply_to_reals",
                    r#"
forall n, m R:
    n >= m or n <= m - 1
"#,
                ),
                (
                    "integer_mod_power_does_not_accept_an_extra_residue",
                    r#"
forall n Z, m N_pos, k N_pos:
    n ^ m % k = ((n % k) ^ m + 1) % k
"#,
                ),
            ];

            for (name, source_code) in cases {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(name);
                let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
                let (run_succeeded, run_output) =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
                assert!(
                    !run_succeeded,
                    "{name} must remain outside the builtin rule boundary:\n{run_output}"
                );
            }
        },
    );
}
