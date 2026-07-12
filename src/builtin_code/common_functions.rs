pub const BUILTIN_ENV_CODE_FOR_COMMON_FUNCTIONS: &str = r#"
# Existence of such function is valid by definition of comparison

trust have max_of_finite_set fn(s power_set(R): $is_finite_set(s)) R
trust have min_of_finite_set fn(s power_set(R): $is_finite_set(s)) R

trust:
    forall s power_set(R), item s:
        $is_finite_set(s)
        =>:
            item <= max_of_finite_set(s)
            min_of_finite_set(s) <= item

    forall s power_set(R):
        $is_finite_set(s)
        =>:
            max_of_finite_set(s) $in s
            min_of_finite_set(s) $in s

# Natural-number well-ordering: every non-empty subset of N has a least
# element. Example: if `S power_set(N)` and `$is_nonempty_set(S)`, then
# `min_of_N_set(S) $in S` and `min_of_N_set(S) <= x` for every `x S`.
trust have min_of_N_set fn(s power_set(N): $is_nonempty_set(s)) N

trust:
    forall s power_set(N), item s:
        $is_nonempty_set(s)
        =>:
            min_of_N_set(s) <= item

    forall s power_set(N):
        $is_nonempty_set(s)
        =>:
            min_of_N_set(s) $in s
"#;
