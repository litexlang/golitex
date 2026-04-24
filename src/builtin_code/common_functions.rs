pub const BUILTIN_ENV_CODE_FOR_COMMON_FUNCTIONS: &str = r#"
# Existence of such function is valid by definition of comparison
let max_of_finite_set fn(s power_set(R): $is_finite_set(s)) R
let min_of_finite_set fn(s power_set(R): $is_finite_set(s)) R

know:
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
"#;
