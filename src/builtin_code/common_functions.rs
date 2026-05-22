pub const BUILTIN_ENV_CODE_FOR_COMMON_FUNCTIONS: &str = r#"
# Existence of such function is valid by definition of comparison

let max_of_finite_set fn(s power_set(R): $is_finite_set(s)) R
let min_of_finite_set fn(s power_set(R): $is_finite_set(s)) R
let floor fn(x R) Z
let ceil fn(x R) Z

know:
    forall x R:
        floor(x) <= x
        x < floor(x) + 1
        ceil(x) - 1 < x
        x <= ceil(x)

    forall x R, y Z:
        0 <= x - y
        x - y < 1
        =>:
            y = floor(x)

    forall x R, y Z:
        0 <= y - x
        y - x < 1
        =>:
            y = ceil(x)

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

let min_of_N_set fn(s power_set(N)) N

know:
    forall s power_set(N), item s:
        min_of_N_set(s) <= item

    forall s power_set(N):
        min_of_N_set(s) $in s
"#;
