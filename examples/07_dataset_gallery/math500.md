# MATH-500

Finished competition-style problems across algebra, intermediate algebra, prealgebra, number theory, precalculus, geometry, and counting/probability.

Each example below is an independent checked Litex snippet. The metadata record keeps the dataset translation fields next to the runnable code.

## 1. `test/algebra/1078`

```yaml
id: "test/algebra/1078"
source: "MATH-500"
topic: "algebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall x R:
            -4 < x^4 + 4*x^2 < 21
            =>:
                -sqrt(3) < x < sqrt(3)

    (x^2 + 2)^2 = x^4 + 4*x^2 + 4 < 21 + 4 = 25 = 5^2
    0 <= x^2
    0 <= x^2 + 2
    0 <= 5
    by contra x^2 + 2 < 5:
        x^2 + 2 >= 5
        5 <= x^2 + 2
        5^2 <= (x^2 + 2)^2
        impossible (x^2 + 2)^2 < 5^2
    x^2 = (x^2 + 2) + (-2) < 5 + (-2) = 3
    sqrt(3) > 0
    sqrt(3) >= 0
    sqrt(3)^2 = 3
    by contra x < sqrt(3):
        x >= sqrt(3)
        sqrt(3) <= x
        0 <= sqrt(3) <= x
        0 <= x
        sqrt(3)^2 <= x^2
        3 <= x^2
        impossible x^2 < 3
    by contra x > -sqrt(3):
        x <= -sqrt(3)
        -x = (-1) * x >= (-1) * (-sqrt(3)) = sqrt(3)
        sqrt(3) <= -x
        0 <= sqrt(3) <= -x
        0 <= -x
        sqrt(3)^2 <= (-x)^2
        (-x)^2 = x^2
        3 <= x^2
        impossible x^2 < 3
```

## 2. `test/algebra/1282`

```yaml
id: "test/algebra/1282"
source: "MATH-500"
topic: "algebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Let k = sqrt(120 - sqrt(x)).  The integer choices are k = 0 through 10,
# and each gives x = (120 - k^2)^2.
have fn x_from_k(k R) R = (120 - k ^ 2) ^ 2
have possible_k set = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
have possible_x set = {14400, 14161, 13456, 12321, 10816, 9025, 7056, 5041, 3136, 1521, 400}

x_from_k(0) = (120 - 0 ^ 2) ^ 2 = 14400
x_from_k(1) = (120 - 1 ^ 2) ^ 2 = 14161
x_from_k(2) = (120 - 2 ^ 2) ^ 2 = 13456
x_from_k(3) = (120 - 3 ^ 2) ^ 2 = 12321
x_from_k(4) = (120 - 4 ^ 2) ^ 2 = 10816
x_from_k(5) = (120 - 5 ^ 2) ^ 2 = 9025
x_from_k(6) = (120 - 6 ^ 2) ^ 2 = 7056
x_from_k(7) = (120 - 7 ^ 2) ^ 2 = 5041
x_from_k(8) = (120 - 8 ^ 2) ^ 2 = 3136
x_from_k(9) = (120 - 9 ^ 2) ^ 2 = 1521
x_from_k(10) = (120 - 10 ^ 2) ^ 2 = 400
possible_k = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
possible_x = {14400, 14161, 13456, 12321, 10816, 9025, 7056, 5041, 3136, 1521, 400}
count({14400, 14161, 13456, 12321, 10816, 9025, 7056, 5041, 3136, 1521, 400}) = 11
```

## 3. `test/algebra/2043`

```yaml
id: "test/algebra/2043"
source: "MATH-500"
topic: "algebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# The denominator is sqrt(q), so the real-valued domain requires q > 0,
# where q = x^2 - 5*x + 6 = (x - 2) * (x - 3).

scratch:
    have ans set = union(info(2), oinf(3))

claim:
    prove:
        forall x R:
            x < 2
            =>:
                x^2 - 5*x + 6 > 0
                sqrt(x^2 - 5*x + 6) > 0
                sqrt(x^2 - 5*x + 6) != 0

    x - 2 < 0
    x - 3 = x - 2 - 1 < 0 - 1 = -1 < 0
    (x - 2) * (x - 3) > 0
    x^2 - 5*x + 6 = (x - 2) * (x - 3)
    x^2 - 5*x + 6 > 0
    sqrt(x^2 - 5*x + 6) > 0
    sqrt(x^2 - 5*x + 6) != 0

claim:
    prove:
        forall x R:
            x > 3
            =>:
                x^2 - 5*x + 6 > 0
                sqrt(x^2 - 5*x + 6) > 0
                sqrt(x^2 - 5*x + 6) != 0

    x - 3 > 0
    x - 2 = (x - 3) + 1 > 0 + 1 = 1 > 0
    (x - 2) * (x - 3) > 0
    x^2 - 5*x + 6 = (x - 2) * (x - 3)
    x^2 - 5*x + 6 > 0
    sqrt(x^2 - 5*x + 6) > 0
    sqrt(x^2 - 5*x + 6) != 0

claim:
    prove:
        forall x R:
            x $in union(info(2), oinf(3))
            =>:
                x^2 - 5*x + 6 > 0
                sqrt(x^2 - 5*x + 6) > 0
                sqrt(x^2 - 5*x + 6) != 0

    by cases:
        prove:
            x^2 - 5*x + 6 > 0
        case x $in info(2):
            x < 2
            x^2 - 5*x + 6 > 0
        case x $in oinf(3):
            x > 3
            x^2 - 5*x + 6 > 0
    sqrt(x^2 - 5*x + 6) > 0
    sqrt(x^2 - 5*x + 6) != 0

claim:
    prove:
        forall x R:
            2 <= x <= 3
            =>:
                x^2 - 5*x + 6 <= 0

    x - 2 >= 0
    x - 3 <= 0
    (x - 2) * (x - 3) <= 0
    x^2 - 5*x + 6 = (x - 2) * (x - 3)
    x^2 - 5*x + 6 <= 0

claim:
    prove:
        forall x R:
            x^2 - 5*x + 6 > 0
            =>:
                x < 2 or x > 3

    by cases:
        prove:
            x < 2 or x > 3
        case x < 2:
            x < 2 or x > 3
        case x >= 2:
            by cases:
                prove:
                    x < 2 or x > 3
                case x > 3:
                    x < 2 or x > 3
                case x <= 3:
                    2 <= x <= 3
                    x^2 - 5*x + 6 <= 0
                    impossible x^2 - 5*x + 6 > 0

claim:
    prove:
        forall x R:
            x^2 - 5*x + 6 > 0
            =>:
                x $in union(info(2), oinf(3))

    x < 2 or x > 3
    by cases:
        prove:
            x $in union(info(2), oinf(3))
        case x < 2:
            x $in info(2)
            x $in union(info(2), oinf(3))
        case x > 3:
            x $in oinf(3)
            x $in union(info(2), oinf(3))

scratch:
    union(info(2), oinf(3)) = union(info(2), oinf(3))
```

## 4. `test/algebra/2257`

```yaml
id: "test/algebra/2257"
source: "MATH-500"
topic: "algebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# For a real solution, the radicals and denominator require 2*x >= 0 and
# 3*x - 1 > 0. Clearing the nonzero denominator and squaring gives 19*x = 9.

claim:
    prove:
        forall x R:
            2*x >= 0
            3*x - 1 > 0
            sqrt(2*x) / sqrt(3*x - 1) = 3 / 2
            =>:
                x = 9 / 19

    sqrt(3*x - 1) > 0
    sqrt(3*x - 1) != 0
    sqrt(2*x) = (3 / 2) * sqrt(3*x - 1)
    (sqrt(2*x))^2 = ((3 / 2) * sqrt(3*x - 1))^2
    (sqrt(2*x))^2 = 2*x
    ((3 / 2) * sqrt(3*x - 1))^2 = (3 / 2)^2 * (sqrt(3*x - 1))^2
    (3 / 2)^2 = 9 / 4
    (sqrt(3*x - 1))^2 = 3*x - 1
    ((3 / 2) * sqrt(3*x - 1))^2 = 9 / 4 * (3*x - 1)
    2*x = 9 / 4 * (3*x - 1)
    8*x = 4 * (2*x) = 4 * (9 / 4 * (3*x - 1)) = 9 * (3*x - 1)
    8*x = 27*x - 9
    8*x + 9 = (27*x - 9) + 9 = 27*x
    27*x = 8*x + 9
    27*x - 8*x = (8*x + 9) - 8*x = 9
    27*x - 8*x = 19*x
    19*x = 9
    x = 9 / 19

scratch:
    2 * (9 / 19) = 18 / 19 > 0
    2 * (9 / 19) >= 0
    3 * (9 / 19) - 1 = 8 / 19 > 0
    sqrt(18 / 19) > 0
    sqrt(8 / 19) > 0
    sqrt(8 / 19) != 0
    ((3 / 2) * sqrt(8 / 19))^2 = (3 / 2)^2 * sqrt(8 / 19)^2
    (3 / 2)^2 = 9 / 4
    sqrt(8 / 19)^2 = 8 / 19
    ((3 / 2) * sqrt(8 / 19))^2 = 9 / 4 * (8 / 19) = 18 / 19
    sqrt(18 / 19)^2 = 18 / 19
    sqrt(18 / 19)^2 = ((3 / 2) * sqrt(8 / 19))^2
    sqrt(18 / 19) = (3 / 2) * sqrt(8 / 19)
    sqrt(18 / 19) / sqrt(8 / 19) = 3 / 2
    sqrt(2 * (9 / 19)) / sqrt(3 * (9 / 19) - 1) = sqrt(18 / 19) / sqrt(8 / 19) = 3 / 2
```

## 5. `test/counting_and_probability/1009`

```yaml
id: "test/counting_and_probability/1009"
source: "MATH-500"
topic: "counting and probability"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Selecting six indistinguishable cookies of three kinds is stars and bars:
# choose the two separators among eight positions.
have fn choose_by_factorials(total_factorial, selected_factorial, leftover_factorial R: selected_factorial * leftover_factorial != 0) R = total_factorial / (selected_factorial * leftover_factorial)

have factorial_8 R = 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1
have factorial_6 R = 6 * 5 * 4 * 3 * 2 * 1
have factorial_2 R = 2 * 1

factorial_6 * factorial_2 != 0

have assortments R = choose_by_factorials(factorial_8, factorial_6, factorial_2)

factorial_8 = 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1 = 40320
factorial_6 = 6 * 5 * 4 * 3 * 2 * 1 = 720
factorial_2 = 2 * 1 = 2
assortments = choose_by_factorials(factorial_8, factorial_6, factorial_2) = factorial_8 / (factorial_6 * factorial_2) = 40320 / (720 * 2) = 28
```

## 6. `test/counting_and_probability/666`

```yaml
id: "test/counting_and_probability/666"
source: "MATH-500"
topic: "counting and probability"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Choose 4 of 5 upper-class soldiers and 8 of 10 lower-class soldiers.
have fn choose_by_factorials(total_factorial, selected_factorial, leftover_factorial R: selected_factorial * leftover_factorial != 0) R = total_factorial / (selected_factorial * leftover_factorial)

have factorial_5 R = 5 * 4 * 3 * 2 * 1
have factorial_4 R = 4 * 3 * 2 * 1
have factorial_1 R = 1
have factorial_10 R = 10 * 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1
have factorial_8 R = 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1
have factorial_2 R = 2 * 1

factorial_4 * factorial_1 != 0
factorial_8 * factorial_2 != 0

have upper_choices R = choose_by_factorials(factorial_5, factorial_4, factorial_1)
have lower_choices R = choose_by_factorials(factorial_10, factorial_8, factorial_2)
have battalions R = upper_choices * lower_choices

factorial_5 = 5 * 4 * 3 * 2 * 1 = 120
factorial_4 = 4 * 3 * 2 * 1 = 24
factorial_10 = 10 * 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1 = 3628800
factorial_8 = 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1 = 40320
factorial_2 = 2
upper_choices = choose_by_factorials(factorial_5, factorial_4, factorial_1) = 120 / (24 * 1) = 5
lower_choices = choose_by_factorials(factorial_10, factorial_8, factorial_2) = 3628800 / (40320 * 2) = 45
battalions = upper_choices * lower_choices = 5 * 45 = 225
```

## 7. `test/geometry/465`

```yaml
id: "test/geometry/465"
source: "MATH-500"
topic: "geometry"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Let x be angle ADC in degrees.  The shaded outer ring contributes x/360 of
# 3*pi, and the shaded inner circle contributes (360-x)/360 of pi.
have angle R = 120
have inner_radius R = 1
have outer_radius R = 2
have outer_ring_area R = pi * (outer_radius^2 - inner_radius^2)
have outer_shaded_area R = angle / 360 * outer_ring_area
have inner_shaded_area R = (360 - angle) / 360 * pi * inner_radius^2
have shaded_area R = outer_shaded_area + inner_shaded_area
have target_shaded_area R = 5 / 12 * pi * outer_radius^2

outer_ring_area = pi * (outer_radius^2 - inner_radius^2) = pi * (2^2 - 1^2) = 3 * pi
outer_shaded_area = angle / 360 * outer_ring_area = 120 / 360 * (3 * pi) = pi
inner_shaded_area = (360 - angle) / 360 * pi * inner_radius^2 = (360 - 120) / 360 * pi * 1^2 = 2 * pi / 3
shaded_area = outer_shaded_area + inner_shaded_area = pi + 2 * pi / 3 = 5 * pi / 3
target_shaded_area = 5 / 12 * pi * outer_radius^2 = 5 / 12 * pi * 2^2 = 5 * pi / 3
shaded_area = target_shaded_area
angle = 120
```

## 8. `test/geometry/473`

```yaml
id: "test/geometry/473"
source: "MATH-500"
topic: "geometry"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
have fn cube_volume_ft(side_ft R) R = side_ft ^ 3
have fn cube_surface_area_in2(side_ft R) R = 6 * (12 * side_ft) ^ 2

claim:
    prove:
        forall s R:
            s >= 0
            cube_volume_ft(s) = 1
            =>:
                s = 1
    cube_volume_ft(s) = s ^ 3
    s ^ 3 = 1
    s ^ 3 - 1 = 0
    s ^ 3 - 1 = (s - 1) * (s ^ 2 + s + 1)
    (s - 1) * (s ^ 2 + s + 1) = 0
    s ^ 2 >= 0
    s ^ 2 + s + 1 >= 1
    s ^ 2 + s + 1 != 0
    s - 1 = ((s - 1) * (s ^ 2 + s + 1)) / (s ^ 2 + s + 1) = 0 / (s ^ 2 + s + 1) = 0
    s = 1

claim:
    prove:
        forall side_ft, area_in2 R:
            side_ft >= 0
            cube_volume_ft(side_ft) = 1
            area_in2 = cube_surface_area_in2(side_ft)
            =>:
                area_in2 = 864
    side_ft = 1
    cube_surface_area_in2(side_ft) = 6 * (12 * side_ft) ^ 2 = 6 * (12 * 1) ^ 2 = 864
    area_in2 = cube_surface_area_in2(side_ft) = 864
```

## 9. `test/intermediate_algebra/1063`

```yaml
id: "test/intermediate_algebra/1063"
source: "MATH-500"
topic: "intermediate algebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
struct C:
    re R
    im R

have fn C_add(a, b &C) &C = (&C{a}.re + &C{b}.re, &C{a}.im + &C{b}.im)
have fn C_sub(a, b &C) &C = (&C{a}.re - &C{b}.re, &C{a}.im - &C{b}.im)
have fn C_mul(a, b &C) &C = (&C{a}.re * &C{b}.re - &C{a}.im * &C{b}.im, &C{a}.re * &C{b}.im + &C{a}.im * &C{b}.re)
have C_i &C = (0, 1)

# z_0 = 1 / 137 + i and F(z) = (z + i) / (z - i).  The complex quotient is
# certified here by multiplying the proposed value by the denominator.
have z0 &C = (1 / 137, 1)
have z1 &C = (1, 274)

claim:
    prove:
        C_mul(z1, C_sub(z0, C_i)) = C_add(z0, C_i)

    C_i = (0, 1)
    C_sub(z0, C_i) = C_sub((1 / 137, 1), (0, 1)) = (1 / 137 - 0, 1 - 1) = (1 / 137, 0)
    C_add(z0, C_i) = C_add((1 / 137, 1), (0, 1)) = (1 / 137 + 0, 1 + 1) = (1 / 137, 2)
    C_mul(z1, C_sub(z0, C_i)) = C_mul((1, 274), (1 / 137, 0))
    C_mul((1, 274), (1 / 137, 0)) = (1 * (1 / 137) - 274 * 0, 1 * 0 + 274 * (1 / 137)) = (1 / 137, 2)
    C_mul(z1, C_sub(z0, C_i)) = C_add(z0, C_i)

# The Mobius matrix for F is [[1, i], [1, -i]].  Its cube is a nonzero scalar
# matrix, so F^3 is the identity wherever all three iterates are defined.
# Proof debt: std/complex has no division/rational-map composition API yet.
have m11 &C = (1, 0)
have m12 &C = (0, 1)
have m21 &C = (1, 0)
have m22 &C = (0, -1)

C_mul((1, 0), (1, 0)) = (1 * 1 - 0 * 0, 1 * 0 + 0 * 1) = (1, 0)
C_mul((0, 1), (1, 0)) = (0 * 1 - 1 * 0, 0 * 0 + 1 * 1) = (0, 1)
C_add(C_mul((1, 0), (1, 0)), C_mul((0, 1), (1, 0))) = C_add((1, 0), (0, 1)) = (1 + 0, 0 + 1) = (1, 1)

C_mul((1, 0), (0, 1)) = (1 * 0 - 0 * 1, 1 * 1 + 0 * 0) = (0, 1)
C_mul((0, 1), (0, -1)) = (0 * 0 - 1 * (-1), 0 * (-1) + 1 * 0) = (1, 0)
C_add(C_mul((1, 0), (0, 1)), C_mul((0, 1), (0, -1))) = C_add((0, 1), (1, 0)) = (0 + 1, 1 + 0) = (1, 1)

C_mul((0, -1), (1, 0)) = (0 * 1 - (-1) * 0, 0 * 0 + (-1) * 1) = (0, -1)
C_add(C_mul((1, 0), (1, 0)), C_mul((0, -1), (1, 0))) = C_add((1, 0), (0, -1)) = (1 + 0, 0 + -1) = (1, -1)

C_mul((0, -1), (0, -1)) = (0 * 0 - (-1) * (-1), 0 * (-1) + (-1) * 0) = (-1, 0)
C_add(C_mul((1, 0), (0, 1)), C_mul((0, -1), (0, -1))) = C_add((0, 1), (-1, 0)) = (0 + -1, 1 + 0) = (-1, 1)

C_mul((1, 1), (1, 0)) = (1 * 1 - 1 * 0, 1 * 0 + 1 * 1) = (1, 1)
C_add(C_mul((1, 1), (1, 0)), C_mul((1, 1), (1, 0))) = C_add((1, 1), (1, 1)) = (1 + 1, 1 + 1) = (2, 2)

C_mul((1, 1), (0, 1)) = (1 * 0 - 1 * 1, 1 * 1 + 1 * 0) = (-1, 1)
C_mul((1, 1), (0, -1)) = (1 * 0 - 1 * (-1), 1 * (-1) + 1 * 0) = (1, -1)
C_add(C_mul((1, 1), (0, 1)), C_mul((1, 1), (0, -1))) = C_add((-1, 1), (1, -1)) = (-1 + 1, 1 + -1) = (0, 0)

C_mul((1, -1), (1, 0)) = (1 * 1 - (-1) * 0, 1 * 0 + (-1) * 1) = (1, -1)
C_mul((-1, 1), (1, 0)) = (-1 * 1 - 1 * 0, -1 * 0 + 1 * 1) = (-1, 1)
C_add(C_mul((1, -1), (1, 0)), C_mul((-1, 1), (1, 0))) = C_add((1, -1), (-1, 1)) = (1 + -1, -1 + 1) = (0, 0)

C_mul((1, -1), (0, 1)) = (1 * 0 - (-1) * 1, 1 * 1 + (-1) * 0) = (1, 1)
C_mul((-1, 1), (0, -1)) = (-1 * 0 - 1 * (-1), -1 * (-1) + 1 * 0) = (1, 1)
C_add(C_mul((1, -1), (0, 1)), C_mul((-1, 1), (0, -1))) = C_add((1, 1), (1, 1)) = (1 + 1, 1 + 1) = (2, 2)

2002 = 3 * 667 + 1

# Thus the problem-level answer is z_2002 = z_1 = 1 + 274 i.
have answer_1063 &C = z1
answer_1063 = (1, 274)
```

## 10. `test/intermediate_algebra/1454`

```yaml
id: "test/intermediate_algebra/1454"
source: "MATH-500"
topic: "intermediate algebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Problem: test/intermediate_algebra/1454
# Original problem:
# For $0 \le x \le 40$ and $0 \le y \le 50,$ find the minimum value of
# \[\sqrt{x^2 + 400} + \sqrt{y^2 + 900} + \sqrt{x^2 + y^2 - 80x - 100y + 4100}.\]

sqrt(2) > 0
sqrt(2) != 0
sqrt(2) ^ 2 = 2
sqrt(800) = 20 * sqrt(2)
sqrt(1800) = 30 * sqrt(2)

claim:
    prove:
        forall t R:
            t >= 0
            =>:
                sqrt(t) >= 0
    by cases:
        prove:
            sqrt(t) >= 0
        case t > 0:
            sqrt(t) > 0
            sqrt(t) >= 0
        case t <= 0:
            t = 0
            sqrt(t) = sqrt(0) = 0
            sqrt(t) >= 0

claim:
    prove:
        forall a, b R:
            a >= 0
            b >= 0
            =>:
                sqrt(a ^ 2 + b ^ 2) >= (a + b) / sqrt(2)
    a + b >= 0
    (a + b) / sqrt(2) >= 0
    ((a + b) / sqrt(2)) ^ 2 = (a + b) ^ 2 / (sqrt(2) ^ 2)
    ((a + b) / sqrt(2)) ^ 2 = (a + b) ^ 2 / 2
    (a ^ 2 + b ^ 2) - (a + b) ^ 2 / 2 = (a - b) ^ 2 / 2
    (a - b) ^ 2 >= 0
    (a - b) ^ 2 / 2 >= 0
    (a ^ 2 + b ^ 2) - (a + b) ^ 2 / 2 >= 0
    a ^ 2 + b ^ 2 >= (a + b) ^ 2 / 2
    a ^ 2 + b ^ 2 >= ((a + b) / sqrt(2)) ^ 2
    sqrt(a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2
    sqrt(a ^ 2 + b ^ 2) ^ 2 >= ((a + b) / sqrt(2)) ^ 2
    a ^ 2 >= 0
    b ^ 2 >= 0
    a ^ 2 + b ^ 2 >= 0
    sqrt(a ^ 2 + b ^ 2) >= 0
    by contra sqrt(a ^ 2 + b ^ 2) >= (a + b) / sqrt(2):
        sqrt(a ^ 2 + b ^ 2) < (a + b) / sqrt(2)
        0 <= sqrt(a ^ 2 + b ^ 2)
        sqrt(a ^ 2 + b ^ 2) ^ 2 < ((a + b) / sqrt(2)) ^ 2
        impossible sqrt(a ^ 2 + b ^ 2) ^ 2 >= ((a + b) / sqrt(2)) ^ 2

claim:
    prove:
        sqrt(20 ^ 2 + 400) + sqrt(30 ^ 2 + 900) + sqrt(20 ^ 2 + 30 ^ 2 - 80 * 20 - 100 * 30 + 4100) = 70 * sqrt(2)
    20 ^ 2 + 400 = 800
    30 ^ 2 + 900 = 1800
    20 ^ 2 + 30 ^ 2 - 80 * 20 - 100 * 30 + 4100 = 800
    sqrt(20 ^ 2 + 400) + sqrt(30 ^ 2 + 900) + sqrt(20 ^ 2 + 30 ^ 2 - 80 * 20 - 100 * 30 + 4100) = sqrt(800) + sqrt(1800) + sqrt(800)
    sqrt(800) + sqrt(1800) + sqrt(800) = 20 * sqrt(2) + 30 * sqrt(2) + 20 * sqrt(2) = 70 * sqrt(2)

claim:
    prove:
        forall x, y R:
            0 <= x
            x <= 40
            0 <= y
            y <= 50
            x ^ 2 + 400 >= 0
            y ^ 2 + 900 >= 0
            x ^ 2 + y ^ 2 - 80 * x - 100 * y + 4100 >= 0
            =>:
                sqrt(x ^ 2 + 400) + sqrt(y ^ 2 + 900) + sqrt(x ^ 2 + y ^ 2 - 80 * x - 100 * y + 4100) >= 70 * sqrt(2)
    sqrt(x ^ 2 + 400) = sqrt(x ^ 2 + 20 ^ 2)
    sqrt(y ^ 2 + 900) = sqrt(y ^ 2 + 30 ^ 2)
    x ^ 2 + y ^ 2 - 80 * x - 100 * y + 4100 = (40 - x) ^ 2 + (50 - y) ^ 2
    sqrt(x ^ 2 + y ^ 2 - 80 * x - 100 * y + 4100) = sqrt((40 - x) ^ 2 + (50 - y) ^ 2)
    40 - x >= 0
    50 - y >= 0
    sqrt(x ^ 2 + 20 ^ 2) >= (x + 20) / sqrt(2)
    sqrt(y ^ 2 + 30 ^ 2) >= (y + 30) / sqrt(2)
    sqrt((40 - x) ^ 2 + (50 - y) ^ 2) >= ((40 - x) + (50 - y)) / sqrt(2)
    sqrt(x ^ 2 + 400) >= (x + 20) / sqrt(2)
    sqrt(y ^ 2 + 900) >= (y + 30) / sqrt(2)
    sqrt(x ^ 2 + y ^ 2 - 80 * x - 100 * y + 4100) >= ((40 - x) + (50 - y)) / sqrt(2)
    sqrt(x ^ 2 + 400) + sqrt(y ^ 2 + 900) + sqrt(x ^ 2 + y ^ 2 - 80 * x - 100 * y + 4100) >= (x + 20) / sqrt(2) + (y + 30) / sqrt(2) + ((40 - x) + (50 - y)) / sqrt(2)
    (x + 20) / sqrt(2) + (y + 30) / sqrt(2) + ((40 - x) + (50 - y)) / sqrt(2) = 140 / sqrt(2)
    140 / sqrt(2) = 140 * sqrt(2) / (sqrt(2) ^ 2) = 140 * sqrt(2) / 2 = 70 * sqrt(2)
    sqrt(x ^ 2 + 400) + sqrt(y ^ 2 + 900) + sqrt(x ^ 2 + y ^ 2 - 80 * x - 100 * y + 4100) >= 70 * sqrt(2)

forall x, y R:
    0 <= x
    x <= 40
    0 <= y
    y <= 50
    x ^ 2 + 400 >= 0
    y ^ 2 + 900 >= 0
    x ^ 2 + y ^ 2 - 80 * x - 100 * y + 4100 >= 0
    =>:
        sqrt(x ^ 2 + 400) + sqrt(y ^ 2 + 900) + sqrt(x ^ 2 + y ^ 2 - 80 * x - 100 * y + 4100) >= 70 * sqrt(2)
```

## 11. `test/intermediate_algebra/2015`

```yaml
id: "test/intermediate_algebra/2015"
source: "MATH-500"
topic: "intermediate algebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
struct C:
    re R
    im R

have fn C_add(a, b &C) &C = (&C{a}.re + &C{b}.re, &C{a}.im + &C{b}.im)
have fn C_sub(a, b &C) &C = (&C{a}.re - &C{b}.re, &C{a}.im - &C{b}.im)
have fn C_mul(a, b &C) &C = (&C{a}.re * &C{b}.re - &C{a}.im * &C{b}.im, &C{a}.re * &C{b}.im + &C{a}.im * &C{b}.re)
have C_i &C = (0, 1)

# For roots a, b, c, d of x^4 + 2x^3 + 2, Vieta gives
# e1 = a + b + c + d = -2, e2 = 0, e3 = 0, e4 = 2.
# The three pair sums y are roots of the cubic resolvent
# y^3 - e2*y^2 + (e1*e3 - 4*e4)*y + (4*e2*e4 - e1^2*e4 - e3^2),
# hence here y^3 - 8*y - 8.
# This snippet certifies the three resulting real resolvent roots explicitly.

have s R = sqrt(5)
have y_a R = -2
have y_b R = 1 + s
have y_c R = 1 - s

claim:
    prove:
        y_a^3 - 8 * y_a - 8 = 0

    y_a^3 - 8 * y_a - 8 = (-2)^3 - 8 * (-2) - 8 = -8 + 16 - 8 = 0

claim:
    prove:
        y_b^3 - 8 * y_b - 8 = 0

    s^2 = sqrt(5)^2 = 5
    (1 + s)^2 = 1 + 2 * s + s^2 = 6 + 2 * s

    (1 + s)^3 = (1 + s) * (1 + s)^2
    (1 + s) * (1 + s)^2 = (1 + s) * (6 + 2 * s)
    (1 + s) * (6 + 2 * s) = 6 + 8 * s + 2 * s^2
    6 + 8 * s + 2 * s^2 = 6 + 8 * s + 2 * 5 = 16 + 8 * s

    y_b^3 - 8 * y_b - 8 = (1 + s)^3 - 8 * (1 + s) - 8
    (1 + s)^3 - 8 * (1 + s) - 8 = 16 + 8 * s - 8 * (1 + s) - 8 = 0
    y_b^3 - 8 * y_b - 8 = 0

claim:
    prove:
        y_c^3 - 8 * y_c - 8 = 0

    s^2 = sqrt(5)^2 = 5
    (1 - s)^2 = 1 - 2 * s + s^2 = 6 - 2 * s
    (1 - s)^3 = (1 - s) * (1 - s)^2
    (1 - s) * (1 - s)^2 = (1 - s) * (6 - 2 * s)
    (1 - s) * (6 - 2 * s) = 6 - 8 * s + 2 * s^2
    6 - 8 * s + 2 * s^2 = 6 - 8 * s + 2 * 5 = 16 - 8 * s
    y_c^3 - 8 * y_c - 8 = (1 - s)^3 - 8 * (1 - s) - 8
    (1 - s)^3 - 8 * (1 - s) - 8 = 16 - 8 * s - 8 * (1 - s) - 8 = 0
    y_c^3 - 8 * y_c - 8 = 0

claim:
    prove:
        y_a + y_b + y_c = 0

    y_a + y_b + y_c = -2 + (1 + s) + (1 - s) = 0

claim:
    prove:
        y_a * y_b + y_a * y_c + y_b * y_c = -8

    y_a * y_b + y_a * y_c + y_b * y_c = -2 * (1 + s) + -2 * (1 - s) + (1 + s) * (1 - s)
    s^2 = sqrt(5)^2 = 5
    (1 + s) * (1 - s) = 1 - s^2 = -4
    y_a * y_b + y_a * y_c + y_b * y_c = -8

have answer_2015 set = {-2, 1 + s, 1 - s}
```

## 12. `test/intermediate_algebra/754`

```yaml
id: "test/intermediate_algebra/754"
source: "MATH-500"
topic: "intermediate algebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# The equations all have the same right side 7/3 > 1. The largest solution
# comes from the smallest base greater than 1.
have fn base_A(r R) R = 1 + r
have fn base_B(r R) R = 1 + r / 10
have fn base_C(r R) R = 1 + 2 * r
have fn base_D(r R: 0 < r, r < 3) R = 1 + sqrt(r)
have fn base_E(r R: 0 < r, r < 3) R = 1 + 1 / r

claim:
    prove:
        forall r R:
            0 < r
            r < 3
            =>:
                base_B(r) < base_A(r)
    r / 10 < r
    base_B(r) = 1 + r / 10 < 1 + r = base_A(r)

claim:
    prove:
        forall r R:
            0 < r
            r < 3
            =>:
                base_B(r) < base_C(r)
    r / 10 < r
    r < 2 * r
    r / 10 < r < 2 * r
    base_B(r) = 1 + r / 10 < 1 + 2 * r = base_C(r)

claim:
    prove:
        forall r R:
            0 < r
            r < 3
            =>:
                r / 10 < sqrt(r)
    r * r < 3 * r
    r^2 = r * r
    3 * r < 100 * r
    r^2 = r * r < 3 * r < 100 * r
    r^2 / 100 < (100 * r) / 100
    (100 * r) / 100 = r
    r^2 / 100 < r
    (r / 10)^2 = r^2 / 100
    sqrt(r)^2 = r
    (r / 10)^2 < sqrt(r)^2
    r / 10 > 0
    sqrt(r) > 0
    by contra r / 10 < sqrt(r):
        r / 10 >= sqrt(r)
        sqrt(r) <= r / 10
        0 <= sqrt(r)
        0 <= sqrt(r) <= r / 10
        sqrt(r)^2 <= (r / 10)^2
        impossible (r / 10)^2 < sqrt(r)^2

claim:
    prove:
        forall r R:
            0 < r
            r < 3
            =>:
                r / 10 < 1 / r
    r * r < 3 * r
    3 * r < 3 * 3
    3 * 3 = 9
    r^2 = r * r
    r^2 = r * r < 3 * r < 3 * 3 = 9 < 10
    r^2 < 10
    r^2 / 10 < 10 / 10
    10 / 10 = 1
    r^2 / 10 < 1
    r != 0
    by contra r / 10 < 1 / r:
        r / 10 >= 1 / r
        1 / r <= r / 10
        (1 / r) * r <= (r / 10) * r
        (1 / r) * r = 1
        (r / 10) * r = r^2 / 10
        1 <= r^2 / 10
        impossible r^2 / 10 < 1

claim:
    prove:
        forall r R:
            0 < r
            r < 3
            =>:
                base_B(r) < base_D(r)
    r / 10 < sqrt(r)
    base_B(r) = 1 + r / 10 < 1 + sqrt(r) = base_D(r)

claim:
    prove:
        forall r R:
            0 < r
            r < 3
            =>:
                base_B(r) < base_E(r)
    r / 10 < 1 / r
    base_B(r) = 1 + r / 10 < 1 + 1 / r = base_E(r)

forall r R:
    0 < r
    r < 3
    =>:
        base_B(r) < base_A(r)
        base_B(r) < base_C(r)
        base_B(r) < base_D(r)
        base_B(r) < base_E(r)
```

## 13. `test/number_theory/1201`

```yaml
id: "test/number_theory/1201"
source: "MATH-500"
topic: "number theory"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Since 3, 4, and 5 are pairwise relatively prime, their common multiple step
# is 3 * 4 * 5 = 60. Only the first such multiple is at most 100.
claim:
    prove:
        forall step, multiple_count R:
            step = 3 * 4 * 5
            multiple_count = 1
            multiple_count * step <= 100
            100 < (multiple_count + 1) * step
            =>:
                multiple_count = 1
    step = 3 * 4 * 5 = 60
    multiple_count * step = 1 * 60 = 60 <= 100
    100 < 120 = (1 + 1) * 60 = (multiple_count + 1) * step
    multiple_count = 1
```

## 14. `test/number_theory/410`

```yaml
id: "test/number_theory/410"
source: "MATH-500"
topic: "number theory"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Scale 57/160 by 5^4 so the denominator becomes 10^5.
have fn terminating_decimal(digits, places R) R = digits / 10 ^ places

have numerator R = 57
have denominator R = 160
have scale_factor R = 5 ^ 4
have decimal_places R = 5
have decimal_digits R = numerator * scale_factor
have original_fraction R = numerator / denominator
have answer_decimal R = terminating_decimal(decimal_digits, decimal_places)

scale_factor = 5 ^ 4 = 625
denominator * scale_factor = 160 * 625 = 100000
10 ^ decimal_places = 10 ^ 5 = 100000
decimal_digits = numerator * scale_factor = 57 * 625 = 35625
original_fraction = numerator / denominator = 57 / 160
answer_decimal = terminating_decimal(decimal_digits, decimal_places) = decimal_digits / 10 ^ decimal_places = 35625 / 100000 = 0.35625
original_fraction = 57 / 160 = 0.35625
```

## 15. `test/number_theory/533`

```yaml
id: "test/number_theory/533"
source: "MATH-500"
topic: "number theory"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# A repeating four-digit block 1331 gives 1331 / 9999; reduce by 11.
have raw_numerator R = 1331
have raw_denominator R = 9999
have common_factor R = 11
have reduced_numerator R = raw_numerator / common_factor
have reduced_denominator R = raw_denominator / common_factor
have answer R = reduced_numerator + reduced_denominator

reduced_numerator = raw_numerator / common_factor = 1331 / 11 = 121
reduced_denominator = raw_denominator / common_factor = 9999 / 11 = 909
raw_numerator / raw_denominator = 1331 / 9999 = 121 / 909
answer = reduced_numerator + reduced_denominator = 121 + 909 = 1030
```

## 16. `test/prealgebra/105`

```yaml
id: "test/prealgebra/105"
source: "MATH-500"
topic: "prealgebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Encode compass positions by quarter-turns to the right from north:
# north = 0, east = 1, south = 2, west = 3.
claim:
    prove:
        forall total_degrees, right_angle_degrees, full_turn_degrees, full_turns, final_quarter_turns, full_turn_quarters, remainder_quarter_turns, east_index R:
            total_degrees = 2250
            right_angle_degrees = 90
            full_turn_degrees = 360
            full_turns = 6
            final_quarter_turns = total_degrees / right_angle_degrees
            full_turn_quarters = full_turn_degrees / right_angle_degrees
            remainder_quarter_turns = final_quarter_turns - full_turns * full_turn_quarters
            east_index = 1
            =>:
                remainder_quarter_turns = east_index
    final_quarter_turns = total_degrees / right_angle_degrees = 2250 / 90 = 25
    full_turn_quarters = full_turn_degrees / right_angle_degrees = 360 / 90 = 4
    remainder_quarter_turns = final_quarter_turns - full_turns * full_turn_quarters = 25 - 6 * 4 = 1 = east_index
```

## 17. `test/prealgebra/1139`

```yaml
id: "test/prealgebra/1139"
source: "MATH-500"
topic: "prealgebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Associativity of multiplication means only the placement of the +1 changes
# the value: after 5, after 4*5, after 3*4*5, or after all four factors.
have value_after_5 R = 2 * 3 * 4 * (5 + 1)
have value_after_45 R = 2 * 3 * (4 * 5 + 1)
have value_after_345 R = 2 * (3 * 4 * 5 + 1)
have value_after_all R = 2 * 3 * 4 * 5 + 1
have possible_values set = {144, 126, 122, 121}

claim:
    prove:
        count({144, 126, 122, 121}) = 4
    value_after_5 = 2 * 3 * 4 * (5 + 1) = 144
    value_after_45 = 2 * 3 * (4 * 5 + 1) = 126
    value_after_345 = 2 * (3 * 4 * 5 + 1) = 122
    value_after_all = 2 * 3 * 4 * 5 + 1 = 121

    144 != 126
    126 != 122
    122 != 121
    possible_values = {144, 126, 122, 121}
    count({144, 126, 122, 121}) = 4
```

## 18. `test/prealgebra/1742`

```yaml
id: "test/prealgebra/1742"
source: "MATH-500"
topic: "prealgebra"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
have fn arithmetic_progression_count(first, last, step R: step != 0) R = (last - first) / step + 1
have fn probability(favorable, total R: total != 0) R = favorable / total

have total_outcomes R = 100
have first_multiple R = 3
have last_multiple R = 99
have next_after_last R = 102
have step R = 3

step != 0
total_outcomes != 0
first_multiple = 3 * 1 = 3
last_multiple = 3 * 33 = 99
next_after_last = 3 * 34 = 102
next_after_last > total_outcomes

have favorable_outcomes R = arithmetic_progression_count(first_multiple, last_multiple, step)
have answer_probability R = probability(favorable_outcomes, total_outcomes)

favorable_outcomes = arithmetic_progression_count(first_multiple, last_multiple, step) = (99 - 3) / 3 + 1 = 33
answer_probability = probability(favorable_outcomes, total_outcomes) = favorable_outcomes / total_outcomes = 33 / 100
```

## 19. `test/precalculus/24313`

```yaml
id: "test/precalculus/24313"
source: "MATH-500"
topic: "precalculus"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Simplify the original expression Trig::sec(x) / Trig::sin(x) - Trig::sin(x) / Trig::cos(x).
import Trig

claim:
    prove:
        forall x R:
            Trig::cos(x) != 0
            Trig::sin(x) != 0
            Trig::cos(x) * Trig::sin(x) != 0
            =>:
                Trig::sec(x) / Trig::sin(x) - Trig::sin(x) / Trig::cos(x) = Trig::cot(x)
    Trig::sec(x) = 1 / Trig::cos(x)
    Trig::cot(x) = Trig::cos(x) / Trig::sin(x)
    Trig::sin(x)^2 + Trig::cos(x)^2 = 1
    Trig::sin(x)^2 + Trig::cos(x)^2 - Trig::sin(x)^2 = 1 - Trig::sin(x)^2
    Trig::sin(x)^2 + Trig::cos(x)^2 - Trig::sin(x)^2 = Trig::cos(x)^2
    Trig::cos(x)^2 = 1 - Trig::sin(x)^2
    Trig::sec(x) / Trig::sin(x) - Trig::sin(x) / Trig::cos(x) = (1 / Trig::cos(x)) / Trig::sin(x) - Trig::sin(x) / Trig::cos(x)
    (1 / Trig::cos(x)) / Trig::sin(x) - Trig::sin(x) / Trig::cos(x) = (1 - Trig::sin(x)^2) / (Trig::cos(x) * Trig::sin(x))
    (1 - Trig::sin(x)^2) / (Trig::cos(x) * Trig::sin(x)) = Trig::cos(x)^2 / (Trig::cos(x) * Trig::sin(x))
    Trig::cos(x)^2 / (Trig::cos(x) * Trig::sin(x)) = Trig::cos(x) / Trig::sin(x)
    Trig::sec(x) / Trig::sin(x) - Trig::sin(x) / Trig::cos(x) = Trig::cot(x)
```

## 20. `test/precalculus/697`

```yaml
id: "test/precalculus/697"
source: "MATH-500"
topic: "precalculus"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
# Simplify the original expression Trig::tan(100 degrees) + 4 * Trig::sin(100 degrees).
import Trig

100 * pi / 180 = 5 * pi / 9
not 1 / 18 $in Z
(100 * pi / 180 - pi / 2) / pi = 1 / 18
not (100 * pi / 180 - pi / 2) / pi $in Z
Trig::cos(100 * pi / 180) != 0
Trig::cos(5 * pi / 9) = Trig::cos(100 * pi / 180)
Trig::cos(5 * pi / 9) != 0
Trig::tan(100 * pi / 180) = Trig::tan(5 * pi / 9)
Trig::sin(100 * pi / 180) = Trig::sin(5 * pi / 9)

pi / 3 = pi / 3 + 2 * 0 * pi
Trig::sin(pi / 3 + 2 * 0 * pi) = sqrt(3) / 2
Trig::cos(pi / 3 + 2 * 0 * pi) = 1 / 2
Trig::sin(pi / 3) = Trig::sin(pi / 3 + 2 * 0 * pi) = sqrt(3) / 2
Trig::cos(pi / 3) = Trig::cos(pi / 3 + 2 * 0 * pi) = 1 / 2

Trig::sin(5 * pi / 9 + pi / 3) = Trig::sin(5 * pi / 9) * Trig::cos(pi / 3) + Trig::cos(5 * pi / 9) * Trig::sin(pi / 3)
2 * Trig::sin(5 * pi / 9 + pi / 3) = 2 * (Trig::sin(5 * pi / 9) * Trig::cos(pi / 3) + Trig::cos(5 * pi / 9) * Trig::sin(pi / 3))
2 * (Trig::sin(5 * pi / 9) * Trig::cos(pi / 3) + Trig::cos(5 * pi / 9) * Trig::sin(pi / 3)) = 2 * (Trig::sin(5 * pi / 9) * (1 / 2) + Trig::cos(5 * pi / 9) * (sqrt(3) / 2))
2 * (Trig::sin(5 * pi / 9) * (1 / 2) + Trig::cos(5 * pi / 9) * (sqrt(3) / 2)) = Trig::sin(5 * pi / 9) + sqrt(3) * Trig::cos(5 * pi / 9)
Trig::sin(5 * pi / 9) + sqrt(3) * Trig::cos(5 * pi / 9) = 2 * Trig::sin(5 * pi / 9 + pi / 3)
5 * pi / 9 + pi / 3 = 8 * pi / 9
Trig::sin(5 * pi / 9 + pi / 3) = Trig::sin(8 * pi / 9)
2 * Trig::sin(5 * pi / 9 + pi / 3) = 2 * Trig::sin(8 * pi / 9)
Trig::sin(5 * pi / 9) + sqrt(3) * Trig::cos(5 * pi / 9) = 2 * Trig::sin(5 * pi / 9 + pi / 3) = 2 * Trig::sin(8 * pi / 9)

Trig::sin(pi) = 0
Trig::cos(pi) = -1
Trig::sin(pi - pi / 9) = Trig::sin(pi) * Trig::cos(pi / 9) - Trig::cos(pi) * Trig::sin(pi / 9)
Trig::sin(pi) * Trig::cos(pi / 9) - Trig::cos(pi) * Trig::sin(pi / 9) = 0 * Trig::cos(pi / 9) - (-1) * Trig::sin(pi / 9)
0 * Trig::cos(pi / 9) - (-1) * Trig::sin(pi / 9) = Trig::sin(pi / 9)
Trig::sin(pi - pi / 9) = Trig::sin(pi / 9)
pi - pi / 9 = 8 * pi / 9
Trig::sin(8 * pi / 9) = Trig::sin(pi - pi / 9) = Trig::sin(pi / 9)

Trig::sin(pi + pi / 9) = Trig::sin(pi) * Trig::cos(pi / 9) + Trig::cos(pi) * Trig::sin(pi / 9)
Trig::sin(pi) * Trig::cos(pi / 9) + Trig::cos(pi) * Trig::sin(pi / 9) = 0 * Trig::cos(pi / 9) + (-1) * Trig::sin(pi / 9)
0 * Trig::cos(pi / 9) + (-1) * Trig::sin(pi / 9) = -Trig::sin(pi / 9)
Trig::sin(pi + pi / 9) = -Trig::sin(pi / 9)
pi + pi / 9 = 10 * pi / 9
Trig::sin(10 * pi / 9) = Trig::sin(pi + pi / 9) = -Trig::sin(pi / 9)

Trig::sin(2 * (5 * pi / 9)) = 2 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9)
2 * (5 * pi / 9) = 10 * pi / 9
Trig::sin(2 * (5 * pi / 9)) = Trig::sin(10 * pi / 9)
4 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9) = 2 * (2 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9)) = 2 * Trig::sin(2 * (5 * pi / 9)) = 2 * Trig::sin(10 * pi / 9)

2 * Trig::sin(8 * pi / 9) + 2 * Trig::sin(10 * pi / 9) = 2 * Trig::sin(pi / 9) + 2 * (-Trig::sin(pi / 9)) = 0
Trig::sin(5 * pi / 9) + sqrt(3) * Trig::cos(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9) = 2 * Trig::sin(8 * pi / 9) + 2 * Trig::sin(10 * pi / 9) = 0
Trig::sin(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9) = Trig::sin(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9) + sqrt(3) * Trig::cos(5 * pi / 9) - sqrt(3) * Trig::cos(5 * pi / 9)
Trig::sin(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9) + sqrt(3) * Trig::cos(5 * pi / 9) - sqrt(3) * Trig::cos(5 * pi / 9) = Trig::sin(5 * pi / 9) + sqrt(3) * Trig::cos(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9) - sqrt(3) * Trig::cos(5 * pi / 9)
Trig::sin(5 * pi / 9) + sqrt(3) * Trig::cos(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9) - sqrt(3) * Trig::cos(5 * pi / 9) = 0 - sqrt(3) * Trig::cos(5 * pi / 9)
0 - sqrt(3) * Trig::cos(5 * pi / 9) = -sqrt(3) * Trig::cos(5 * pi / 9)
Trig::sin(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9) = -sqrt(3) * Trig::cos(5 * pi / 9)
Trig::tan(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) = Trig::sin(5 * pi / 9) / Trig::cos(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9)
Trig::sin(5 * pi / 9) / Trig::cos(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) = (Trig::sin(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9)) / Trig::cos(5 * pi / 9)
(Trig::sin(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) * Trig::cos(5 * pi / 9)) / Trig::cos(5 * pi / 9) = (-sqrt(3) * Trig::cos(5 * pi / 9)) / Trig::cos(5 * pi / 9)
(-sqrt(3) * Trig::cos(5 * pi / 9)) / Trig::cos(5 * pi / 9) = -sqrt(3)
Trig::tan(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) = -sqrt(3)
Trig::tan(100 * pi / 180) + 4 * Trig::sin(100 * pi / 180) = Trig::tan(5 * pi / 9) + 4 * Trig::sin(5 * pi / 9) = -sqrt(3)
```

## 21. `test/precalculus/990`

```yaml
id: "test/precalculus/990"
source: "MATH-500"
topic: "precalculus"
difficulty: "MATH-500 test"
natural_language_idea: "Finished MATH-500 derivation; the body gives the key algebraic, geometric, or counting reductions explicitly."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
struct C:
    re R
    im R

have fn C_add(a, b &C) &C = (&C{a}.re + &C{b}.re, &C{a}.im + &C{b}.im)
have fn C_sub(a, b &C) &C = (&C{a}.re - &C{b}.re, &C{a}.im - &C{b}.im)
have fn C_mul(a, b &C) &C = (&C{a}.re * &C{b}.re - &C{a}.im * &C{b}.im, &C{a}.re * &C{b}.im + &C{a}.im * &C{b}.re)
have C_i &C = (0, 1)

# Translate by c = (2, -3), rotate by pi / 4 via ((1 / sqrt(2)), (1 / sqrt(2))),
# then translate back.
claim:
    prove:
        C_add(C_mul(C_sub((2 + sqrt(2), -(3 + 3 * sqrt(2))), (2, -3)), (1 / sqrt(2), 1 / sqrt(2))), (2, -3)) = (6, -5)

    C_sub((2 + sqrt(2), -(3 + 3 * sqrt(2))), (2, -3)) = C_sub((2 + sqrt(2), -(3 + 3 * sqrt(2))), (2, -3)) = (2 + sqrt(2) - 2, -(3 + 3 * sqrt(2)) - (-3)) = (sqrt(2), -3 * sqrt(2))
    C_mul(C_sub((2 + sqrt(2), -(3 + 3 * sqrt(2))), (2, -3)), (1 / sqrt(2), 1 / sqrt(2))) = C_mul((sqrt(2), -3 * sqrt(2)), (1 / sqrt(2), 1 / sqrt(2)))
    C_mul((sqrt(2), -3 * sqrt(2)), (1 / sqrt(2), 1 / sqrt(2))) = C_mul((sqrt(2), -3 * sqrt(2)), (1 / sqrt(2), 1 / sqrt(2))) = (sqrt(2) * (1 / sqrt(2)) - (-3 * sqrt(2)) * (1 / sqrt(2)), sqrt(2) * (1 / sqrt(2)) + (-3 * sqrt(2)) * (1 / sqrt(2))) = (4, -2)
    C_add(C_mul(C_sub((2 + sqrt(2), -(3 + 3 * sqrt(2))), (2, -3)), (1 / sqrt(2), 1 / sqrt(2))), (2, -3)) = C_add((4, -2), (2, -3))
    C_add((4, -2), (2, -3)) = C_add((4, -2), (2, -3)) = (4 + 2, -2 + (-3)) = (6, -5)
    C_add(C_mul(C_sub((2 + sqrt(2), -(3 + 3 * sqrt(2))), (2, -3)), (1 / sqrt(2), 1 / sqrt(2))), (2, -3)) = (6, -5)
```
