# Tao Analysis I

Small checked Analysis I slices using Litex-native natural numbers, sets, functions, rationals, Cauchy-style closeness, and limits.

Each example below is an independent checked Litex snippet. The metadata record keeps the dataset translation fields next to the runnable code.

## 1. `chap2_addition_cancellation`

```yaml
id: "chap2_addition_cancellation"
source: "Tao Analysis I"
topic: "natural-number addition"
difficulty: "chapter 2"
natural_language_idea: "Cancel a common natural-number summand by subtracting it from both sides."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Nat

forall a, b, c N:
    a + b = a + c
    =>:
        b = (a + b) - a
        (a + b) - a = (a + c) - a
        (a + c) - a = c
        b = c
```

## 2. `chap2_arbitrarily_large_nat`

```yaml
id: "chap2_arbitrarily_large_nat"
source: "Tao Analysis I"
topic: "natural-number order"
difficulty: "chapter 2"
natural_language_idea: "Use the successor as an explicit natural number larger than n."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Nat

have fn succ(n N) N_pos = n + 1

claim:
    prove:
        forall n N:
            exist m N st {m > n}
    succ(n) = n + 1
    n + 1 > n
    succ(n) > n
    witness exist m N st {m > n} from succ(n):
        succ(n) $in N
        succ(n) > n
```

## 3. `chap2_positive_sum`

```yaml
id: "chap2_positive_sum"
source: "Tao Analysis I"
topic: "natural-number positivity"
difficulty: "chapter 2"
natural_language_idea: "A positive natural plus a natural number remains positive."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Nat

forall a N_pos, b N:
    a + b $in N_pos
    a + b != 0

forall a N_pos, b N:
    b + a $in N_pos
    b + a != 0
```

## 4. `chap2_successor_injective`

```yaml
id: "chap2_successor_injective"
source: "Tao Analysis I"
topic: "natural numbers"
difficulty: "chapter 2"
natural_language_idea: "Show successor injectivity by subtracting one from both sides."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Nat

have fn succ(n N) N_pos = n + 1

forall n, m N:
    succ(n) = succ(m)
    =>:
        succ(n) = n + 1
        succ(m) = m + 1
        n + 1 = m + 1
        n = (n + 1) - 1
        (n + 1) - 1 = (m + 1) - 1
        (m + 1) - 1 = m
        n = m
```

## 5. `chap2_successor_numerals`

```yaml
id: "chap2_successor_numerals"
source: "Tao Analysis I"
topic: "natural numbers"
difficulty: "chapter 2"
natural_language_idea: "Use Litex natural numbers and successor notation to check the first numerals."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Nat

have fn succ(n N) N_pos = n + 1
succ(0) = 1
succ(1) = 2
succ(2) = 3
succ(3) = 4
3 $in N
4 != 0
```

## 6. `chap2_unique_predecessor`

```yaml
id: "chap2_unique_predecessor"
source: "Tao Analysis I"
topic: "natural numbers"
difficulty: "chapter 2"
natural_language_idea: "A positive natural has the unique predecessor obtained by subtracting one."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Nat

have fn succ(n N) N_pos = n + 1

forall n, m N:
    succ(n) = succ(m)
    =>:
        succ(n) = n + 1
        succ(m) = m + 1
        n + 1 = m + 1
        n = (n + 1) - 1
        (n + 1) - 1 = (m + 1) - 1
        (m + 1) - 1 = m
        n = m

claim:
    prove:
        forall a N_pos:
            exist! b N st {succ(b) = a}
    a >= 1
    a - 1 >= 0
    a - 1 $in Z
    a - 1 $in N
    witness exist b N st {succ(b) = a} from a - 1:
        succ(a - 1) = (a - 1) + 1
        (a - 1) + 1 = a
        succ(a - 1) = a
    forall b1, b2 N:
        succ(b1) = a
        succ(b2) = a
        =>:
            succ(b1) = succ(b2)
            b1 = b2
    exist! b N st {succ(b) = a}
```

## 7. `chap2_zero_sum`

```yaml
id: "chap2_zero_sum"
source: "Tao Analysis I"
topic: "natural-number order"
difficulty: "chapter 2"
natural_language_idea: "If a sum of natural numbers is zero, each summand is squeezed to zero."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Nat

forall a, b N:
    a + b = 0
    =>:
        0 <= a <= a + b
        a <= 0
        a = 0
        0 <= b <= a + b
        b <= 0
        b = 0
```

## 8. `chap3_composition_order`

```yaml
id: "chap3_composition_order"
source: "Tao Analysis I"
topic: "functions"
difficulty: "chapter 3"
natural_language_idea: "Concrete function composition calculations show that the two orders differ."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Nat

have fn double_nat(n N) N = 2 * n
have fn add3_nat(n N) N = n + 3
have fn add3_after_double(n N) N = add3_nat(double_nat(n))
have fn double_after_add3(n N) N = double_nat(add3_nat(n))

double_nat(1) = 2
add3_nat(2) = 5
add3_after_double(1) = add3_nat(double_nat(1)) = add3_nat(2) = 5
add3_nat(1) = 4
double_nat(4) = 8
double_after_add3(1) = double_nat(add3_nat(1)) = double_nat(4) = 8
add3_after_double(1) != double_after_add3(1)
```

## 9. `chap3_finite_set_extensionality`

```yaml
id: "chap3_finite_set_extensionality"
source: "Tao Analysis I"
topic: "finite sets"
difficulty: "chapter 3"
natural_language_idea: "Prove equality of two displayed finite sets by membership in both directions."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
by extension:
    prove:
        {3, 8, 5, 2} = {2, 3, 5, 8}
    by enumerate finite_set:
        prove:
            forall x {3, 8, 5, 2}:
                x $in {2, 3, 5, 8}
    by enumerate finite_set:
        prove:
            forall y {2, 3, 5, 8}:
                y $in {3, 8, 5, 2}
```

## 10. `chap3_function_equality`

```yaml
id: "chap3_function_equality"
source: "Tao Analysis I"
topic: "functions"
difficulty: "chapter 3"
natural_language_idea: "Check two polynomial definitions pointwise, then use function equality."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
have fn poly1(x R) R = x^2 + 2 * x + 1
have fn poly2(x R) R = (x + 1)^2

forall x R:
    poly1(x) = poly2(x)

$fn_eq(poly1, poly2)
```

## 11. `chap3_subset_antisymmetry`

```yaml
id: "chap3_subset_antisymmetry"
source: "Tao Analysis I"
topic: "subsets"
difficulty: "chapter 3"
natural_language_idea: "Use extensionality to turn mutual subset containment into set equality."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
claim:
    prove:
        forall A, B set:
            A $subset B
            B $subset A
            =>:
                A = B
    by extension:
        prove:
            A = B
```

## 12. `chap3_subset_example`

```yaml
id: "chap3_subset_example"
source: "Tao Analysis I"
topic: "subsets"
difficulty: "chapter 3"
natural_language_idea: "Enumerate a finite subset and then record proper containment."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
by enumerate finite_set:
    prove:
        forall x {1, 2, 4}:
            x $in {1, 2, 3, 4, 5}

{1, 2, 4} $subset {1, 2, 3, 4, 5}
{1, 2, 4} != {1, 2, 3, 4, 5}
```

## 13. `chap3_successor_bijection`

```yaml
id: "chap3_successor_bijection"
source: "Tao Analysis I"
topic: "functions"
difficulty: "chapter 3"
natural_language_idea: "Show successor is injective and surjective from N onto positive naturals."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Nat

have fn succ(n N) N_pos = n + 1

prop injective_fn(S, T set, f fn(x S) T):
    forall x1, x2 S:
        f(x1) = f(x2)
        =>:
            x1 = x2

prop surjective_fn(S, T set, f fn(x S) T):
    forall y T:
        exist x S st {y = f(x)}

prop bijective_fn(S, T set, f fn(x S) T):
    $injective_fn(S, T, f)
    $surjective_fn(S, T, f)

claim:
    prove:
        $injective_fn(N, N_pos, succ)
    forall x1, x2 N:
        succ(x1) = succ(x2)
        =>:
            succ(x1) = x1 + 1
            succ(x2) = x2 + 1
            x1 + 1 = x2 + 1
            x1 = (x1 + 1) - 1
            (x1 + 1) - 1 = (x2 + 1) - 1
            (x2 + 1) - 1 = x2
            x1 = x2

claim:
    prove:
        $surjective_fn(N, N_pos, succ)
    claim:
        prove:
            forall y N_pos:
                exist x N st {y = succ(x)}
        y - 1 $in N
        witness exist x N st {y = succ(x)} from y - 1:
            succ(y - 1) = (y - 1) + 1
            (y - 1) + 1 = y
            y = succ(y - 1)
    $surjective_fn(N, N_pos, succ)

$bijective_fn(N, N_pos, succ)
```

## 14. `chap4_integer_cancellation`

```yaml
id: "chap4_integer_cancellation"
source: "Tao Analysis I"
topic: "integers"
difficulty: "chapter 4"
natural_language_idea: "Cancel a nonzero integer factor by dividing both sides."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Int

forall a, b, c Z:
    a * c = b * c
    c != 0
    =>:
        a = (a * c) / c
        (a * c) / c = (b * c) / c
        (b * c) / c = b
        a = b
```

## 15. `chap4_integer_order_translation`

```yaml
id: "chap4_integer_order_translation"
source: "Tao Analysis I"
topic: "integers"
difficulty: "chapter 4"
natural_language_idea: "Translate an integer inequality through addition by the same integer."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Int

forall a, b, c Z:
    a > b
    =>:
        a - b > 0
        (a + c) - (b + c) = a - b
        (a + c) - (b + c) > 0
        a + c > b + c
```

## 16. `chap4_rational_abs_positive`

```yaml
id: "chap4_rational_abs_positive"
source: "Tao Analysis I"
topic: "rational metric"
difficulty: "chapter 4"
natural_language_idea: "A nonzero rational has strictly positive absolute value by trichotomy."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Rat
import Real

claim:
    prove:
        forall x Q:
            x != 0
            =>:
                abs(x) > 0
    abs(x) >= 0
    abs(x) > 0 or abs(x) = 0 or abs(x) < 0
    by cases:
        prove:
            abs(x) > 0
        case abs(x) > 0:
            abs(x) > 0
        case abs(x) = 0:
            x = 0
            impossible x != 0
        case abs(x) < 0:
            impossible abs(x) >= 0
```

## 17. `chap4_rational_distance_symmetry`

```yaml
id: "chap4_rational_distance_symmetry"
source: "Tao Analysis I"
topic: "rational metric"
difficulty: "chapter 4"
natural_language_idea: "Expand rational distance to absolute value and prove symmetry by inequalities both ways."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Rat
import Real

have fn dist_Q(x, y Q) R = abs(x - y)

forall x, y Q:
    dist_Q(x, y) = abs(x - y)
    dist_Q(y, x) = abs(y - x)
    -(y - x) <= abs(y - x)
    x - y = -(y - x)
    x - y <= abs(y - x)
    y - x <= abs(y - x)
    -(x - y) = y - x
    -(x - y) <= abs(y - x)
    abs(x - y) <= abs(y - x)
    -(x - y) <= abs(x - y)
    y - x = -(x - y)
    y - x <= abs(x - y)
    x - y <= abs(x - y)
    -(y - x) = x - y
    -(y - x) <= abs(x - y)
    abs(y - x) <= abs(x - y)
    abs(x - y) = abs(y - x)
    dist_Q(x, y) = dist_Q(y, x)
```

## 18. `chap4_rational_reciprocal`

```yaml
id: "chap4_rational_reciprocal"
source: "Tao Analysis I"
topic: "rationals"
difficulty: "chapter 4"
natural_language_idea: "Use the nonzero rational reciprocal interface."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Rat

forall x Q_nz:
    x * (1 / x) = 1
    (1 / x) * x = 1
```

## 19. `chap5_close_Q_symmetric`

```yaml
id: "chap5_close_Q_symmetric"
source: "Tao Analysis I"
topic: "Cauchy sequences"
difficulty: "chapter 5"
natural_language_idea: "Package rational closeness and prove that it is symmetric."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Rat
import Real

have fn dist_Q(x, y Q) R = abs(x - y)

prop close_Q(epsilon Q_pos, x, y Q):
    dist_Q(x, y) <= epsilon

forall x, y Q:
    dist_Q(x, y) = abs(x - y)
    dist_Q(y, x) = abs(y - x)
    -(y - x) <= abs(y - x)
    x - y = -(y - x)
    x - y <= abs(y - x)
    y - x <= abs(y - x)
    -(x - y) = y - x
    -(x - y) <= abs(y - x)
    abs(x - y) <= abs(y - x)
    -(x - y) <= abs(x - y)
    y - x = -(x - y)
    y - x <= abs(x - y)
    x - y <= abs(x - y)
    -(y - x) = x - y
    -(y - x) <= abs(x - y)
    abs(y - x) <= abs(x - y)
    abs(x - y) = abs(y - x)
    dist_Q(x, y) = dist_Q(y, x)

thm close_Q_symmetric:
    prove:
        forall epsilon Q_pos, x, y Q:
            $close_Q(epsilon, x, y)
            =>:
                $close_Q(epsilon, y, x)
    dist_Q(x, y) <= epsilon
    dist_Q(y, x) = dist_Q(x, y)
    dist_Q(y, x) <= epsilon
    $close_Q(epsilon, y, x)
```

## 20. `chap9_constant_function_limit`

```yaml
id: "chap9_constant_function_limit"
source: "Tao Analysis I"
topic: "function limits"
difficulty: "chapter 9"
natural_language_idea: "Use epsilon/delta witnesses to prove the constant real function has limit c."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Real

have fn dist_R(x, y R) R = abs(x - y)

prop close_R(epsilon R_pos, x, y R):
    dist_R(x, y) <= epsilon

forall epsilon R_pos, x R:
    x - x = 0
    dist_R(x, x) = abs(x - x) = abs(0) = 0
    0 <= epsilon
    $close_R(epsilon, x, x)

prop epsilon_adherent_to_R_subset(X set, x R, epsilon R_pos):
    X $subset R
    exist y X st {$close_R(epsilon, x, y)}

prop adherent_point_R(X set, x R):
    X $subset R
    forall epsilon R_pos:
        $epsilon_adherent_to_R_subset(X, x, epsilon)

prop local_close_witness_R(X, E set, f fn(x X) R, L, x0 R, epsilon, delta R_pos):
    E $subset X
    E $subset R
    forall x E:
        dist_R(x, x0) < delta
        =>:
            $close_R(epsilon, f(x), L)

prop locally_close_to_R(X, E set, f fn(x X) R, L, x0 R, epsilon R_pos):
    exist delta R_pos st {$local_close_witness_R(X, E, f, L, x0, epsilon, delta)}

prop function_limit_at_R(X, E set, f fn(x X) R, x0, L R):
    E $subset X
    E $subset R
    $adherent_point_R(E, x0)
    forall epsilon R_pos:
        $locally_close_to_R(X, E, f, L, x0, epsilon)

claim:
    prove:
        forall c, x0 R:
            $function_limit_at_R(R, R, '(x R) R {c}, x0, c)
    claim:
        prove:
            $adherent_point_R(R, x0)
        claim:
            prove:
                forall epsilon R_pos:
                    $epsilon_adherent_to_R_subset(R, x0, epsilon)
            witness exist y R st {$close_R(epsilon, x0, y)} from x0:
                $close_R(epsilon, x0, x0)
            $epsilon_adherent_to_R_subset(R, x0, epsilon)
        $adherent_point_R(R, x0)
    claim:
        prove:
            forall epsilon R_pos:
                $locally_close_to_R(R, R, '(x R) R {c}, c, x0, epsilon)
        witness exist delta R_pos st {$local_close_witness_R(R, R, '(x R) R {c}, c, x0, epsilon, delta)} from 1:
            forall x R:
                dist_R(x, x0) < 1
                =>:
                    '(x R) R {c}(x) = c
                    $close_R(epsilon, c, c)
                    $close_R(epsilon, '(x R) R {c}(x), c)
            $local_close_witness_R(R, R, '(x R) R {c}, c, x0, epsilon, 1)
        $locally_close_to_R(R, R, '(x R) R {c}, c, x0, epsilon)
    $function_limit_at_R(R, R, '(x R) R {c}, x0, c)
```
