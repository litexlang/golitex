# High School Book

High-school textbook snippets covering equality, trigonometry, coordinate geometry, derivatives, and extrema records.

Each example below is an independent checked Litex snippet. The metadata record keeps the dataset translation fields next to the runnable code.

## 1. `optional-1/0034`

```yaml
id: "optional-1/0034"
source: "High School Book"
topic: "coordinate geometry"
difficulty: "optional"
natural_language_idea: "Represent the line through a point with slope 4/3 as a set of ordered pairs."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Trig

have answer_0034 set = { p cart(R, R) : p[2] - 5 = 4 / 3 * (p[1] - 3) }
```

## 2. `optional-2/0008`

```yaml
id: "optional-2/0008"
source: "High School Book"
topic: "average rate of change"
difficulty: "optional"
natural_language_idea: "Compute the average change rate of a circle circumference formula and simplify to 2*pi."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
have fn average_change_rate(a R, h R_pos) R = (2 * pi * (a + h) - 2 * pi * a) / h
forall a R, h R_pos:
    average_change_rate(a, h) = 2 * pi
```

## 3. `optional-2/0030`

```yaml
id: "optional-2/0030"
source: "High School Book"
topic: "average rate of change"
difficulty: "optional"
natural_language_idea: "Compute the average change rate of area pi*x^2 over an increment h."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
have fn average_change_rate(a R, h R_pos) R = (pi * (a + h)^2 - pi * a^2) / h
forall a R, h R_pos:
    average_change_rate(a, h) = pi * (2 * a + h)
```

## 4. `optional-2/0069`

```yaml
id: "optional-2/0069"
source: "High School Book"
topic: "derivative formulas"
difficulty: "optional"
natural_language_idea: "Record derivative functions for a quadratic and a double-angle sine expression."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Trig

have fn f_prime_1(x R) R = 8 * x - 12
have fn f_prime_2(x R) R = 2 * Trig::cos(2 * x)
```

## 5. `optional-2/0105`

```yaml
id: "optional-2/0105"
source: "High School Book"
topic: "function extrema"
difficulty: "optional"
natural_language_idea: "Record the maximum and minimum witnesses and values for a textbook extrema exercise."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
have x_of_max R = 3
have max_value R = 8
have x_of_min R = 7
have min_value R = -8
```

## 6. `required-1/0085`

```yaml
id: "required-1/0085"
source: "High School Book"
topic: "equality algebra"
difficulty: "required"
natural_language_idea: "Use equality substitution to multiply two equalities side by side."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
forall a, b, c, d R:
    a = b
    c = d
    =>:
        a * c = b * d
```

## 7. `required-1/0086`

```yaml
id: "required-1/0086"
source: "High School Book"
topic: "equality algebra"
difficulty: "required"
natural_language_idea: "Use equality substitution to add two equalities side by side."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
forall a, b, c, d R:
    a = b
    c = d
    =>:
        a + c = b + d
```

## 8. `required-1/0087`

```yaml
id: "required-1/0087"
source: "High School Book"
topic: "equality algebra"
difficulty: "required"
natural_language_idea: "Use equality substitution to multiply equal quantities."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
forall a, b, c, d R:
    a = b
    c = d
    =>:
        a * c = b * d
```

## 9. `required-1/0088`

```yaml
id: "required-1/0088"
source: "High School Book"
topic: "reciprocal equality"
difficulty: "required"
natural_language_idea: "If equal nonzero real numbers are reciprocated, their reciprocals are equal."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
forall a, b R:
    a = b
    a != 0
    =>:
        1 / a = 1 / b
```

## 10. `required-1/0089`

```yaml
id: "required-1/0089"
source: "High School Book"
topic: "power equality"
difficulty: "required"
natural_language_idea: "Raise equal real numbers to the same positive natural power."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
forall a, b R, n N_pos:
    a = b
    =>:
        a ^ n = b ^ n
```

## 11. `required-1/0094`

```yaml
id: "required-1/0094"
source: "High School Book"
topic: "zero product"
difficulty: "required"
natural_language_idea: "Use the real zero-product property."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
forall a, b R:
    a * b = 0
    =>:
        a = 0 or b = 0
```

## 12. `required-1/0096`

```yaml
id: "required-1/0096"
source: "High School Book"
topic: "zero product"
difficulty: "required"
natural_language_idea: "Use the real zero-product property in a repeated textbook slot."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
forall a, b R:
    a * b = 0
    =>:
        a = 0 or b = 0
```

## 13. `required-2/0018`

```yaml
id: "required-2/0018"
source: "High School Book"
topic: "angle conversion"
difficulty: "required"
natural_language_idea: "Convert representative degree measures into radians and package the answer tuple."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
15 * pi / 180 = pi / 12
-108 * pi / 180 = -3 * pi / 5
22.5 * pi / 180 = pi / 8
have answer set = (pi / 12, -3 * pi / 5, pi / 8)
```

## 14. `required-2/0025`

```yaml
id: "required-2/0025"
source: "High School Book"
topic: "special-angle trigonometry"
difficulty: "required"
natural_language_idea: "Evaluate sine, cosine, and tangent at selected coterminal special angles."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Trig

Trig::sin(5 * pi / 3 + 2 * 0 * pi) = (-1 * sqrt(3)) / 2
Trig::cos(5 * pi / 3 + 2 * 0 * pi) = 1 / 2
Trig::cos(2 * pi / 3 + 1 * pi) != 0
Trig::tan(2 * pi / 3 + 1 * pi) = -1 * sqrt(3)
have answer set = ((-1 * sqrt(3)) / 2, 1 / 2, -1 * sqrt(3), (-1 * sqrt(3)) / 3)
```

## 15. `required-2/0027`

```yaml
id: "required-2/0027"
source: "High School Book"
topic: "trigonometry periods"
difficulty: "required"
natural_language_idea: "Check sine and cosine values at integer multiples of pi."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Trig
forall k Z:
    Trig::sin(k * pi) = 0

forall k Z:
    Trig::cos(2 * k * pi) = 1
    Trig::cos((2 * k + 1) * pi) = -1
```

## 16. `required-2/0032`

```yaml
id: "required-2/0032"
source: "High School Book"
topic: "inverse trigonometry"
difficulty: "required"
natural_language_idea: "Record the inverse sine and inverse cosine identities on their principal domains."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Trig

forall x R:
    0 <= x <= 1
    -1 <= x <= 1
    =>:
        Trig::sin(Trig::arcsin(x)) = x
        Trig::cos(Trig::arccos(x)) = x

forall y R:
    0 <= y <= pi / 2
    -pi / 2 <= y <= pi / 2
    0 <= y <= pi
    =>:
        Trig::arcsin(Trig::sin(y)) = y
        Trig::arccos(Trig::cos(y)) = y

forall x R:
    -1 <= x <= 1
    =>:
        Trig::sin(Trig::arcsin(x)) = x
        Trig::cos(Trig::arccos(x)) = x

forall y R:
    -pi / 2 <= y <= pi / 2
    =>:
        Trig::arcsin(Trig::sin(y)) = y

forall y R:
    0 <= y <= pi
    =>:
        Trig::arccos(Trig::cos(y)) = y
```

## 17. `required-2/0033`

```yaml
id: "required-2/0033"
source: "High School Book"
topic: "inverse trigonometry"
difficulty: "required"
natural_language_idea: "Record the arctangent and tangent inverse identities on the principal interval."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Trig

forall x R:
    0 < 1 + x^2
    =>:
        Trig::cos(Trig::arctan(x)) > 0
        Trig::tan(Trig::arctan(x)) = x

forall y R:
    -pi / 2 < y < pi / 2
    =>:
        Trig::arctan(Trig::tan(y)) = y
```

## 18. `required-2/0059`

```yaml
id: "required-2/0059"
source: "High School Book"
topic: "trigonometric solution sets"
difficulty: "required"
natural_language_idea: "Record representative solution sets for inverse-trigonometric equation solving."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Trig
have answer_0059_1 set = (pi / 6, pi / 3, 7 * pi / 6, 4 * pi / 3)
have answer_0059_2 set = {x R: (x - pi / 12) / pi / 2 $in Z or (x + 5 * pi / 12) / pi / 2 $in Z}
have answer_0059_3 set = {x R: (x - pi / 4) / pi * 2 $in Z}
```

## 19. `required-2/0330`

```yaml
id: "required-2/0330"
source: "High School Book"
topic: "inverse trigonometry"
difficulty: "required"
natural_language_idea: "Repeat the arcsin/arccos principal-domain interface from a later exercise slot."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Trig

forall x R:
    0 <= x <= 1
    -1 <= x <= 1
    =>:
        Trig::sin(Trig::arcsin(x)) = x
        Trig::cos(Trig::arccos(x)) = x

forall y R:
    0 <= y <= pi / 2
    -pi / 2 <= y <= pi / 2
    0 <= y <= pi
    =>:
        Trig::arcsin(Trig::sin(y)) = y
        Trig::arccos(Trig::cos(y)) = y

forall x R:
    -1 <= x <= 1
    =>:
        Trig::sin(Trig::arcsin(x)) = x
        Trig::cos(Trig::arccos(x)) = x

forall y R:
    -pi / 2 <= y <= pi / 2
    =>:
        Trig::arcsin(Trig::sin(y)) = y

forall y R:
    0 <= y <= pi
    =>:
        Trig::arccos(Trig::cos(y)) = y
```

## 20. `required-2/0331`

```yaml
id: "required-2/0331"
source: "High School Book"
topic: "inverse trigonometry"
difficulty: "required"
natural_language_idea: "Repeat the arctan principal-domain interface from a later exercise slot."
litex_code: "see litex block below"
proof_attempt: "see litex block below"
status: "checkable"
blocker: ""
notes: "Dataset-gallery selection; verify with `cargo test run_examples -- --nocapture`."
```

```litex
import Trig

forall x R:
    0 < 1 + x^2
    =>:
        Trig::cos(Trig::arctan(x)) > 0
        Trig::tan(Trig::arctan(x)) = x

forall y R:
    -pi / 2 < y < pi / 2
    =>:
        Trig::arctan(Trig::tan(y)) = y
```
