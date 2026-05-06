# Builtin Verification Rules

Jiachen Shen and The Litex Team, 2026-05-06. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Manual/Builtin_Verification_Rules

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual/Builtin_Verification_Rules.md

Builtin verification rules are the mathematical patterns Litex can use to close a goal while checking a fact. They are part of the verification phase, before a fact is stored.

The main idea is simple: if a goal uses builtin predicates and builtin objects, and it matches a mathematical pattern Litex knows, Litex can close it without asking the user to write a separate theorem.

For the full flow around goals, storage, and inference, see [Proof Process](https://litexlang.com/doc/Manual/Proof_Process).

---

## How To Read This Page

This page is not something to memorize. It is a map of common builtin patterns, and you can read it casually when you want to know what Litex can close automatically.

Most examples are real `litex` snippets. They are meant to show the shape of facts Litex can verify automatically. The checker may use several smaller rules internally, but the user-facing experience is that the fact just closes.

There are many entries here because basic mathematical concepts have many simple pairwise relationships. Each relationship is usually easy, but the total number of combinations is large. One of Litex's main design choices is to build in many of these simple-but-numerous relationships. The result is that user code can stay closer to everyday mathematical writing without giving up runtime speed.

When a rule does not apply, the usual fix is to write an intermediate fact that makes the goal look more like one of these patterns.

---

## Equality Rules

Equality goals are mainly handled by evaluation, normalization, structural matching, and standard algebraic identities.

### Numeric Evaluation

Pure numeric goals are reduced and compared.

```litex
2 + 3 * 4 = 14
```

Integer remainder with concrete operands is evaluated directly.

```litex
4 % 2 = 0
```

Rational equalities can close by the rational pipeline, which is morally cross-multiplication under valid denominators.

```litex
2 / 3 = 4 / 6
```

### Algebraic Normalization

Equivalent polynomial expressions over ordinary number domains can normalize to the same form.

```litex
forall a, b R:
    (a + b)^2 = a^2 + a*b + b^2 + b*a
```

Same-head expressions can be proved equal when their corresponding arguments are equal.

```litex
forall x, y R:
    x = y
    =>:
        (x + 1) * (x + 1) = (y + 1) * (y + 1)
```

The same structural idea applies to many composite objects: matrices, `max`, `min`, set operations, tuples, and other builtin object heads.

### Known Numeric Values

After a name is known to equal a concrete number, Litex can resolve that name when checking later equalities.

```litex
have a R = 2
a ^ 2 = 4
```

This is why facts like `x = 2` are so useful: they make later expressions involving `x` calculable.

### Functions And Families

For a named function introduced by `have fn`, Litex can instantiate the function body at the given arguments.

```litex
have fn f(x R) R = x + 1
f(2) = 3
```

Anonymous functions behave the same way: applying the function substitutes the argument into the body.

```litex
'R(x){x + 1}(2) = 3
```

A parameterized `family` expands to the object it defines when instantiated.

```litex
prove:
    family p(a set) = fn(x a) a
    \p(R) = fn(x R) R
```

### Absolute Value

Litex knows the usual absolute-value cases.

```litex
forall x R:
    0 <= x
    =>:
        abs(x) = x
```

```litex
forall x R:
    x <= 0
    =>:
        abs(x) = -x
```

It also knows common algebraic identities involving `abs`.

```litex
forall x, y R:
    abs(x * y) = abs(x) * abs(y)
```

```litex
forall x R:
    x^4 = abs(x)^4
```

If `abs(x) = 0` is known, Litex can conclude `x = 0`.

```litex
forall x R:
    abs(x) = 0
    =>:
        x = 0
```

### Powers

Exponent one simplifies to the base.

```litex
forall a R:
    a^1 = a
```

Positive integer exponents can use the usual exponent-addition law.

```litex
forall a R, m, n N_pos:
    a^(m + n) = a^m * a^n
```

If a positive literal power is zero, Litex can reduce the goal to the base being zero.

```litex
prove:
    forall a R:
        a = 0
        =>:
            a ^ 3 = 0
```

A difference against literal zero can close when the two sides are known equal.

```litex
prove:
    have x R = 5
    x - x = 0
```

### Logarithms

Logarithm rules follow the standard inverse and algebra laws, with well-definedness and domain conditions checked first.

```litex
forall a, b R_pos:
    a != 1
    =>:
        log(a, a^b) = b
```

```litex
forall a, b, c R_pos:
    a != 1
    a^b != 1
    =>:
        log(a^b, c) = log(a, c) / b
```

```litex
forall a, x, b R_pos:
    a != 1
    =>:
        log(a, x^b) = b * log(a, x)
```

```litex
forall a, x, y R_pos:
    a != 1
    =>:
        log(a, x * y) = log(a, x) + log(a, y)
```

```litex
forall a, x, y R_pos:
    a != 1
    =>:
        log(a, x / y) = log(a, x) - log(a, y)
```

```litex
forall a, b R_pos, c R:
    a != 1
    a^c = b
    =>:
        log(a, b) = c
```

### Finite Sums And Products

Litex has builtin rules for common finite `sum` and `product` shapes: splitting summands, concatenating adjacent ranges, peeling the last term, tiling a range, reindexing by a constant shift, and summing a constant body.

```litex
sum(1, 3, '(x Z) Z {x + x}) = sum(1, 3, '(x Z) Z {x}) + sum(1, 3, '(x Z) Z {x})
```

```litex
sum(1, 3, '(x Z) Z {x + x}) + sum(4, 6, '(x Z) Z {x + x}) = sum(1, 6, '(x Z) Z {x + x})
```

```litex
sum(1, 3, '(x Z) Z {x}) = sum(1, 2, '(x Z) Z {x}) + '(x Z) Z {x}(3)
```

```litex
product(1, 3, '(x Z) Z {x}) = product(1, 2, '(x Z) Z {x}) * '(x Z) Z {x}(3)
```

```litex
sum(1, 10, '(x Z) Z {x}) = sum(1, 3, '(x Z) Z {x}) + sum(4, 8, '(x Z) Z {x}) + sum(9, 10, '(x Z) Z {x})
```

```litex
product(1, 10, '(x Z) Z {x}) = product(1, 3, '(x Z) Z {x}) * product(4, 8, '(x Z) Z {x}) * product(9, 10, '(x Z) Z {x})
```

```litex
sum(1, 3, '(x Z) Z {x}) = sum(2, 4, '(x Z) Z {x - 1})
```

```litex
have c Z
sum(1, 3, '(x Z) Z {c}) = ((3 - 1) + 1) * c
```

### Modular Arithmetic

Concrete `%` expressions are evaluated when possible. Litex also knows common congruence patterns.

```litex
forall m Z:
    m != 0
    =>:
        0 % m = 0
```

```litex
forall x1, x2, y1, y2 Z, m N_pos:
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 + y1) % m = (x1 % m + y1 % m) % m = (x2 % m + y2 % m) % m = (x2 + y2) % m
```

```litex
forall x1, x2, y1, y2, m Z:
    m != 0
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 - y1) % m = (x2 - y2) % m
```

```litex
forall x1, x2, y1, y2, m Z:
    m != 0
    x1 % m = x2 % m
    y1 % m = y2 % m
    =>:
        (x1 * y1) % m = (x2 * y2) % m
```

Taking `% m` twice with the same `m` is redundant.

```litex
prove:
    (5 % 7) % 7 = 5 % 7
```

---

## Order And Comparison Rules

Order goals use sign reasoning, monotonicity, standard number-set facts, and fraction comparison.

### Numeric Comparisons

Concrete numeric inequalities are evaluated directly.

```litex
1 < 2
```

```litex
2 <= 2
```

When both sides are explicit fractions with nonzero denominators, Litex may compare by clearing denominators.

```litex
prove:
    1 / 2 < 3 / 4
```

### Bounds From Number Sets

Litex knows basic order facts about `N` and `N_pos`.

```litex
forall n N_pos:
    1 <= n
```

```litex
forall n N:
    0 <= n
```

```litex
forall x N:
    x != 0
    =>:
        1 <= x
```

```litex
forall x N:
    1 <= x
    =>:
        x != 0
```

### Sums, Products, Quotients, And Powers

Nonnegative or positive parts can make a larger expression nonnegative or positive.

```litex
forall a, b R:
    0 <= a
    0 <= b
    =>:
        0 <= a + b
```

```litex
let a, b, c R:
    0 <= a
    0 <= b
    0 <= c

0 <= a + b + c
```

```litex
forall a, b R:
    0 < a
    0 <= b
    =>:
        0 < a + b
```

```litex
forall a, b, c R:
    a < b
    0 <= c
    =>:
        a < b + c
```

```litex
0 <= 3 * 2
```

```litex
0 <= 3 / 2
```

```litex
0 <= (-2) ^ 2
```

```litex
forall a R:
    0 <= a ^ 2
```

```litex
0 < 2 ^ 3
```

### Combining Inequalities

Litex knows standard monotonicity patterns for addition, subtraction, multiplication by a nonnegative value, and division by a positive value.

```litex
forall a, b, c, d R:
    a <= b
    c <= d
    =>:
        a + c <= b + d
```

```litex
forall a, b, c, d R:
    a <= b
    c <= d
    =>:
        a - d <= b - c
```

```litex
forall a, b R:
    0 <= a
    1 <= b
    =>:
        a <= b * a
```

```litex
prove:
    have k R = 2
    have a R = 1
    have b R = 3
    0 <= k
    a <= b
    k * a <= k * b
```

```litex
prove:
    have a R = 2
    have b R = 4
    have c R = 3
    0 < c
    a < b
    a / c < b / c
```

### Sign Flips And Absolute Value

Multiplying by `-1` flips the sign in the usual way.

```litex
forall x R:
    x <= 0
    =>:
        0 <= -1 * x
```

Litex also knows the standard order properties of `abs`.

```litex
forall x R:
    x <= abs(x)
```

```litex
forall x R:
    -x <= abs(x)
```

```litex
forall x R:
    0 <= abs(x)
```

```litex
forall x, b R:
    x <= b
    -x <= b
    =>:
        abs(x) <= b
```

```litex
forall x, y R:
    abs(x + y) <= abs(x) + abs(y)
```

```litex
forall x, y R:
    abs(x) - abs(y) <= abs(x + y)
```

### Disequality

Disequalities such as `!=` can close when numeric or ordering information rules out equality.

```litex
2 != 3
```

---

## Membership Rules

Membership goals are checked by evaluating the object and recognizing standard set shapes.

### Standard Number Sets

Concrete literals and many arithmetic combinations of literals can be checked against standard number sets.

```litex
1 $in N_pos
```

```litex
1 + 1 $in N
```

Negated membership in a standard set can close for concrete numeric values.

```litex
prove:
    not (-1) $in N
```

### Numeric Cones And `max` / `min`

If `max(a,b)` or `min(a,b)` is asserted inside a standard one-sided number cone, Litex may close the goal when both operands are already known to lie in that same cone.

```litex
prove:
    max(2, 3) $in R_pos
```

### Finite Sums And Products

A finite `sum` or `product` over an integer range is treated as a real once the indexed expression is well-defined.

```litex
prove:
    sum(1, 3, '(x Z) Z {x}) $in R
```

---

## Set Inclusion Rules

Subset goals are treated as universal membership: every element of the left set must lie in the right set.

```litex
{1} $subset {1, 2}
```

Superset and negated subset or superset claims are related to the same membership idea. When a direct subset statement is clumsy, write the universal membership fact explicitly as in an ordinary proof.

---

## Type Predicate Rules

Type predicates recognize standard object shapes.

```litex
$is_set({1, 2})
```

Nonempty enumerated sets, standard sets such as `R`, integer closed ranges with valid endpoints, Cartesian products with nonempty factors, nonempty function spaces, and similar shapes can be recognized as nonempty.

```litex
$is_nonempty_set({1})
```

```litex
prove:
    $is_nonempty_set(closed_range(0, 2))
```

```litex
prove:
    $is_nonempty_set(cart(R_pos, R_pos))
```

An empty enumeration proves negated non-emptiness.

```litex
prove:
    not $is_nonempty_set({})
```

Finite-set syntax is recognized directly.

```litex
$is_finite_set({1, 2})
```

Tuple and Cartesian-product shapes are recognized structurally.

```litex
$is_tuple((2, 3))
```

```litex
$is_cart(cart(R, Q))
```

---

## Function Equality Rules

Function equality rules reduce function equality to pointwise equality.

### Equality On A Set

`$fn_eq_in(f, g, S)` means that `f` and `g` agree on every input in `S`. The checker reduces the goal to the corresponding pointwise facts.

```litex
have fn f(x R) R = x
have fn g(x R) R = x

forall x R:
    f(x) = x = g(x)

$fn_eq_in(f, g, R)
```

Anonymous function heads can be compared the same way when they denote the same map on the set.

```litex
$fn_eq_in('R(x){x}, 'R(y){y}, R)
```

### Equality From Function Type

`$fn_eq(f, g)` is for values whose function type is given by the same `fn(...)` or `have fn` specification on both sides. After checking that the type data matches, the goal reduces to a parameterized proof that `f` and `g` agree on every argument tuple.

```litex
$fn_eq('R(x){x}, 'R(y){y})
```

```litex
have fn f(x R) R = x
have fn g(x R) R = x
forall x R:
    f(x) = x = g(x)
$fn_eq(f, g)
```

Two function-set values written with the same `fn` parameter list and body-shaped data can be proved equal when each side implies the other as a type.

---

## Practical Advice

Builtin verification works best when your goal is written in a familiar shape. If a mathematically true statement does not close, try adding a smaller intermediate fact: an equality, a sign condition, a membership fact, a nonzero denominator, or a pointwise fact for function equality.

Also read the output message. It often tells you whether a fact was closed by builtin rules, a known fact, or a known `forall`.
