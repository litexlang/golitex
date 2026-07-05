# Proof Patterns

Small proof moves that come up again and again: conjunctions, cases,
contradiction, witnesses, induction, theorem reuse, and named facts.

The purpose line says when the move is useful. The code blocks keep the setting
small so the proof pattern is easy to recognize.

## 1. `and_fact`

- Category: `fact`
- Purpose: Shows conjunction introduction and reuse.

```litex
1 = 1 and 1 + 2 = 3
```

## 2. `atomic_fact`

- Category: `fact`
- Purpose: Shows abstract atomic proposition matching.

```litex
abstract_prop p(a, b, c)
forall a, b, c, d, e, f R:
    $p(a, b, c)
    a = d
    b = e
    c = f
    =>:
        $p(d, e, f)
```

## 3. `by_axiom_of_choice`

- Category: `proof pattern`
- Purpose: Shows the choice-function proof form over a set of nonempty sets.

```litex
claim:
    prove:
        forall S set:
            forall A S:
                $is_nonempty_set(A)
            =>:
                exist f fn(A S) cup(S) st {forall! A S => {f(A) $in A}}

by axiom_of_choice: set S:
    ...
```

## 3.1. `general_cart`

- Category: `proof pattern`
- Purpose: Uses the built-in general Cartesian product as a choice-function set.

```litex
have I set
have s nonempty_set
have g fn(alpha I) s

know forall X s:
    $is_nonempty_set(X)

$is_nonempty_set(general_cart(I, s, g))
general_cart(I, s, g) = {f fn(t I)cup(s): forall! alpha I => {f(alpha) $in g(alpha)}}

have c general_cart(I, s, g)
c $in fn(t I)cup(s)

forall alpha I:
    c(alpha) $in g(alpha)
```

## 4. `by_cases`

- Category: `proof pattern`
- Purpose: Shows case splits over proposition and order alternatives.

```litex
sketch:
    by cases:
        prove:
            1 + 1 = 2
        case 1 + 1 = 2:
            do_nothing
        case 1 + 1 != 2:
            1 + 1 = 2
            impossible 1 + 1 = 2
```

```litex
abstract_prop p(x)

claim:
    prove:
        forall x R:
            forall y R:
                y > 0
                =>:
                    $p(y)
            forall y R:
                y <= 0
                =>:
                    $p(y)
            =>:
                $p(x)
    by cases:
        prove:
            $p(x)

        case x > 0:
            $p(x)
        case x <= 0:
            $p(x)

by cases 1 = 1:
    case 1 = 1:
        do_nothing
    case 1 != 1:
        impossible 1 = 1
```

```litex
# Real-line trichotomy is available in the common equality-first order.
forall x, y R:
    x = y or x < y or x > y
```

## 5. `by_contra`

- Category: `proof pattern`
- Purpose: Shows contradiction-based proof.

```litex
abstract_prop p(a)

claim:
    prove:
        forall b, c R:
            forall a R:
                $p(a + b)
                =>:
                    $p(a)
            not $p(c)
            =>:
                not $p(c + b)
    by contra:
        prove:
            not $p(c + b)
        impossible $p(c)

by contra 1 = 1:
    impossible 1 != 1

by contra:
    prove:
        not exist x R st {x != x}
    have by exist x R st {x != x}: a
    impossible a = a

by contra:
    prove:
        exist x R st {x = x}
    impossible 0 = 0
```

## 6. `by_enumerate_closed_range`

- Category: `proof pattern`
- Purpose: Shows finite closed-range enumeration.

```litex
sketch:
    have x closed_range(0, 10)

    by closed_range as cases: x $in 0...10
```

```litex
sketch:
    have a Z
    have x closed_range(a, a + 10)

    by closed_range as cases: x $in a...a + 10
```

## 7. `by_enumerate_finite_set`

- Category: `proof pattern`
- Purpose: Shows finite-set enumeration.

```litex
by enumerate finite_set:
    prove:
        forall a {1, 2}, b {3, 4}:
            a > 1
            b > 3
            =>:
                a = 2
                b = 4

by enumerate finite_set forall! a {1, 2}, b {3, 4}: a > 1 and b > 3 => {(a, b) = (2, 4)}:
    ...
```

## 8. `by_enumerate_range`

- Category: `proof pattern`
- Purpose: Shows finite range and closed-range enumeration syntax.

```litex
claim:
    prove:
        forall a range(7, 8):
            a = 7
    by enumerate range: a $in range(7, 8)
```

```litex
claim:
    prove:
        forall x range(1, 3):
            x = 1 or x = 2
    by enumerate range: x $in range(1, 3)
```

```litex
claim:
    prove:
        forall y closed_range(1, 3):
            y = 1 or y = 2 or y = 3
    by enumerate closed_range: y $in 1...3
```

## 9. `by_extension`

- Category: `proof pattern`
- Purpose: Shows set/function extensional equality.

```litex
by extension:
    prove:
        {1, 2} = {2, 1}
    by enumerate finite_set:
        prove:
            forall x {1, 2}:
                x $in {2, 1}
    by enumerate finite_set:
        prove:
            forall y {2, 1}:
                y $in {1, 2}

{1, 2} = {2, 1}

by extension {1} = {1}
```

## 10. `by_for`

- Category: `proof pattern`
- Purpose: Shows bounded universal proof automation.

```litex
by for:
    prove:
        forall n range(0, 10):
            n < 10
    do_nothing

by for:
    prove:
        forall n closed_range(0, 10):
            n <= 10
    do_nothing

by for forall! n range(0, 3) => {n < 3}:
    ...

by for:
    prove:
        forall x cart({1, 2}, {3, 4}):
            0 <= x[1] + x[2]
    do_nothing
```

```litex
sketch:
    prop Prime(x N_pos):
        2 <= x
        forall y range(2, x):
            x % y != 0

    prop superpowered(k N_pos):
        forall n N_pos:
            $Prime(k ^ (k ^ n) + 1)

    by for:
        prove:
            forall n range(2, 2):
                2 % n != 0

    $Prime(2)

    forall n N_pos:
        1^n = 1
        1^(1^n) + 1 = 1^1 + 1 = 2
        $Prime(1^(1^n) + 1)

    $superpowered(1)

    by contra not $superpowered(2):
        $Prime(2^(2^5) + 1) # by $superpowered(2)
        (2^(2^5) + 1) % 641 = 0
        impossible (2^(2^5) + 1) % 641 = 0

    witness exist k N_pos st {$superpowered(k) and not $superpowered(k + 1)} from 1
```

## 11. `by_induc`

- Category: `proof pattern`
- Purpose: Shows ordinary induction.

```litex
abstract_prop p(a)

claim:
    prove:
        forall n Z:
            $p(0)
            forall m Z:
                m >= 0
                $p(m)
                =>:
                    $p(m + 1)
            n >= 0
            =>:
                $p(n)
    by induc n from 0:
        prove:
            $p(n)

        prove from n = 0:
            $p(0)

        prove induc:
            $p(n + 1)
```

## 12. `by_induc_example1`

- Category: `proof pattern`
- Purpose: Shows a small induction proof.

```litex
claim:
    prove:
        forall n N:
            2 ^ n >= n + 1
    by induc n from 0:
        prove:
            2 ^ n >= n + 1
        2^0 = 1 >= 0 + 1

        forall m Z:
            m >= 0
            2^m >= m + 1
            =>:
                2^m * 2^1 >= (m+1) * 2
                2 ^ (m + 1) = 2 ^ m * 2^1 >= (m+1) * 2 = (m + 1) + (m + 1) >= m + 1 + 1
```

## 13. `by_induc_example2`

- Category: `proof pattern`
- Purpose: Shows a larger induction proof with arithmetic state.

```litex
claim:
    prove:
        forall b fn(x Z: x >= 0) Z, i Z:
            forall y Z:
                y >= 0
                =>:
                    b(y+1) = b(y)^ 2 - 2
            b(0) = 3
            i >= 0
            =>:
                b(i) % 2 = 1
    by induc i from 0:
        prove:
            b(i) % 2 = 1
        b(0) % 2 = 3 % 2 = 1

        forall m Z:
            m >= 0
            b(m) % 2 = 1
            =>:
                b(m+1) = b(m)^ 2 - 2
                b(m)^2 % 2 = (b(m) % 2)^2 % 2 = 1^2 % 2 = 1
                b(m + 1) % 2 = (b(m)^ 2 - 2) % 2
                (b(m)^ 2 - 2) % 2 = ((b(m)^2 %2) - (2 % 2)) % 2 = (1 - 0) % 2 = 1
                b(m + 1) % 2 = 1
```

## 14. `by_symmetric_reflexive_antisymmetric_prop`

- Category: `proof pattern`
- Purpose: Shows reflexive, symmetric, and antisymmetric proposition helpers.

```litex
sketch:
    prop same_obj(x set, y set):
        x = y

    prop r(x set, y set):
        x = y
    prop p(x set, y set):
        x = y

    by reflexive_prop:
        prove:
            forall x set:
                $same_obj(x, x)
        x = x

    by reflexive_prop:
        prove:
            forall x set:
                $r(x, x)
        x = x

    by symmetric_prop:
        prove:
            forall x, y set:
                $p(x, y)
                =>:
                    $p(y, x)
        x = y
        y = x

    by antisymmetric_prop:
        prove:
            forall x, y set:
                $p(x, y)
                $p(y, x)
                =>:
                    x = y
        x = y

    claim:
        prove:
            forall a set:
                $same_obj(a, a)

    claim:
        prove:
            forall a set:
                $r(a, a)

    claim:
        prove:
            forall a, b set:
                $p(a, b)
                =>:
                    $p(b, a)

    claim:
        prove:
            forall a, b set:
                $p(a, b)
                $p(b, a)
                =>:
                    a = b
```

## 15. `by_transitive_prop`

- Category: `proof pattern`
- Purpose: Shows transitive proposition chaining.

```litex
prop p(x set, y set):
    x = y

by transitive_prop:
    prove:
        forall x, y, z set:
            $p(x, y)
            $p(y, z)
            =>:
                $p(x, z)
    x = y
    y = z
    x = z

forall a, b, c set:
    $p(a, b)
    $p(b, c)
    =>:
        $p(a, c)
```

## 16. `claim`

- Category: `stmt`
- Purpose: Shows local claim statements and reuse.

```litex
claim:
    prove:
        1 = 1 and 1 + 2 = 3
    1 = 1
    1 + 2 = 3

claim:
    prove:
        forall a R:
            a $in R
    a $in R

claim 1 = 1:
    do_nothing
```

```litex
claim:
    ? 2 = 2
    2 = 2

thm question_goal_example:
    ? forall x R:
        x = x
    x = x
```

## 17. `exist`

- Category: `fact`
- Purpose: Shows existential and unique-existence facts.

```litex
abstract_prop p(a, b)
abstract_prop q(a, b)

forall:
    exist! a, b, c R st {$p(a, b), $q(b, c)}
    forall a1, b1, c1 R, a2, b2, c2 R:
        $p(a1, b1)
        $q(b1, c1)
        $p(a2, b2)
        $q(b2, c2)
        =>:
            (a1, b1, c1) = (a2, b2, c2)
    =>:
        # exist can be proved by exist!
        exist a, b, c R st {$p(a, b), $q(b, c)}
        exist! a, b, c R st {$p(a, b), $q(b, c)}

abstract_prop t(a)

forall:
    exist a R st {$t(a)}
    forall a1, a2 R:
        $t(a1)
        $t(a2)
        =>:
            a1 = a2
    =>:
        exist! a R st {$t(a)}
```

```litex
abstract_prop p(x, y)

forall:
    exist! a R st {$p(a, 1)}
    not exist x R st {$p(x, 2)}
    =>:
        exist b R st {$p(b, 1)}
        exist! c R st {$p(c, 1)}
        not exist y R st {$p(y, 2)}
```

```litex
abstract_prop p(x, y)
abstract_prop q(x, y)

forall:
    forall a R:
        exist! b R st {$p(a, b)}

    forall a R:
        not exist b R st {$q(a, b)}
    =>:
        exist b R st {$p(1, b)}
        exist! c R st {$p(1, c)}
        not exist b R st {$q(1, b)}
```

```litex
forall:
    exist a R st {a > 0, a < 1}
    =>:
        exist b R st {b > 0, b < 1}
```

## 18. `exist_fact_that_contains_forall`

- Category: `fact`
- Purpose: Shows extracting an existential whose witness carries a universal fact.

```litex
abstract_prop p(x)
abstract_prop q(x, y)

forall:
    exist a R st {forall! b R: $p(b) => {$q(a, b)}, $p(a)}
    =>:
        exist a R st {forall! b R: $p(b) => {$q(a, b)}, $p(a)}
```

## 19. `forall_in_forall`

- Category: `stmt`
- Purpose: Shows nested universal facts and local instantiation.

```litex
# Let a be a real number and suppose that for all real numbers x, a <= x^2 - 2x. Show that a <= -1.


forall a R:
    forall x R:
        a <= x^2 - 2 * x
    =>:
        a <= 1^2 - 2 * 1 = -1

"""
Let n be a natural number which is a factor of every natural number m. Show that n = 1.
"""

claim:
    prove:
        forall n N:
            forall m, k N:
                0 < m < k
                =>:
                    m % k = m
            n > 0
            forall m N:
                m % n = 0
            =>:
                n = 1
    by contra:
        prove:
            n <= 1
        n > 1
        1 % n = 0
        1 % n = 1
        impossible 0 = 1

    n $in closed_range(0, 1)
    by for:
        prove:
            forall m closed_range(0, 1):
                m = 0 or m = 1

    n =  0 or n = 1
    by cases:
        prove:
            n = 1
        case n  = 0:
            n >  0
            impossible 0 > 0
        case n = 1:
            do_nothing
```

```litex
abstract_prop p(a, b, c, d)
abstract_prop q(a, b)

forall:
    forall a, b R:
        forall c, d R:
            $p(a, b, c, d)
        =>:
            $q(a, b)

    forall c, d R:
        $p(1, 2, c, d)
    =>:
        $q(1, 2)
```

## 20. `inline_forall`

- Category: `stmt`
- Purpose: Shows inline universal facts inside proposition bodies.

```litex
forall! a R: a > 0 => { a + 1 > 1 }

forall! a R: a > 0 => {a + 1 > 1 and a + 2 > 2}
```

## 21. `logic`

- Category: `proof pattern`
- Purpose: Shows propositional reasoning, implication, cases, and negation.

```litex
abstract_prop p()
abstract_prop q()
abstract_prop r()

# 5.1.1
# 由 P∨Q 与 ¬Q 得 P：析取分情形，第二支与 ¬Q 矛盾。
"""
If P ∨ Q and ¬ Q, then P.
"""
```

```litex
abstract_prop p()
abstract_prop q()
abstract_prop r()

claim:
    prove:
        forall:
            $p() or $q()
            not $p()
            =>:
                $q()
    by cases:
        prove:
            $q()
        case $p():
            impossible not $p()
        case $q():
            do_nothing

"""
# P → P ∨ ¬Q：由 P 可左注入得 P∨(¬Q)（书本 left）。
"""
"""
P implies P ∨ (not Q).
"""

forall:
    $p()
    =>:
        $p() or not $q()

# 5.1.4
# 两公式逻辑等价：指其 ↔ 在 Lean 可证（尚有一处 tactic 在 5.2 才齐全，故有些等价暂时无法演示）。
# P∨P ↔ P：左到右析取消去；右到左重复左注入。
"""
(P ∨ P) is logically equivalent to P.
"""
claim:
    prove:
        forall:
            $p() or $p()
            =>:
                $p()
    by cases:
        prove:
            $p()
        case $p():
            do_nothing
        case $p():
            do_nothing

forall:
    =>:
        $p() or $p()
    <=>:
        $p()

# 5.1.5
"""
P ∧ (Q ∨ R) is logically equivalent to (P ∧ Q) ∨ (P ∧ R).
"""
claim:
    prove:
        forall:
            $p()
            $q() or $r()
            =>:
                $p() and $q() or $p() and $r()

    by cases:
        prove:
            $p() and $q() or $p() and $r()
        case $q():
            $p() and $q()
        case $r():
            $p() and $r()

# 5.1.6
# 谓词 P(x)、Q(x)：由 ∀x Px 与 ∀x Qx 得 ∀x (Px∧Qx)。

abstract_prop P(x)
abstract_prop P2(x)

forall x set:
    $P(x)
    $P2(x)
    =>:
        $P(x) and $P2(x)

###标准库中应有quick prime check--能够check一个数是否为素数--函数应该要能够调用

### 答：用 by for 从 2 到 n-1做迭代，证明 d % i != 0就能证明了

# 5.2.6
# 命题逻辑：¬¬P ⇒ P（「负负得正」）需排中律：对 P 本身作 by_cases。
"""
From ¬¬P deduce P (using excluded middle).
"""

forall:
    not not $p()
    =>:
        $p()
```

## 22. `match_obj_with_free_param_in_forall`

- Category: `fact`
- Purpose: Shows matching free parameters in universal facts.

```litex
abstract_prop p(a, b)
abstract_prop q(a, b)

forall:
    forall a, b R:
        $p(a, {x R: $p(x, b)})
        $q(1, {x R: $q(a + b, x)})
    =>:
        $p(1, {x R: $p(x, 2)})
        # $p(1, {x R: $p(x, x)}) 是unknown，因为x作为set builder的参数不能匹配b
        $q(1, {x R: $q(1 + 2, x)})
```

## 23. `max_min_bounds`

- Category: `builtin rule`
- Purpose: Shows builtin max/min order consequences.

```litex
# Max/min order bounds used by sequence-limit estimates.

forall a, b, c R:
    a <= c
    b <= c
    =>:
        max(a, b) <= c

forall a, b, c R:
    c <= a
    c <= b
    =>:
        c <= min(a, b)
```

## 24. `membership_in_set_valued_fn`

- Category: `fact`
- Purpose: Shows membership unfolding for set-valued functions.

```litex
# Set-valued have fn applications unfold one layer for membership.

have fn circle(r R_pos) power_set(cart(R, R)) = {x cart(R, R): x[1]^2 + x[2]^2 = r^2}
have fn line(a, b, c R: a != 0 or b != 0) power_set(cart(R, R)) = {x cart(R, R): a * x[1] + b * x[2] + c = 0}

(3, 4) $in circle(5)
(2, 2) $in line(1, -1, 0)

forall a, b R:
    a != 0 or b != 0
    =>:
        (0, 0) $in line(a, b, 0)

forall p cart(R, R):
    p $in circle(5)
    =>:
        p[1]^2 + p[2]^2 = 5^2
```

## 25. `not_exist`

- Category: `fact`
- Purpose: Shows reasoning from negated existential facts.

```litex
abstract_prop p(x, y)

forall x R:
    not exist y R st {$p(y, 1)}
    =>:
        not $p(x, 1)

abstract_prop q(x, y)

forall x R:
    not exist y R st {$q(y, 1), $q(y, 2)}
    =>:
        not $q(x, 1) or not $q(x, 2)
```

## 26. `not_forall`

- Category: `fact`
- Purpose: Shows extracting counterexamples from negated universal facts.

```litex
abstract_prop p(x)
abstract_prop p2(x)
abstract_prop q(x)
abstract_prop q2(x)

forall:
    not forall x R:
        $p(x)
        $p2(x)
        =>:
            $q(x)
            $q2(x)
    =>:
        exist x R st {$p(x), $p2(x), not $q(x) or not $q2(x)}
```

## 27. `or_fact`

- Category: `fact`
- Purpose: Shows disjunction introduction and use.

```litex
abstract_prop p(a, b)
abstract_prop q(a, b)

forall:
    $p(1, 2) or $q(1, 2)
    =>:
        $p(1, 2) or $q(1, 2)
```

```litex
forall x Z:
    x >= 1
    =>:
        x = 1 or x = 2 or x = 3 or x = 4 or x > 4
```

```litex
forall a, x Z:
    x >= a
    =>:
        x = a or x = a + 1 or x = a + 2 or x > a + 2
```

```litex
abstract_prop p(a, b, c)
abstract_prop q(a, b, c)

forall a, b, c R:
    $p(1, 2, 3) or $q(1, 2, 3)
    a = 1
    b = 2
    c = 3
    =>:
        $p(a, b, c) or $q(a, b, c)
```

```litex
abstract_prop p(a, b)
abstract_prop q(a, b)

forall:
    forall a, b R:
        $p(a, b) or $q(a, b)
    =>:
        $p(1, 2) or $q(1, 2)
```

## 28. `power_builtin_rules`

- Category: `builtin rule`
- Purpose: Shows builtin exponent algebra and order rules.

```litex
# Power builtin rules cover common exponent algebra and order patterns.
# Example shape: use the equality or order relation directly.

0^0 = 1
8^(1/3) = 2

forall x Q, n, m N:
    x^n * x^m = x^(n + m)

forall x Q, n, m N:
    (x^n)^m = x^(n * m)

forall x, y Q, n N:
    (x * y)^n = x^n * y^n

forall x Q, n N_pos:
    x^n = 0
    =>:
        x = 0

forall x, y Q, n N_pos:
    x >= y
    y >= 0
    =>:
        x^n >= y^n
        y^n >= 0

forall x, y R, n N_pos:
    x > y
    y >= 0
    =>:
        x^n > y^n

forall x R:
    x < 0
    =>:
        x^3 < 0

forall x R, n N_pos:
    x < 0
    n % 2 = 1
    =>:
        x^n < 0

forall x, y R, n N_pos:
    x < y
    n % 2 = 1
    =>:
        x^n < y^n

forall x R, n N:
    abs(x^n) = abs(x)^n

forall x Q_nz, n, m Z:
    x^n * x^m = x^(n + m)

forall x R_nz, n Z:
    x^n != 0
    abs(x^n) = abs(x)^n

forall x R_nz, n N_pos:
    x^(-n) = 1 / x^n

forall x, y R_nz, n Z:
    (x * y)^n = x^n * y^n

forall x, y R_pos, n Z:
    x >= y
    n < 0
    =>:
        x^n <= y^n

forall x, y R_pos, n Z:
    n != 0
    x^n = y^n
    =>:
        x = y

forall a R_pos, x R:
    a^x $in R_pos

forall a R_pos, x, y R:
    a^x = y
    =>:
        y $in R_pos

forall a R_pos, x, y R:
    a != 1
    a^x = y
    =>:
        x = log(a, y)
```

## 29. `set_algebra_builtin_rules`

- Category: `builtin rule`
- Purpose: Shows builtin subset/union/intersection algebra.

```litex
forall A, B set:
    intersect(A, B) = intersect(B, A)

forall A, B, C set:
    intersect(intersect(A, B), C) = intersect(A, intersect(B, C))

forall A, B, C set:
    intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))

forall A, B, C set:
    set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))

forall A, B, C set:
    set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C))

forall S set, x set, y set:
    x $in S
    not y $in S
    =>:
        intersect(S, {x, y}) = {x}

have A, B, C set
intersect(A, B) = intersect(B, A)
intersect(intersect(A, B), C) = intersect(A, intersect(B, C))
intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))
set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))
set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C))
```

## 30. `strategy`

- Category: `proof pattern`
- Purpose: Shows reusable proof strategies over abstract propositions.

```litex
prop p(x R):
    x = 1
prop q(x R):
    x = x
prop r(x R):
    x = 1

strategy prove_p:
    prove:
        forall x R:
            x = 1
            =>:
                $p(x)
    x = 1

# A verified strategy is enabled immediately after definition.
$p(1)

strategy prove_q:
    prove:
        forall x R:
            x = x
            =>:
                $q(x)
    x = x

# A stopped strategy still leaves its proved forall available to ordinary proofs.
strategy prove_r:
    prove:
        forall x R:
            x = 1
            =>:
                $r(x)
    x = 1

stop strategy prove_r
claim:
    prove:
        forall z R:
            z = 1
            =>:
                $r(z)

# Same environment: stop followed by use re-enables the same strategy key.
stop strategy prove_p
use strategy prove_p
$p(1)

# Parent environment is stopped, but a child environment can enable the strategy locally.
use strategy prove_q
stop strategy prove_q
claim:
    prove:
        $q(2)
    use strategy prove_q

# Back in the parent environment, use removes the parent stop and re-enables it.
use strategy prove_q
$q(3)
```

## 31. `strong_induc`

- Category: `proof pattern`
- Purpose: Shows strong induction over integers.

```litex
abstract_prop p(a)

claim:
    prove:
        forall n Z:
            $p(0)
            forall m Z:
                m >= 0
                forall y Z:
                    y >= 0
                    y <= m
                    =>:
                        $p(y)
                =>:
                    $p(m + 1)
            n >= 0
            =>:
                $p(n)
    by strong_induc n from 0:
        prove:
            $p(n)

        prove from n = 0:
            $p(0)

        prove strong_induc:
            $p(n + 1)
```

## 32. `syllogism`

- Category: `proof pattern`
- Purpose: Shows a minimal universal-instantiation argument.

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

forall:
    forall x human:
        $mortal(x)
    =>:
        $mortal(Socrates)
```

## 33. `thm`

- Category: `stmt`
- Purpose: Shows theorem declaration, aliases, and theorem application.

```litex
# Basic named theorem with aliases and no domain facts.
thm thm_refl_r, thm_refl_r_alias:
    prove:
        forall x R:
            x = x

by thm thm_refl_r(0)
0 = 0

by thm thm_refl_r_alias(0)
0 = 0

# A theorem alias can use a local-language name while the original theorem
# keeps an English/std-facing name.
thm self_eq_en:
    prove:
        forall x R:
            x = x
    x = x

alias thm 自反等式 <=> self_eq_en
by thm 自反等式(1)
1 = 1

# A theorem with one domain fact.
thm thm_one_succ:
    prove:
        forall x R:
            x = 1
            =>:
                x + 1 = 2
    x + 1 = 1 + 1 = 2

by thm thm_one_succ(1)
1 + 1 = 2

# Multiple arguments and multiple domain facts.
thm thm_add_equal_with_unit:
    prove:
        forall a, b, c R:
            a = b
            c = 1
            =>:
                a + c = b + 1
    a + c = b + c = b + 1

by thm thm_add_equal_with_unit(2, 2, 1)
2 + 1 = 2 + 1

# Multiple then-facts are all released by the named theorem call.
thm thm_many_then:
    prove:
        forall x R:
            x = 1
            =>:
                x = 1
                x + 1 = 2
                x + 2 = 3
    x = 1
    x + 1 = 1 + 1 = 2
    x + 2 = 1 + 2 = 3

by thm thm_many_then(1)
1 + 2 = 3

# A theorem can release an and-fact.
thm thm_and_then:
    prove:
        forall x R:
            x = 0
            =>:
                x = 0 and x + 1 = 1
    x = 0
    x + 1 = 0 + 1 = 1
    x = 0 and x + 1 = 1

by thm thm_and_then(0)
0 + 1 = 1

# A theorem can release a chain fact.
thm thm_chain_then:
    prove:
        forall x R:
            x = 1
            =>:
                x + 1 = 1 + 1 = 2
    x + 1 = 1 + 1 = 2

by thm thm_chain_then(1)
1 + 1 = 2

# The explicit call works inside a claim proof.
claim:
    prove:
        forall x R:
            x = 1
            =>:
                x + 1 = 2
    by thm thm_one_succ(x)

# A named theorem may use another named theorem in its proof.
thm thm_use_thm_inside_thm:
    prove:
        forall x R:
            x = 1
            =>:
                x + 2 = 3
    by thm thm_one_succ(x)
    x + 2 = 1 + 2 = 3

by thm thm_use_thm_inside_thm(1)
1 + 2 = 3

# Argument type checking still applies for theorem calls.
thm thm_nat_refl:
    prove:
        forall n N:
            n = n

by thm thm_nat_refl(1)
1 = 1

# A proved theorem is also stored as a forall fact. After the domain fact is
# known, ordinary fact checking can use the theorem without an explicit call.
prop thm_match_p(x R):
    x = 1
prop thm_match_q(x R):
    x = 1

thm thm_stored_forall:
    prove:
        forall x R:
            $thm_match_p(x)
            =>:
                $thm_match_q(x)
    x = 1

$thm_match_p(1)
$thm_match_q(1)

# The explicit theorem call remains available when theorem-instantiation
# output is useful.
by thm thm_stored_forall(1)
```

## 34. `use_builtin_code_to_verify`

- Category: `builtin rule`
- Purpose: Shows facts verified from builtin background code.

```litex
claim:
    prove:
        forall a, b R:
            a < b or a = b or a > b

claim:
    prove:
        forall a, b R:
            a <= b
            =>:
                a = b or a < b

import Int

claim:
    prove:
        forall x R:
            Int::floor(x) $in R
    Int::floor(x) $in R
```

## 35. `use_forall_and_prop_def_to_verify_atomic_fact`

- Category: `fact`
- Purpose: Shows atomic fact verification through prop definitions and forall facts.

```litex
abstract_prop q(x, y, z)

prop p(x, y R):
    x > y
    forall t R:
        $q(x, y, t)

forall a, b R:
    $p(a, b)
    =>:
        a > b
        $q(a, b, 2)
```

```litex
abstract_prop p(a)

forall b, c R:
    forall a R:
        $p(a + b)
        =>:
            $p(a)
    $p(c + b)
    =>:
        $p(c)
```

## 36. `use_forall_arithmetic_to_prove`

- Category: `fact`
- Purpose: Shows arithmetic instantiation of universal facts.

```litex
sketch:
    abs(-1) = 1
```

```litex
abstract_prop q(a)

forall:
    forall a R:
        $q(-a)
    =>:
        $q(1)
```

```litex
abstract_prop p(a)

forall:
    forall a R:
        $p(2 * a)
    =>:
        $p(1)
```

```litex
abstract_prop p(a)

forall:
    forall a R:
        $p(a * 2)
    =>:
        $p(1)
```

```litex
abstract_prop p(a)

forall:
    forall a R:
        $p(a / 2)
    =>:
        $p(1)
```

```litex
abstract_prop p(a)

forall:
    forall a R:
        $p(2 + a)
    =>:
        $p(1)
```

```litex
abstract_prop p(a)

forall:
    forall a R:
        $p(2 - a)
    =>:
        $p(1)
```

```litex
abstract_prop p(a)

forall:
    forall a R:
        $p(a + 2)
    =>:
        $p(1)
```

```litex
abstract_prop p(a)

forall:
    forall a R:
        $p(a - 2)
    =>:
        $p(1)
```

## 37. `verify_by_resolving_atomic_fact_arg`

- Category: `fact`
- Purpose: Shows resolving an atomic proposition argument before matching.

```litex
abstract_prop p(a)

forall:
    forall a R:
        $p(a)
        =>:
            $p(a + 1)
    $p(1)
    =>:
        $p(2)
```

## 38. `witness_exist`

- Category: `proof pattern`
- Purpose: Shows explicit witnesses for existential facts.

```litex
witness exist x, y R st {x > y} from 1, 0:
    1 > 0

exist x, y R st {x > y}
```

## 39. `witness_nonempty`

- Category: `proof pattern`
- Purpose: Shows explicit witnesses for nonempty sets.

```litex
claim:
    prove:
        forall s set:
            1 $in s
            =>:
                $is_nonempty_set(s)
    witness $is_nonempty_set(s) from 1:
        1 $in s
```

## 40. `nonzero_natural_is_positive`

- Category: `fact`
- Purpose: Shows that a nonzero natural number is a positive natural number.

```litex
forall n N:
    n != 0
    =>:
        n $in N_pos
```

## 41. `by_regularity_axiom`

- Category: `proof pattern`
- Purpose: Shows the trusted regularity/foundation step for a nonempty set.

```litex
know $is_nonempty_set({1, 2})

by regularity_axiom({1, 2})

exist x {1, 2} st {intersect(x, {1, 2}) = {}}
```

## 42. `cup_membership`

- Category: `fact`
- Purpose: Shows introduction and elimination for family-union membership.

```litex
thm cup_intro_from_member:
    prove:
        forall x set, F set, A set:
            A $in F
            x $in A
            =>:
                x $in cup(F)
    x $in cup(F)

thm cup_elim_to_exist:
    prove:
        forall x set, F set:
            x $in cup(F)
            =>:
                exist A F st {x $in A}
    exist A F st {x $in A}
```
