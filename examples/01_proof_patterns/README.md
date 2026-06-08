# Proof Patterns

Reusable proof shapes and verifier tactics. These snippets are intentionally small and focus on one statement form or proof move at a time.

Each Litex block below is checked independently by `cargo test run_examples -- --nocapture`.
The `Category` and `System surface` fields say what part of Litex the example is meant to exercise.

## 1. `and_fact`

- Category: `fact`
- System surface: `and fact`
- Purpose: Shows conjunction introduction and reuse.

```litex
1 = 1 and 1 + 2 = 3
```

## 2. `atomic_fact`

- Category: `fact`
- System surface: `atomic proposition`
- Purpose: Shows abstract atomic proposition matching.

```litex
abstract_prop p(a, b, c)
let a, b, c, d, e, f R:
    $p(a, b, c)
    a = d
    b = e
    c = f

$p(d, e, f)
```

## 3. `by_axiom_of_choice`

- Category: `proof pattern`
- System surface: `by axiom_of_choice`
- Purpose: Shows the choice-function proof form over a set of nonempty sets.

```litex
have S set

by axiom_of_choice: set S:
    know forall A S:
        $is_nonempty_set(A)

exist f fn(A S) cup(S) st {forall! A S: {f(A) $in A}}
```

## 4. `by_cases`

- Category: `proof pattern`
- System surface: `by cases`
- Purpose: Shows case splits over proposition and order alternatives.

```litex
scratch:
    by cases:
        prove:
            1 + 1 = 2
        case 1 + 1 = 2:
            do_nothing
        case 1 + 1 != 2:
            1 + 1 = 2
            impossible 1 + 1 = 2

scratch:
    abstract_prop p(x)

    know:
        forall x R:
            x > 0
            =>:
                $p(x)
        forall x R:
            x <= 0
            =>:
                $p(x)

    by cases:
        prove:
            forall x R:
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

## 5. `by_contra`

- Category: `proof pattern`
- System surface: `by contra`
- Purpose: Shows contradiction-based proof.

```litex
abstract_prop p(a)

have b R, c R

know forall a R:
    $p(a + b)
    =>:
        $p(a)

know not $p(c)

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
- System surface: `by enumerate closed_range`
- Purpose: Shows finite closed-range enumeration.

```litex
scratch:
    have x closed_range(0, 10)

    by closed_range as cases: x $in 0...10

scratch:
    have a Z
    have x closed_range(a, a + 10)

    by closed_range as cases: x $in a...a + 10
```

## 7. `by_enumerate_finite_set`

- Category: `proof pattern`
- System surface: `by enumerate finite_set`
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

by enumerate finite_set forall! a {1, 2}, b {3, 4}: a > 1, b > 3 => {(a, b) = (2, 4)}:
    ...
```

## 8. `by_enumerate_range`

- Category: `proof pattern`
- System surface: `by enumerate range`
- Purpose: Shows finite range and closed-range enumeration syntax.

```litex
scratch:
    let a range(7, 8)

    by enumerate range: a $in range(7, 8)

    a = 7

scratch:
    let x range(1, 3)

    by enumerate range: x $in range(1, 3)

    x = 1 or x = 2

scratch:
    let y closed_range(1, 3)

    by enumerate closed_range: y $in 1...3

    y = 1 or y = 2 or y = 3
```

## 9. `by_extension`

- Category: `proof pattern`
- System surface: `by extension`
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

## 10. `by_fn`

- Category: `proof pattern`
- System surface: `by fn`
- Purpose: Shows construction of a function object.

```litex
have f fn(x R)R

by fn as set: f
```

## 11. `by_fn_set`

- Category: `proof pattern`
- System surface: `by fn set as set`
- Purpose: Shows turning a function-space condition into a set object.

```litex
let f set

know:
    forall x1 f:
        x1 $in cart(R, Q, Z)
        tuple_dim(x1) = 3

    forall x1 f:
        exist x2 R, x3 Q, z Z st {x2 > x3, x2 > 2, x1 = (x2, x3, z)}

    forall x2 R, x3 Q:
        x2 > x3
        x2 > 2
        =>:
            exist x1 f, z Z st {x1 = (x2, x3, z)}

    forall x1, x2 f:
        x1 $in cart(R, Q, Z)
        x2 $in cart(R, Q, Z)
        x1[1] = x2[1]
        x1[2] = x2[2]
        =>:
            x1 = x2

by fn set as set: f $in fn(x1 R, y1 Q: x1 > y1, x1 > 2) Z

f(100,99) = f(100,99)
```

## 12. `by_for`

- Category: `proof pattern`
- System surface: `by for`
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

by for forall! n range(0, 3): n < 3:
    ...

by for:
    prove:
        forall x cart({1, 2}, {3, 4}):
            0 <= x[1] + x[2]
    do_nothing

scratch:
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

## 13. `by_induc`

- Category: `proof pattern`
- System surface: `by induc`
- Purpose: Shows ordinary induction.

```litex
# Minimal structured `by induc` example.
# `prove induc:` proves the step under the default induction hypotheses.

abstract_prop p(a)

know:
    $p(0)
    forall n Z:
        n >= 0
        $p(n)
        =>:
            $p(n + 1)

by induc n from 0:
    prove:
        $p(n)

    prove from n = 0:
        $p(0)

    prove induc:
        $p(n + 1)

forall n Z:
    n >= 0
    =>:
        $p(n)
```

## 14. `by_induc_example1`

- Category: `proof pattern`
- System surface: `by induc`
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

## 15. `by_induc_example2`

- Category: `proof pattern`
- System surface: `by induc`
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

## 16. `by_symmetric_reflexive_antisymmetric_prop`

- Category: `proof pattern`
- System surface: `relation-property proof patterns`
- Purpose: Shows reflexive, symmetric, and antisymmetric proposition helpers.

```litex
scratch:
    prop same_obj(x set, y set):
        x = y

    abstract_prop r(x, y)
    abstract_prop p(x, y)

    by reflexive_prop:
        prove:
            forall x set:
                $same_obj(x, x)
        x = x

    by reflexive_prop:
        prove:
            forall x set:
                $r(x, x)
        know $r(x, x)

    by symmetric_prop:
        prove:
            forall x, y set:
                $p(x, y)
                =>:
                    $p(y, x)
        know $p(y, x)

    by antisymmetric_prop:
        prove:
            forall x, y set:
                $p(x, y)
                $p(y, x)
                =>:
                    x = y
        know x = y

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

## 17. `by_transitive_prop`

- Category: `proof pattern`
- System surface: `by transitive_prop`
- Purpose: Shows transitive proposition chaining.

```litex

abstract_prop p(x, y)

by transitive_prop:
    prove:
        forall x, y, z set:
            $p(x, y)
            $p(y, z)
            =>:
                $p(x, z)
    know $p(x, z)

have a, b, c set

know a $p b $p c

a $p b $p c
```

## 18. `by_tuple`

- Category: `obj`
- System surface: `tuple object`
- Purpose: Shows tuple construction as a set object.

```litex
by tuple as set: (1, 2)
```

## 19. `by_zorn_lemma`

- Category: `proof pattern`
- System surface: `by zorn_lemma`
- Purpose: Shows the Zorn-lemma proof interface.

```litex
have s set
abstract_prop leq(x, y)

by zorn_lemma: set s, prop leq:
    know $is_nonempty_set(s)
    know:
        forall x s:
            $leq(x, x)
        forall x, y, z s:
            $leq(x, y)
            $leq(y, z)
            =>:
                $leq(x, z)
        forall x, y s:
            $leq(x, y)
            $leq(y, x)
            =>:
                x = y
        forall C power_set(s):
            forall x, y C:
                $leq(x, y) or $leq(y, x)
            =>:
                exist u s st {forall! x C: {$leq(x, u)}}

exist m s st {forall! x s: $leq(m, x) => {x = m}}
```

## 20. `claim`

- Category: `stmt`
- System surface: `claim`
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

## 21. `exist`

- Category: `fact`
- System surface: `exist and exist!`
- Purpose: Shows existential and unique-existence facts.

```litex
scratch:
    abstract_prop p(a, b)
    abstract_prop q(a, b)

    know:
        exist! a, b, c R st {$p(a, b), $q(b, c)}
        forall a1, b1, c1 R, a2, b2, c2 R:
            $p(a1, b1)
            $q(b1, c1)
            $p(a2, b2)
            $q(b2, c2)
            =>:
                (a1, b1, c1) = (a2, b2, c2)

    # exist can be proved by exist!
    exist a, b, c R st {$p(a, b), $q(b, c)}
    exist! a, b, c R st {$p(a, b), $q(b, c)}

    abstract_prop t(a)

    know:
        exist a R st {$t(a)}
        forall a1, a2 R:
            $t(a1)
            $t(a2)
            =>:
                a1 = a2

scratch:
    abstract_prop p(x, y)

    know:
        exist! a R st {$p(a, 1)}
        not exist x R st {$p(x, 2)}

    exist b R st {$p(b, 1)}
    exist! c R st {$p(c, 1)}
    not exist y R st {$p(y, 2)}

scratch:
    abstract_prop p(x, y)
    abstract_prop q(x, y)

    know:
        forall a R:
            exist! b R st {$p(a, b)}

        forall a R:
            not exist b R st {$q(a, b)}

    exist b R st {$p(1, b)}
    exist! c R st {$p(1, c)}
    not exist b R st {$q(1, b)}

scratch:
    know exist a R st {a > 0, a < 1}

    exist b R st {b > 0, b < 1}

    have by exist c R st {c > 0, c < 1}: number_larger_than_0_and_smaller_than_1
    number_larger_than_0_and_smaller_than_1 > 0
    number_larger_than_0_and_smaller_than_1 < 1
```

## 22. `exist_fact_that_contains_forall`

- Category: `fact`
- System surface: `exist fact with forall body`
- Purpose: Shows extracting an existential whose witness carries a universal fact.

```litex
abstract_prop p(x)
abstract_prop q(x, y)

know exist a R st {forall! b R: $p(b) => {$q(a, b)}, $p(a)}

exist a R st {forall! b R: $p(b) => {$q(a, b)}, $p(a)}
```

## 23. `forall_in_forall`

- Category: `stmt`
- System surface: `nested forall`
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

know:
    forall m, n N:
        0 < m < n
        =>:
            m % n = m

claim:
    prove:
        forall n N:
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

scratch:
    abstract_prop p(a, b, c, d)
    abstract_prop q(a, b)

    know:
        forall a, b R:
            forall c, d R:
                $p(a, b, c, d)
            =>:
                $q(a, b)

        forall c, d R:
            $p(1, 2, c, d)
    $q(1, 2)
```

## 24. `have_obj_by_exist_facts`

- Category: `stmt`
- System surface: `have by exist`
- Purpose: Shows naming witnesses from existential facts.

```litex
know exist x R st {x > 0}

have x R:
    x > 0

x > 0

know exist a, b R st {a > b, b > 0}

have a, b R:
    a > b
    b > 0

a > b
b > 0

template<s set: s = s>:
    have positive_choice R:
        positive_choice > 0

\positive_choice<R> > 0
```

## 25. `inline_forall`

- Category: `stmt`
- System surface: `forall!`
- Purpose: Shows inline universal facts inside proposition bodies.

```litex
know forall! a R: a > 0 => { a + 1 > 1 }

forall! a R: a > 0 => { a + 1 > 1 }

know forall! a R: forall! b R: b > 0 => { a > b } => { a > 0 }

forall! a R: forall! b R: b > 0 => { a > b } => { a > 0 }

know forall! a R: a > 0 => { a + 1 > 1, a + 2 > 2 }

forall! a R: a > 0 => { a + 1 > 1, a + 2 > 2 }

know forall! a R: { a > 0, a + 1 > 1 }

forall! a R: { a > 0, a + 1 > 1 }

abstract_prop p(x)
abstract_prop q(x, y)

know forall x R:
    forall y R:
        $p(y)
        =>:
            $q(x, y)
    =>:
        $p(x)

forall! x R: forall! y R: $p(y) => {$q(x, y)} => {$p(x)}
```

## 26. `logic`

- Category: `proof pattern`
- System surface: `propositional logic`
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
scratch:
    know:
        $p() or $q()
        not $p()

    by cases:
        prove:
            $q()
        case $p():
            impossible not $p()
        case $q():
            do_nothing

# You can also formalize this in this way: Use forall without parameters.
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

## 27. `match_obj_with_free_param_in_forall`

- Category: `fact`
- System surface: `forall matching`
- Purpose: Shows matching free parameters in universal facts.

```litex
scratch:
    abstract_prop p(a, b)
    abstract_prop q(a, b)

    know forall a, b R:
        $p(a, {x R: $p(x, b)})
        $q(1, {x R: $q(a + b, x)})

    prove:
        $p(1, {x R: $p(x, 2)})
        # $p(1, {x R: $p(x, x)}) 是unknown，因为x作为set builder的参数不能匹配b
        $q(1, {x R: $q(1 + 2, x)})
```

## 28. `max_min_bounds`

- Category: `builtin rule`
- System surface: `max/min bounds`
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

## 29. `membership_in_set_valued_fn`

- Category: `fact`
- System surface: `set-valued function membership`
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

## 30. `not_exist`

- Category: `fact`
- System surface: `not exist`
- Purpose: Shows reasoning from negated existential facts.

```litex
abstract_prop p(x, y)

know not exist x R st {$p(x, 1)}

forall x R:
    not $p(x, 1)

abstract_prop q(x, y)

know not exist x R st {$q(x, 1), $q(x, 2)}

forall x R:
    not $q(x, 1) or not $q(x, 2)
```

## 31. `not_forall`

- Category: `fact`
- System surface: `not forall`
- Purpose: Shows extracting counterexamples from negated universal facts.

```litex
know not forall x R:
    x > 0

not forall x R:
    x > 0

abstract_prop p(x)
abstract_prop p2(x)
abstract_prop q(x)
abstract_prop q2(x)

know not forall x R:
    $p(x)
    $p2(x)
    =>:
        $q(x)
        $q2(x)



exist x R st {$p(x), $p2(x), not $q(x) or not $q2(x)}
```

## 32. `or_fact`

- Category: `fact`
- System surface: `or fact`
- Purpose: Shows disjunction introduction and use.

```litex
scratch:
    abstract_prop p(a, b)
    abstract_prop q(a, b)

    know $p(1, 2) or $q(1, 2)

    $p(1, 2) or $q(1, 2)

scratch:
    let x Z:
        x >= 1

    x = 1 or x = 2 or x = 3 or x = 4 or x > 4

scratch:
    let a, x Z:
        x >= a

    x = a or x = a + 1 or x = a + 2 or x > a + 2

scratch:
    abstract_prop p(a, b, c)
    abstract_prop q(a, b, c)

    know $p(1, 2, 3) or $q(1, 2, 3)

    let a, b, c R:
        a = 1
        b = 2
        c = 3

    $p(a, b, c) or $q(a, b, c)

scratch:
    abstract_prop p(a, b)
    abstract_prop q(a, b)

    know:
        forall a, b R:
            $p(a, b) or $q(a, b)

    $p(1, 2) or $q(1, 2)
```

## 33. `power_builtin_rules`

- Category: `builtin rule`
- System surface: `power rules`
- Purpose: Shows builtin exponent algebra and order rules.

```litex
# Power builtin rules cover common exponent algebra and order patterns.
# Example shape: use the equality/order directly instead of a local `know`.

0^0 = 1

forall x Q, n, m N:
    x^n * x^m = x^(n + m)

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

forall x Q, n N_pos:
    abs(x^n) = abs(x)^n

forall x Q_nz, n, m Z:
    x^n * x^m = x^(n + m)

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

## 34. `set_algebra_builtin_rules`

- Category: `builtin rule`
- System surface: `set algebra rules`
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

have A, B, C set
intersect(A, B) = intersect(B, A)
intersect(intersect(A, B), C) = intersect(A, intersect(B, C))
intersect(A, union(B, C)) = union(intersect(A, B), intersect(A, C))
set_minus(A, union(B, C)) = intersect(set_minus(A, B), set_minus(A, C))
set_minus(A, intersect(B, C)) = union(set_minus(A, B), set_minus(A, C))
```

## 35. `strategy`

- Category: `proof pattern`
- System surface: `strategy`
- Purpose: Shows reusable proof strategies over abstract propositions.

```litex
abstract_prop p(x)
abstract_prop q(x)
abstract_prop r(x)

strategy prove_p:
    prove:
        forall x R:
            x = 1
            =>:
                $p(x)

    know:
        forall y R:
            y = 1
            =>:
                $p(y)

# A verified strategy is enabled immediately after definition.
$p(1)

strategy prove_q:
    prove:
        forall x R:
            x = x
            =>:
                $q(x)

    know:
        forall y R:
            y = y
            =>:
                $q(y)

# A stopped strategy still leaves its proved forall available to ordinary proofs.
strategy prove_r:
    prove:
        forall x R:
            x = 1
            =>:
                $r(x)

    know:
        forall y R:
            y = 1
            =>:
                $r(y)

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

## 36. `strong_induc`

- Category: `proof pattern`
- System surface: `by strong_induc`
- Purpose: Shows strong induction over integers.

```litex
# Strong induction: `know` gives base + the strong step; the checker matches the generated obligation.
# Same conclusion as `by induc` when both are available: forall n >= 0, P(n).

abstract_prop p(a)

know:
    $p(0)
    forall n Z:
        n >= 0
        forall y Z:
            y >= 0
            y <= n
            =>:
                $p(y)
        =>:
            $p(n + 1)

by strong_induc n from 0:
    prove:
        $p(n)

    prove from n = 0:
        $p(0)

    prove strong_induc:
        $p(n + 1)

forall n Z:
    n >= 0
    =>:
        $p(n)
```

## 37. `syllogism`

- Category: `proof pattern`
- System surface: `syllogism`
- Purpose: Shows a minimal universal-instantiation argument.

```litex
have human nonempty_set, Socrates human
abstract_prop mortal(x)

know forall x human:
    $mortal(x)

$mortal(Socrates)
```

## 38. `thm`

- Category: `stmt`
- System surface: `thm and by thm`
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

# A proved theorem is named-only. Use an explicit theorem call when you want
# to release its instantiated then-facts into the current context.
abstract_prop thm_match_p(x)
abstract_prop thm_match_q(x)

thm thm_named_only:
    prove:
        forall x R:
            $thm_match_p(x)
            =>:
                $thm_match_q(x)
    know $thm_match_q(x)

know $thm_match_p(1)
by thm thm_named_only(1)
$thm_match_q(1)
```

## 39. `use_builtin_code_to_verify`

- Category: `builtin rule`
- System surface: `builtin code verification`
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

## 40. `use_forall_and_prop_def_to_verify_atomic_fact`

- Category: `fact`
- System surface: `prop definition plus forall facts`
- Purpose: Shows atomic fact verification through prop definitions and forall facts.

```litex
scratch:
    abstract_prop q(x, y, z)

    prop p(x, y R):
        x > y
        forall t R:
            $q(x, y, t)

    have a, b R

    know $p(a, b)

    a > b

    $q(a, b, 2)

scratch:
    abstract_prop p(a)

    have b R, c R

    know forall a R:
        $p(a + b)
        =>:
            $p(a)

    know $p(c + b)

    $p(c)
```

## 41. `use_forall_arithmetic_to_prove`

- Category: `fact`
- System surface: `forall arithmetic matching`
- Purpose: Shows arithmetic instantiation of universal facts.

```litex
scratch:
    abs(-1) = 1

scratch:
    abstract_prop q(a)

    know forall a R:
        $q(-a)

    $q(1)

scratch:
    abstract_prop p(a)

    know forall a R:
        $p(2 * a)
        
    $p(1)

scratch:
    abstract_prop p(a)

    know forall a R:
        $p(a * 2)
        
    $p(1)

scratch:
    abstract_prop p(a)

    know forall a R:
        $p(a / 2)

    $p(1)

scratch:
    abstract_prop p(a)

    know forall a R:
        $p(2 + a)

    $p(1)

scratch:
    abstract_prop p(a)

    know forall a R:
        $p(2 - a)

    $p(1)

scratch:
    abstract_prop p(a)

    know forall a R:
        $p(a + 2)

    $p(1)

scratch:
    abstract_prop p(a)

    know forall a R:
        $p(a - 2)

    $p(1)
```

## 42. `verify_by_resolving_atomic_fact_arg`

- Category: `fact`
- System surface: `atomic argument resolution`
- Purpose: Shows resolving an atomic proposition argument before matching.

```litex
abstract_prop p(a)

know forall a R:
    $p(a)
    =>:
        $p(a + 1)

know $p(1)

$p(2)
```

## 43. `witness_exist`

- Category: `proof pattern`
- System surface: `witness exist`
- Purpose: Shows explicit witnesses for existential facts.

```litex
witness exist x, y R st {x > y} from 1, 0:
    1 > 0

exist x, y R st {x > y}
```

## 44. `witness_nonempty`

- Category: `proof pattern`
- System surface: `witness nonempty`
- Purpose: Shows explicit witnesses for nonempty sets.

```litex
have s set

witness $is_nonempty_set(s) from 1:
    know 1 $in s

$is_nonempty_set(s)
```
