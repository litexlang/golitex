# Litex Examples

These examples are a learning path from small checked facts to small mathematical worlds, not a dump of test files.

## Reading Path

1. [Start Here](#start-here) - read this first when you want a 10-minute feel for the basic Litex loop.
2. [Proof Patterns](#proof-patterns) - use this when you know the fact you want and need the proof move: cases, contradiction, witnesses, theorem calls, induction, and related patterns.
3. [Builtin Math](#builtin-math) - use this when you want to know which arithmetic, order, set, function, and object facts Litex already knows.
4. [Objects And Statements](#objects-and-statements) - use this as the compact reference for object syntax and statement behavior.
5. [Small Worlds](#small-worlds) - read this after the syntax reference to see how objects, predicates, structs, and templates combine.
6. [Case Studies](#case-studies) - use this when you want larger worked examples and can tolerate abstract assumptions in some studies.

## What Is Internal?

`examples/_internal/` contains regression tests, scratch files, fixtures, and implementation-oriented checks. It is useful for developers, but it is not the right entry point for a new reader.

`examples/tmp.lit` is a local scratch file used by short verifier experiments.

---

## Start Here

This page is a short first run through Litex. Each code block is standalone and
runnable, but the ideas build in order: check one fact, grow a context, define
a function, define a predicate, give a witness, then package a tiny proof.

### 1. A Fact Is Checked

Litex reads a file from top to bottom. Once a line succeeds, later lines may
use it.

```litex
have x R = 2

x + 1 = 3
x^2 = 4
```

The first line introduces a real number `x` and records `x = 2`. The next two
lines are ordinary facts. Litex checks them from the current context and exact
arithmetic.

### 2. The Context Grows

New names can depend on earlier names. After `y` is introduced, it becomes part
of the same checked context.

```litex
have x R = 2
have y R = x + 1

y = 3
y^2 = 9
x + y = 5
```

### 3. A Function Can Be Named

Function definitions are reusable facts about all inputs in their domain.

```litex
have fn square_plus_one(t R) R = t^2 + 1

square_plus_one(3) = 10
square_plus_one(0) = 1

forall x R:
    square_plus_one(x) = x^2 + 1
```

### 4. A Predicate Gives A Shape A Name

A `prop` defines a reusable predicate. Calling the predicate with `$...` asks
Litex to unfold and verify the defining facts.

```litex
prop is_unit_distance_from_two(t R):
    abs(t - 2) = 1

$is_unit_distance_from_two(3)
```

### 5. Existential Facts Use Witnesses

To prove an existential fact, give the object that witnesses it. Once the
existential fact is known, `obtain` opens a local name for some witness.

```litex
witness exist x R st {x^2 = 4} from 2:
    2^2 = 4

obtain root from exist x R st {x^2 = 4}
root $in R
root^2 = 4
```

### 6. A Small Proof Block Packages A Fact

Use `claim` when the final fact needs a few local steps. The proof body runs in
the context introduced by the goal.

```litex
claim:
    ? forall x R:
        x = 2
        =>:
            (x + 1)^2 = 9
    x + 1 = 3
    (x + 1)^2 = 9
```

At this point the main loop is visible: write a mathematical fact, let Litex
check it from the current context, and use the accepted fact later.

---

## Proof Patterns

This is a proof-action menu, not the first tutorial. If you are new to Litex,
start with [Start Here](#start-here), then come back here when you need a
specific move.

Small proof moves come up again and again: conjunctions, cases, contradiction,
witnesses, induction, theorem reuse, and named facts.

The purpose line says when the move is useful. The code blocks keep the setting
small so the proof pattern is easy to recognize.

### 1. Conjunctions: Prove And Reuse Both Sides

- Category: `fact`
- Purpose: Shows conjunction introduction and reuse.

```litex
1 = 1 and 1 + 2 = 3
```

### 2. Matching An Atomic Predicate

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

### 3. Choice Functions From Nonempty Sets

- Category: `proof pattern`
- Purpose: Shows the choice-function proof form over a set of nonempty sets.

```litex
claim:
    ? forall S set:
        forall A S:
            $is_nonempty_set(A)
        =>:
            exist f fn(A S) cup(S) st {forall! A S => {f(A) $in A}}

    by axiom_of_choice: set S
```

### 3.1. General Cartesian Products As Choice Functions

- Category: `proof pattern`
- Purpose: Uses the built-in general Cartesian product as a choice-function set.

```litex
have I set
have s nonempty_set
have g fn(alpha I) s

trust forall X s:
    $is_nonempty_set(X)

$is_nonempty_set(general_cart(I, s, g))
general_cart(I, s, g) = {f fn(t I)cup(s): forall! alpha I => {f(alpha) $in g(alpha)}}

have c general_cart(I, s, g)
c $in fn(t I)cup(s)

forall alpha I:
    c(alpha) $in g(alpha)
```

### 4. Case Splits With `by cases`

- Category: `proof pattern`
- Purpose: Shows case splits over proposition and order alternatives.

```litex
sketch:
    by cases:
        ? 1 + 1 = 2
        case 1 + 1 = 2:
            do_nothing
        case 1 + 1 != 2:
            1 + 1 = 2
            impossible 1 + 1 = 2
```

```litex
abstract_prop p(x)

claim:
    ? forall x R:
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
        ? $p(x)

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
## Real-line trichotomy is available in the common equality-first order.
forall x, y R:
    x = y or x < y or x > y
```

### 5. Contradiction With `by contra`

- Category: `proof pattern`
- Purpose: Shows contradiction-based proof.

```litex
abstract_prop p(a)

claim:
    ? forall b, c R:
        forall a R:
            $p(a + b)
            =>:
                $p(a)
        not $p(c)
        =>:
            not $p(c + b)
    by contra:
        ? not $p(c + b)
        impossible $p(c)

by contra 1 = 1:
    impossible 1 != 1

by contra:
    ? not exist x R st {x != x}
    obtain a from exist x R st {x != x}
    impossible a = a

by contra:
    ? exist x R st {x = x}
    impossible 0 = 0
```

### 6. Enumerating A Closed Integer Range

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

### 7. Enumerating A Finite Set

- Category: `proof pattern`
- Purpose: Shows finite-set enumeration.

```litex
by enumerate finite_set:
    ? forall a {1, 2}, b {3, 4}:
        a > 1
        b > 3
        =>:
            a = 2
            b = 4

by enumerate finite_set forall! a {1, 2}, b {3, 4}: a > 1 and b > 3 => {(a, b) = (2, 4)}:
    ...
```

### 8. Enumerating A Half-Open Range

- Category: `proof pattern`
- Purpose: Shows finite range and closed-range enumeration syntax.

```litex
claim:
    ? forall a range(7, 8):
        a = 7
    by enumerate range: a $in range(7, 8)
```

```litex
claim:
    ? forall x range(1, 3):
        x = 1 or x = 2
    by enumerate range: x $in range(1, 3)
```

```litex
claim:
    ? forall y closed_range(1, 3):
        y = 1 or y = 2 or y = 3
    by enumerate closed_range: y $in 1...3
```

### 9. Set Equality By Extension

- Category: `proof pattern`
- Purpose: Shows set/function extensional equality.

```litex
by extension:
    ? {1, 2} = {2, 1}
    by enumerate finite_set:
        ? forall x {1, 2}:
            x $in {2, 1}
    by enumerate finite_set:
        ? forall y {2, 1}:
            y $in {1, 2}

{1, 2} = {2, 1}

by extension {1} = {1}
```

### 10. Repeating A Step With `by for`

- Category: `proof pattern`
- Purpose: Shows bounded universal proof automation.

```litex
by for:
    ? forall n range(0, 10):
        n < 10
    do_nothing

by for:
    ? forall n closed_range(0, 10):
        n <= 10
    do_nothing

by for forall! n range(0, 3) => {n < 3}:
    ...

by for:
    ? forall x cart({1, 2}, {3, 4}):
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
        ? forall n range(2, 2):
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

### 11. Induction With `by induc`

- Category: `proof pattern`
- Purpose: Shows ordinary induction.

```litex
abstract_prop p(a)

claim:
    ? forall n Z:
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
        ? $p(n)

        ? from n = 0:
            $p(0)

        ? induc:
            $p(n + 1)
```

### 12. Induction For A Product Divisibility Fact

- Category: `proof pattern`
- Purpose: Shows a small induction proof.

```litex
claim:
    ? forall n N:
        2 ^ n >= n + 1
    by induc n from 0:
        ? 2 ^ n >= n + 1
        2^0 = 1 >= 0 + 1

        forall m Z:
            m >= 0
            2^m >= m + 1
            =>:
                2^m * 2^1 >= (m+1) * 2
                2 ^ (m + 1) = 2 ^ m * 2^1 >= (m+1) * 2 = (m + 1) + (m + 1) >= m + 1 + 1
```

### 13. Induction For A Closed-Form Sum

- Category: `proof pattern`
- Purpose: Shows a larger induction proof with arithmetic state.

```litex
claim:
    ? forall b fn(x Z: x >= 0) Z, i Z:
        forall y Z:
            y >= 0
            =>:
                b(y+1) = b(y)^ 2 - 2
        b(0) = 3
        i >= 0
        =>:
            b(i) % 2 = 1
    by induc i from 0:
        ? b(i) % 2 = 1
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

### 14. Registering Symmetry, Reflexivity, And Order Properties

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
        ? forall x set:
            $same_obj(x, x)
        x = x

    by reflexive_prop:
        ? forall x set:
            $r(x, x)
        x = x

    by symmetric_prop:
        ? forall x, y set:
            $p(x, y)
            =>:
                $p(y, x)
        x = y
        y = x

    by antisymmetric_prop:
        ? forall x, y set:
            $p(x, y)
            $p(y, x)
            =>:
                x = y
        x = y

    claim:
        ? forall a set:
            $same_obj(a, a)

    claim:
        ? forall a set:
            $r(a, a)

    claim:
        ? forall a, b set:
            $p(a, b)
            =>:
                $p(b, a)

    claim:
        ? forall a, b set:
            $p(a, b)
            $p(b, a)
            =>:
                a = b
```

### 15. Registering Transitivity For A Predicate

- Category: `proof pattern`
- Purpose: Shows transitive proposition chaining.

```litex
prop p(x set, y set):
    x = y

by transitive_prop:
    ? forall x, y, z set:
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

### 16. Local Proof Blocks With `claim`

- Category: `stmt`
- Purpose: Shows local claim statements and reuse.

```litex
claim:
    ? 1 = 1 and 1 + 2 = 3
    1 = 1
    1 + 2 = 3

claim:
    ? forall a R:
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

### 17. Proving Existential Facts

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

### 18. Existentials Whose Body Contains A Universal Fact

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

### 19. Nested Universal Facts

- Category: `stmt`
- Purpose: Shows nested universal facts and local instantiation.

```litex
## Let a be a real number and suppose that for all real numbers x, a <= x^2 - 2x. Show that a <= -1.


forall a R:
    forall x R:
        a <= x^2 - 2 * x
    =>:
        a <= 1^2 - 2 * 1 = -1

"""
Let n be a natural number which is a factor of every natural number m. Show that n = 1.
"""

claim:
    ? forall n N:
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
        ? n <= 1
        n > 1
        1 % n = 0
        1 % n = 1
        impossible 0 = 1

    n $in closed_range(0, 1)
    by for:
        ? forall m closed_range(0, 1):
            m = 0 or m = 1

    n =  0 or n = 1
    by cases:
        ? n = 1
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

### 20. Inline Universal Facts

- Category: `stmt`
- Purpose: Shows inline universal facts inside proposition bodies.

```litex
forall! a R: a > 0 => { a + 1 > 1 }

forall! a R: a > 0 => {a + 1 > 1 and a + 2 > 2}
```

### 21. Basic Logic Patterns

- Category: `proof pattern`
- Purpose: Shows propositional reasoning, implication, cases, and negation.

```litex
abstract_prop p()
abstract_prop q()
abstract_prop r()

## 5.1.1
## 由 P∨Q 与 ¬Q 得 P：析取分情形，第二支与 ¬Q 矛盾。
"""
If P ∨ Q and ¬ Q, then P.
"""
```

```litex
abstract_prop p()
abstract_prop q()
abstract_prop r()

claim:
    ? forall:
        $p() or $q()
        not $p()
        =>:
            $q()
    by cases:
        ? $q()
        case $p():
            impossible not $p()
        case $q():
            do_nothing

"""
## P → P ∨ ¬Q：由 P 可左注入得 P∨(¬Q)（书本 left）。
"""
"""
P implies P ∨ (not Q).
"""

forall:
    $p()
    =>:
        $p() or not $q()

## 5.1.4
## 两公式逻辑等价：指其 ↔ 在 Lean 可证（尚有一处 tactic 在 5.2 才齐全，故有些等价暂时无法演示）。
## P∨P ↔ P：左到右析取消去；右到左重复左注入。
"""
(P ∨ P) is logically equivalent to P.
"""
claim:
    ? forall:
        $p() or $p()
        =>:
            $p()
    by cases:
        ? $p()
        case $p():
            do_nothing
        case $p():
            do_nothing

forall:
    =>:
        $p() or $p()
    <=>:
        $p()

## 5.1.5
"""
P ∧ (Q ∨ R) is logically equivalent to (P ∧ Q) ∨ (P ∧ R).
"""
claim:
    ? forall:
        $p()
        $q() or $r()
        =>:
            $p() and $q() or $p() and $r()

    by cases:
        ? $p() and $q() or $p() and $r()
        case $q():
            $p() and $q()
        case $r():
            $p() and $r()

## 5.1.6
## 谓词 P(x)、Q(x)：由 ∀x Px 与 ∀x Qx 得 ∀x (Px∧Qx)。

abstract_prop P(x)
abstract_prop P2(x)

forall x set:
    $P(x)
    $P2(x)
    =>:
        $P(x) and $P2(x)

###标准库中应有quick prime check--能够check一个数是否为素数--函数应该要能够调用

#### 答：用 by for 从 2 到 n-1做迭代，证明 d % i != 0就能证明了

## 5.2.6
## 命题逻辑：¬¬P ⇒ P（「负负得正」）需排中律：对 P 本身作 by_cases。
"""
From ¬¬P deduce P (using excluded middle).
"""

forall:
    not not $p()
    =>:
        $p()
```

### 22. Matching A Free Parameter In A Universal Fact

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

### 23. Max And Min Bounds

- Category: `builtin rule`
- Purpose: Shows builtin max/min order consequences.

```litex
## Max/min order bounds used by sequence-limit estimates.

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

### 24. Membership In A Set-Valued Function

- Category: `fact`
- Purpose: Shows membership unfolding for set-valued functions.

```litex
## Set-valued have fn applications unfold one layer for membership.

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

### 25. Proving That No Witness Exists

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

### 26. Refuting A Universal Claim

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

### 27. Reusing Disjunctions

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

### 28. Power Rules

- Category: `builtin rule`
- Purpose: Shows builtin exponent algebra and order rules.

```litex
## Power builtin rules cover common exponent algebra and order patterns.
## Example shape: use the equality or order relation directly.

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

### 29. Set Algebra Rules

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

### 30. Defining And Controlling Strategies

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
    ? forall x R:
        x = 1
        =>:
            $p(x)
    x = 1

## A verified strategy is enabled immediately after definition.
$p(1)

strategy prove_q:
    ? forall x R:
        x = x
        =>:
            $q(x)
    x = x

## A stopped strategy still leaves its proved forall available to ordinary proofs.
strategy prove_r:
    ? forall x R:
        x = 1
        =>:
            $r(x)
    x = 1

stop strategy prove_r
claim:
    ? forall z R:
        z = 1
        =>:
            $r(z)

## Same environment: stop followed by use re-enables the same strategy key.
stop strategy prove_p
use strategy prove_p
$p(1)

## Parent environment is stopped, but a child environment can enable the strategy locally.
use strategy prove_q
stop strategy prove_q
claim:
    ? $q(2)
    use strategy prove_q

## Back in the parent environment, use removes the parent stop and re-enables it.
use strategy prove_q
$q(3)
```

### 31. Strong Induction

- Category: `proof pattern`
- Purpose: Shows strong induction over integers.

```litex
abstract_prop p(a)

claim:
    ? forall n Z:
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
        ? $p(n)

        ? from n = 0:
            $p(0)

        ? strong_induc:
            $p(n + 1)
```

### 32. A Divisibility Implication by Witnesses

- Category: `proof pattern`
- Purpose: Shows a universal implication proved by unpacking and constructing
  existential witnesses.

```litex
prop can_be_divided_by_8(x Z):
    exist d Z st {x = 8 * d}

prop can_be_divided_by_2(x Z):
    exist d Z st {x = 2 * d}

claim:
    ? forall x Z:
        $can_be_divided_by_8(x)
        =>:
            $can_be_divided_by_2(x)
    obtain d from exist d Z st {x = 8 * d}
    witness exist e Z st {x = 2 * e} from 4 * d:
        x = 8 * d
        8 * d = 2 * (4 * d)

witness exist d Z st {8 = 1 * d} from 8
$can_be_divided_by_8(8)
$can_be_divided_by_2(8)
```

### 33. Named Theorems With `thm`

- Category: `stmt`
- Purpose: Shows theorem declaration, aliases, and theorem application.

```litex
## Basic named theorem with aliases and no domain facts.
thm thm_refl_r, thm_refl_r_alias:
    ? forall x R:
        x = x

by thm thm_refl_r(0)
0 = 0

by thm thm_refl_r_alias(0)
0 = 0

## A theorem alias can use a local-language name while the original theorem
## keeps an English/source-facing name.
thm self_eq_en:
    ? forall x R:
        x = x
    x = x

alias thm 自反等式 <=> self_eq_en
by thm 自反等式(1)
1 = 1

## A theorem with one domain fact.
thm thm_one_succ:
    ? forall x R:
        x = 1
        =>:
            x + 1 = 2
    x + 1 = 1 + 1 = 2

by thm thm_one_succ(1)
1 + 1 = 2

## Multiple arguments and multiple domain facts.
thm thm_add_equal_with_unit:
    ? forall a, b, c R:
        a = b
        c = 1
        =>:
            a + c = b + 1
    a + c = b + c = b + 1

by thm thm_add_equal_with_unit(2, 2, 1)
2 + 1 = 2 + 1

## Multiple then-facts are all released by the named theorem call.
thm thm_many_then:
    ? forall x R:
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

## A theorem can release an and-fact.
thm thm_and_then:
    ? forall x R:
        x = 0
        =>:
            x = 0 and x + 1 = 1
    x = 0
    x + 1 = 0 + 1 = 1
    x = 0 and x + 1 = 1

by thm thm_and_then(0)
0 + 1 = 1

## A theorem can release a chain fact.
thm thm_chain_then:
    ? forall x R:
        x = 1
        =>:
            x + 1 = 1 + 1 = 2
    x + 1 = 1 + 1 = 2

by thm thm_chain_then(1)
1 + 1 = 2

## The explicit call works inside a claim proof.
claim:
    ? forall x R:
        x = 1
        =>:
            x + 1 = 2
    by thm thm_one_succ(x)

## A named theorem may use another named theorem in its proof.
thm thm_use_thm_inside_thm:
    ? forall x R:
        x = 1
        =>:
            x + 2 = 3
    by thm thm_one_succ(x)
    x + 2 = 1 + 2 = 3

by thm thm_use_thm_inside_thm(1)
1 + 2 = 3

## Argument type checking still applies for theorem calls.
thm thm_nat_refl:
    ? forall n N:
        n = n

by thm thm_nat_refl(1)
1 = 1

## A proved theorem is also stored as a forall fact. After the domain fact is
## known, ordinary fact checking can use the theorem without an explicit call.
prop thm_match_p(x R):
    x = 1
prop thm_match_q(x R):
    x = 1

thm thm_stored_forall:
    ? forall x R:
        $thm_match_p(x)
        =>:
            $thm_match_q(x)
    x = 1

$thm_match_p(1)
$thm_match_q(1)

## The explicit theorem call remains available when theorem-instantiation
## output is useful.
by thm thm_stored_forall(1)
```

### 34. Using Builtin Facts Directly

- Category: `builtin rule`
- Purpose: Shows facts verified from builtin background code.

```litex
claim:
    ? forall a, b R:
        a < b or a = b or a > b

claim:
    ? forall a, b R:
        a <= b
        =>:
            a = b or a < b

```

### 35. Using Universal Facts And Predicate Definitions

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

### 36. Arithmetic Inside Universal Facts

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

### 37. Resolving Predicate Arguments By Equality

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

### 38. Witnesses For Existential Facts

- Category: `proof pattern`
- Purpose: Shows explicit witnesses for existential facts.

```litex
witness exist x, y R st {x > y} from 1, 0:
    1 > 0

exist x, y R st {x > y}
```

### 39. Witnesses For Nonempty Sets

- Category: `proof pattern`
- Purpose: Shows explicit witnesses for nonempty sets.

```litex
claim:
    ? forall s set:
        1 $in s
        =>:
            $is_nonempty_set(s)
    witness $is_nonempty_set(s) from 1:
        1 $in s
```

### 40. Nonzero Naturals Are Positive

- Category: `fact`
- Purpose: Shows that a nonzero natural number is a positive natural number.

```litex
forall n N:
    n != 0
    =>:
        n $in N_pos
```

### 41. Foundation/Regularity As A Proof Step

- Category: `proof pattern`
- Purpose: Shows the trusted regularity/foundation step for a nonempty set.

```litex
trust $is_nonempty_set({1, 2})

by regularity_axiom({1, 2})

exist x {1, 2} st {intersect(x, {1, 2}) = {}}
```

### 42. Membership In A Union Over Sets

- Category: `fact`
- Purpose: Shows introduction and elimination for family-union membership.

```litex
thm cup_intro_from_member:
    ? forall x set, F set, A set:
        A $in F
        x $in A
        =>:
            x $in cup(F)
    x $in cup(F)

thm cup_elim_to_exist:
    ? forall x set, F set:
        x $in cup(F)
        =>:
            exist A F st {x $in A}
    exist A F st {x $in A}
```

---

## Builtin Math

This is a map of mathematical rules Litex already knows, not a proof-writing
tutorial. Use it when a proof step feels like ordinary arithmetic, order, set,
function, or object reasoning and you want to see the checked shapes.

Examples cover builtin arithmetic, order, intervals, finite sets, powers,
absolute value, logs, sums, products, and modular arithmetic.


The examples keep the checked expression close to ordinary algebra. When a
section has several code blocks, the early ones show the basic rule and the
later ones show how the rule appears inside a proof.

### 1. Absolute Value

- Category: `builtin rule`
- Purpose: Shows builtin absolute-value inequalities and equalities.

```litex
forall a R:
    a >= 0
    =>:
        abs(a) = a

forall a R:
    a <= 0
    =>:
        abs(a) = -a

forall a R:
    0 <= abs(a)
    abs(a) = a or abs(a) = -a

forall a R:
    abs(a) = 0
    =>:
        a = 0

forall a R:
    a != 0
    =>:
        abs(a) > 0

forall a R:
    abs(a) = abs(-a)
    abs(-a) = abs(a)

forall x, y R:
    abs(x - y) = abs(y - x)

forall x, y R:
    abs(x * y) = abs(x) * abs(y)

forall x R:
    x <= abs(x)
    -x <= abs(x)

forall x, b R:
    x <= b
    -x <= b
    =>:
        abs(x) <= b

forall x, b R:
    x < b
    -x < b
    =>:
        abs(x) < b

forall x, y R:
    abs(x) <= abs(y)
    =>:
        -abs(y) <= x <= abs(y)

forall x, y R:
    abs(x) < abs(y)
    =>:
        -abs(y) < x < abs(y)

forall x, y R:
    abs(x) <= abs(y)
    0 <= y
    =>:
        -y <= x <= y

forall x, y R:
    abs(x) <= abs(y)
    y <= 0
    =>:
        y <= x <= -y

forall x, y R:
    abs(x + y) <= abs(x) + abs(y)
    abs(x - y) <= abs(x) + abs(y)

forall x, y R:
    abs(x) - abs(y) <= abs(x + y)
    abs(x) - abs(y) <= abs(x - y)

forall x R:
    x ^ 2 = abs(x) ^ 2
    x ^ 4 = abs(x) ^ 4

forall x R, n N:
    abs(x^n) = abs(x)^n

forall a, b R:
    0 <= a <= b
    =>:
        abs(a) <= abs(b)

forall a, b R, k N_pos:
    k % 2 = 0
    abs(a) <= abs(b)
    =>:
        a^k <= b^k
```

### 2. Basic Operators

- Category: `builtin rule`
- Purpose: Shows arithmetic operator typing and simplification.

```litex
+ = +
* = *
/ = /
% = %
^ = ^
+ $in fn(a, b R) R
- $in fn(a, b R) R
* $in fn(a, b R) R
/ $in fn(a R, b R: b != 0) R
% $in fn(a Z, b Z: b != 0) Z
^ $in fn(a, b R: a $in R_pos or a = 0 and b $in R_pos or a $in R_nz and b $in Z or b $in N) R
```

### 3. Common Builtin Rules

- Category: `builtin rule`
- Purpose: Shows common builtin arithmetic/order inference rules.

```litex
forall a, b R_pos:
    1 <= a
    =>:
        b <= a * b

forall a, b R_pos:
    1 < a
    =>:
        b < a * b

forall a, b R:
    a > 0
    b > 1
    =>:
        a / b < a

forall a, b, k R:
    0 <= k
    a <= b
    =>:
        k * a <= k * b

forall a, b, k R:
    0 < k
    a < b
    =>:
        k * a < k * b

forall a, b, c, d R:
    a < b
    c <= d
    =>:
        a - d < b - c

forall x, a, b R:
    x < b
    0 <= a
    =>:
        x - a < b

forall x, a, b R:
    x <= b
    0 < a
    =>:
        x - a < b

forall a, b, c R:
    a + c < b
    =>:
        a < b - c

forall a R:
    0 < a
    =>:
        a != 0
```

### 4. Square Roots

- Category: `builtin rule`
- Purpose: Shows square-root typing and identities.

```litex
sqrt(4) = sqrt(4)
sqrt(0) = 0
sqrt(1) = 1
sqrt(4) = 2
sqrt(452) = sqrt(4 * 113)
sqrt(452) = sqrt(4 * 113) = sqrt(4) * sqrt(113) = 2 * sqrt(113)

forall x R:
    x >= 0
    =>:
        (sqrt(x))^2 = x

forall x R:
    x > 0
    =>:
        sqrt(x) > 0

forall x R:
    x >= 0
    =>:
        sqrt(x) >= 0

forall x, a, b R:
    x >= 0
    a >= 0
    b >= 0
    x = a * b
    =>:
        sqrt(x) = sqrt(a) * sqrt(b)

forall x, a, b R:
    x >= 0
    a >= 0
    b > 0
    x = a / b
    =>:
        sqrt(x) = sqrt(a) / sqrt(b)

forall a, b R:
    a >= 0
    b >= 0
    a <= b
    =>:
        sqrt(a) <= sqrt(b)

forall a, b R:
    a >= 0
    b >= 0
    a < b
    =>:
        sqrt(a) < sqrt(b)
```

### 5. Closed Ranges

- Category: `obj`
- Purpose: Shows closed integer range objects.

```litex
have a 1...3

by closed_range as cases: a $in 1...3

a = 1 or a = 2 or a = 3
```

### 6. Closed And Half-Open Ranges

- Category: `obj`
- Purpose: Shows interaction between half-open and closed ranges.

```litex
forall i Z:
    1 < i < 5
    =>:
        i $in range(2, 5)
        i $in 2...4

forall i Z:
    1 <= i < 5
    =>:
        i $in range(1, 5)
        i $in 1...4

forall i Z:
    1 <= i <= 5
    =>:
        i $in range(1, 6)
        i $in 1...5

forall i Z:
    1 < i <= 5
    =>:
        i $in range(2, 6)
        i $in 2...5

finite_set_size(1...5) =  5
finite_set_size(range(1, 5)) = 4
```

### 7. Comparison And Chained Inequalities

- Category: `builtin rule`
- Purpose: Shows comparison facts and chained inequalities.

```litex
claim:
    ? forall a, b, c, d R:
        2 * a <= 3 * b
        1 <= a
        d = 2
        =>:
            d + a <= 5 * b
    d = 2 * 1 <= 2 * a
    a = (2*a)/2 <= (3*b)/2 = 1.5 * b
    0 <= (2/3)* a = (2 * a)/3 <= (3 * b)/3 = b
    d + a <= 2 * a + a <= 3 * b + a <= 3 * b +1.5*b = 4.5*b <= 5 * b
```

```litex
sketch:
    forall x N:
        x != 0
        =>:
            1 <= x
    forall x N:
        1 <= x
        =>:
            x != 0

forall x, y R:
    =>:
        x != 0 or y != 0
    <=>:
        x^2 + y^2 != 0

forall x, y R:
    =>:
        x*x + y*y != 0
    <=>:
        x != 0 or y != 0


forall a, b R:
    a <= 0
    b >= 0
    =>:
        a * b <= 0

forall a, b R:
    a >= 0
    b <= 0
    =>:
        a * b <= 0

forall a, b R:
    a >= 0
    b >= 0
    =>:
        a * b >= 0

forall a, b R:
    a <= 0
    b <= 0
    =>:
        a * b >= 0

forall a, b R:
    a < 0
    b > 0
    =>:
        a * b < 0

forall a, b R:
    a > 0
    b > 0
    =>:
        a * b > 0

forall a, b R:
    a < b
    =>:
        a^3 < b^3
        b^5 > a^5

by thm has_rational_between(0, 1)
exist q Q st {0 < q < 1}
```

```litex
sketch:
    forall t R_pos:
        t^2 < 4^2
        =>:
            t < 4

    forall t R_pos:
        t^3 < 4^3
        =>:
            t < 4

    forall t R_pos:
        t^4 < 4^4
        =>:
            t < 4

    forall t R_pos:
        t^5 < 4^5
        =>:
            t < 4

claim:
    ? forall t R_pos:
        t^6 < 4^6
        =>:
            t < 4
    by thm pos_pow_strict_order_reflects(t, 4, 6)
```

### 8. Products Under Small Bounds

- Category: `builtin rule`
- Purpose: Shows additional comparison simplification cases.

```litex
claim:
    ? forall x, y, epsilon R:
        forall a, b, c, d R:
            0 <= a < c
            0 <= b < d
            =>:
                a * b < c * d
        0 < epsilon
        epsilon <= 1
        abs(x) < epsilon
        abs(y) < epsilon
        =>:
            abs(x * y) < epsilon
    0 <= abs(x) < epsilon
    0 <= abs(y) < epsilon
    abs(x * y) = abs(x) * abs(y) < epsilon * epsilon <= epsilon * 1 = epsilon
```

### 9. Bounding A Product By One

- Category: `builtin rule`
- Purpose: Shows comparison over mixed arithmetic forms.

```litex
claim:
    ? forall a, b R:
        0 <= a
        a <= 1
        0 <= b
        b <= 1
        =>:
            a * b <= 1
    0 <= 1 - a
    0 <= (1 - a) * b = b - a * b
    a * b <= b <= 1
```

### 10. Nonnegativity Of Large Sums

- Category: `builtin rule`
- Purpose: Shows comparison facts that need local side conditions.

```litex
forall a, b, c, d, e, f, g, h, i, j, k, l, m, n, o R:
    0 <= a
    0 <= b
    0 <= c
    0 <= d
    0 <= e
    0 <= f
    0 <= g
    =>:
        0 <= a + b + c + d + e + f + g
        0 <= a + b + (h + i)^2 + (j + k)^4 + (l + m)^6 + (n + o)^8
        0 <= a^3 + b^3 + c^3 + d^3 + e^3 + f^3 + g^3
```

### 11. Division And Reciprocals

- Category: `builtin rule`
- Purpose: Shows division and reciprocal simplification.

```litex
forall a, b, c R_nz:
    a / (b / c) = a * c / b
    (a / b) / c = a / (b * c)

forall u R:
    u = 1 / (7 / 3)
    =>:
        u = 1 / (7 / 3) = 3 / 7
        7 * u = 3

forall u R:
    u = (-8 / 33) / (-8)
    =>:
        u = (-8 / 33) / (-8) = 1 / 33

forall u, v, w R:
    w != 0
    u = v / w
    =>:
        u * w = v
```

### 12. Finite Sets

- Category: `obj`
- Purpose: Shows finite-set literals, membership, and finite-set-size facts.

```litex
$is_finite_set({1, 2})
finite_set_size({1, 2, 3}) = 3
finite_set_size(cart({1, 2}, {3, 4, 5})) = finite_set_size({1, 2}) * finite_set_size({3, 4, 5})

$is_finite_set(union({1, 2}, {2, 3}))
$is_finite_set(intersect({1, 2}, {2, 3}))
$is_finite_set(set_minus({1, 2}, {2, 3}))
$is_finite_set(set_diff({1, 2}, {2, 3}))

finite_set_size(intersect({1, 2}, {2, 3})) <= finite_set_size({1, 2})
finite_set_size(intersect({1, 2}, {2, 3})) <= finite_set_size({2, 3})
finite_set_size(set_minus({1, 2}, {2, 3})) <= finite_set_size({1, 2})
finite_set_size(union({1, 2}, {2, 3})) <= finite_set_size({1, 2}) + finite_set_size({2, 3})
finite_set_size(set_diff({1, 2}, {2, 3})) <= finite_set_size({1, 2}) + finite_set_size({2, 3})

finite_set_size(union({1, 2}, {2, 3})) = finite_set_size({1, 2}) + finite_set_size({2, 3}) - finite_set_size(intersect({1, 2}, {2, 3}))
finite_set_size(set_minus({1, 2}, {2, 3})) = finite_set_size({1, 2}) - finite_set_size(intersect({1, 2}, {2, 3}))
finite_set_size(set_diff({1, 2}, {2, 3})) = finite_set_size(set_minus({1, 2}, {2, 3})) + finite_set_size(set_minus({2, 3}, {1, 2}))

forall X finite_set:
    finite_set_size(X) >= 1
    =>:
        $is_nonempty_set(X)

claim:
    ? forall X, Y set:
        $is_finite_set(X)
        $is_finite_set(Y)
        =>:
            finite_set_size(cart(X, Y)) = finite_set_size(X) * finite_set_size(Y)
    finite_set_size(cart(X, Y)) = finite_set_size(X) * finite_set_size(Y)
```

### 13. Intervals

- Category: `obj`
- Purpose: Shows interval objects and interval membership.

```litex
## real interval sanity checks
have a '(0, 1)
a $in R
0 < a
a < 1

have b  '(0, 1]
0 < b
b <= 1

have c '[0, 1)
0 <= c
c < 1

have d '[0, 1]
0 <= d
d <= 1

have e '(,1)
e $in R
e < 1

have f '(,1]
f $in R
f <= 1

have g '(0,)
g $in R
0 < g

have h '[0,)
h $in R
0 <= h

forall x R:
    0 <= x
    =>:
        x $in '[0,)
```

```litex
sketch:
    $is_nonempty_set('[0, 0])
```

```litex
sketch:
    $is_nonempty_set('(0, 1))
```

```litex
sketch:
    $is_nonempty_set('(,1))
```

```litex
sketch:
    $is_nonempty_set('(,1])
```

```litex
sketch:
    $is_nonempty_set('(0,))
```

```litex
sketch:
    $is_nonempty_set('[0,))
```

### 14. Logarithms

- Category: `builtin rule`
- Purpose: Shows logarithm facts and monotonicity-style builtin support.

```litex
## Current builtin logarithm support.

log(2, 8) = 3
log(10, 100) = 2
log(3, 1) = 0
log(5, 5) = 1

forall a R_pos, b R:
    a != 1
    =>:
        log(a, a^b) = b

forall a, b R_pos:
    a != 1
    =>:
        a ^ log(a, b) = b
        log(a, a) = 1
        log(a, 1) = 0

forall a, b, c R_pos:
    a != 1
    a^b != 1
    =>:
        log(a^b, c) = log(a, c) / b

forall a, x, b R_pos:
    a != 1
    =>:
        log(a, x^b) = b * log(a, x)

forall a, x, y R_pos:
    a != 1
    =>:
        log(a, x * y) = log(a, x) + log(a, y)
        log(a, x / y) = log(a, x) - log(a, y)

forall a, b R_pos, c R:
    a != 1
    a^c = b
    =>:
        log(a, b) = c

## Useful evaluation-style examples that should stay easy.

log(2, 2^5) = 5
log(2, 32 / 4) = log(2, 32) - log(2, 4) = 5 - 2 = 3
log(2, 8 * 4) = log(2, 8) + log(2, 4) = 3 + 2 = 5
log(4, 64) = log(2^2, 64) = log(2, 64) / 2 = 6 / 2 = 3
log(3, 9^2) = 2 * log(3, 9) = 2 * 2 = 4

## Additional builtin logarithm rules.

forall a, x R_pos:
    a != 1
    =>:
        log(a, 1 / x) = -log(a, x)

forall a, b, c R_pos:
    a != 1
    b != 1
    c != 1
    log(c, a) != 0
    =>:
        log(a, b) = log(c, b) / log(c, a)

forall a, x, y R_pos:
    a > 1
    x < y
    =>:
        log(a, x) < log(a, y)

forall a, x, y R_pos:
    a < 1
    x < y
    =>:
        log(a, x) > log(a, y)

forall a, x R_pos:
    a > 1
    x > 1
    =>:
        log(a, x) > 0

forall a, x R_pos:
    a > 1
    x < 1
    =>:
        log(a, x) < 0

forall a, b R_pos, c R:
    a != 1
    =>:
        log(a, b) = c
    <=>:
        a^c = b
```

### 15. Modular Arithmetic

- Category: `builtin rule`
- Purpose: Shows modular arithmetic and congruence-style reasoning.

Mod: congruence under a common modulus (+, -, *) plus nested mod absorption (see builtin verify rules).

```litex
sketch:
    have X Z
    have Y Z
    have m Z_nz
    (X + Y) % m = ((X % m) + (Y % m)) % m
    (X - Y) % m = ((X % m) - (Y % m)) % m
    (X * Y) % m = ((X % m) * (Y % m)) % m
```

```litex
sketch:
    have b Z
    have c Z
    have d Z_nz
    (b * c) % d = ((b % d) * (c % d)) % d
```

```litex
sketch:
    have a Z
    have b Z
    have c Z
    have d Z_nz
    (a + b * c) % d = ((a % d) + ((b % d) * (c % d)) % d) % d

forall m Z:
    m != 0
    =>:
        0 % m = 0

forall x Z:
    x % 2 = 0 or x % 2 = 1

forall x Z:
    x % 1 = 0

forall a Z, b N_pos:
    0 <= a % b < b
    (a - a % b) % b = 0

forall a N, b N_pos:
    0 <= a % b < b
    (a - a % b) % b = 0
```

```litex
sketch:
    prop mod_eq(a Z, b Z, n Z):
        exist k Z st {a - b = n * k}

    claim:
        ? $mod_eq(11, 3, 4)
        witness exist k Z st {11 - 3 = 4 * k} from 2:
            11 - 3 = 4 * 2

    claim:
        ? $mod_eq(-5, 1, 3)
        witness exist k Z st {(-5) - 1 = 3 * k} from -2:
            (-5) - 1 = 3 * (-2)

    claim:
        ? forall a, b, c, d, n Z:
            $mod_eq(a, b, n)
            $mod_eq(c, d, n)
            =>:
                $mod_eq(a + c, b + d, n)
        obtain x from exist x Z st {a - b = n * x}
        obtain y from exist y Z st {c - d = n * y}
        witness exist k Z st {(a + c) - (b + d) = n * k} from x + y:
            (a + c) - (b + d) = (a - b) + (c - d) = n * x + n * y = n * (x + y)

    claim:
        ? forall a, b, c, d, n Z:
            $mod_eq(a, b, n)
            $mod_eq(c, d, n)
            =>:
                $mod_eq(a - c, b - d, n)
        obtain x from exist x Z st {a - b = n * x}
        obtain y from exist y Z st {c - d = n * y}
        witness exist k Z st {(a - c) - (b - d) = n * k} from x - y:
            (a - c) - (b - d) = (a - b) - (c - d) = n * x - n * y = n * (x - y)

    claim:
        ? forall a, b, n Z:
            $mod_eq(a, b, n)
            =>:
                $mod_eq(-a, -b, n)
        obtain x from exist x Z st {a - b = n * x}
        witness exist k Z st {(-a) - (-b) = n * k} from -x:
            (-a) - (-b) = -(a - b) = -(n * x) = n * (-x)

    claim:
        ? forall a, b, c, d, n Z:
            $mod_eq(a, b, n)
            $mod_eq(c, d, n)
            =>:
                $mod_eq(a * c, b * d, n)
        obtain x from exist x Z st {a - b = n * x}
        obtain y from exist y Z st {c - d = n * y}
        witness exist k Z st {a * c - b * d = n * k} from x * c + b * y:
            a * c - b * d = (a - b) * c + b * (c - d) = n * x * c + b * (n * y) = n * (x * c + b * y)

    claim:
        ? forall a, b, n Z:
            $mod_eq(a, b, n)
            =>:
                $mod_eq(a^2, b^2, n)
        obtain x from exist x Z st {a - b = n * x}
        witness exist k Z st {a^2 - b^2 = n * k} from x * (a + b):
            a^2 - b^2 = (a - b) * (a + b) = n * x * (a + b) = n * (x * (a + b))

    claim:
        ? forall a, b, n Z:
            $mod_eq(a, b, n)
            =>:
                $mod_eq(a^3, b^3, n)
        obtain x from exist x Z st {a - b = n * x}
        witness exist k Z st {a^3 - b^3 = n * k} from x * (a^2 + a * b + b^2):
            a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) = n * x * (a^2 + a * b + b^2) = n * (x * (a^2 + a * b + b^2))

    claim:
        ? forall a, n Z:
            $mod_eq(a, a, n)
        witness exist k Z st {a - a = n * k} from 0:
            a - a = n * 0

    claim:
        ? forall a, b Z:
            $mod_eq(a, 2, 4)
            =>:
                $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)
        obtain x from exist x Z st {a - 2 = 4 * x}
        witness exist k Z st {a * b^2 + a^2 * b + 3 * a - (2 * b^2 + 2^2 * b + 3 * 2) = 4 * k} from x * (b^2 + a * b + 2 * b + 3):
            a * b^2 + a^2 * b + 3 * a - (2 * b^2 + 2^2 * b + 3 * 2) = (a - 2) * (b^2 + a * b + 2 * b + 3) = 4 * x * (b^2 + a * b + 2 * b + 3) = 4 * (x * (b^2 + a * b + 2 * b + 3))

    claim:
        ? forall a, b Z:
            $mod_eq(a, 2, 4)
            =>:
                $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)
        $mod_eq(b^2, b^2, 4)
        $mod_eq(a * b^2, 2 * b^2, 4)
        $mod_eq(a^2, 2^2, 4)
        $mod_eq(b, b, 4)
        $mod_eq(a^2 * b, 2^2 * b, 4)
        $mod_eq(a * b^2 + a^2 * b, 2 * b^2 + 2^2 * b, 4)
        $mod_eq(3, 3, 4)
        $mod_eq(3 * a, 3 * 2, 4)
        $mod_eq(a * b^2 + a^2 * b + 3 * a, 2 * b^2 + 2^2 * b + 3 * 2, 4)
```

### 16. Powers

- Category: `builtin rule`
- Purpose: Shows exponent typing, identities, and inequalities.

```litex
0^0 = 1
8^(1/3) = 2

forall a R:
    a^0 = 1

forall a R, m, n N:
    a^(m+n) = a^m * a^n

forall a R, m, n N:
    (a^m)^n = a^(m * n)

forall a Z, m, n Z:
    m >= 1
    n >= 1
    =>:
        a^(m+n) = a^m * a^n

forall a Z:
    a^1 = a

forall a, b R, n N:
    (a * b)^n = a^n * b^n

forall a Z, n N:
    a^n $in Z

forall a N, n N:
    a^n $in N

forall a N_pos, n N:
    a^n $in N_pos

forall a R_pos, m R:
    a * a^m = a^(m + 1)
    a^m * a = a^(m + 1)

forall a R_nz, m Z:
    a * a^m = a^(m + 1)
    a^m * a = a^(m + 1)

forall x, y R, m N_pos:
    x >= 0
    y >= 0
    x <= y
    =>:
        x^m <= y^m

forall x, y R, m N_pos:
    x > y
    y >= 0
    =>:
        x^m > y^m

forall x R:
    x < 0
    =>:
        x^3 < 0

forall x R, m N_pos:
    x < 0
    m % 2 = 1
    =>:
        x^m < 0

forall x R, m N_pos:
    x <= 0
    m % 2 = 1
    =>:
        x^m <= 0

forall x, y R, m N_pos:
    x < y
    m % 2 = 1
    =>:
        x^m < y^m

forall x, y R, m N_pos:
    x >= 0
    y >= 0
    x^m <= y^m
    =>:
        x <= y

forall x, y R_pos, q R:
    q > 0
    x > y
    =>:
        x^q > y^q

forall x, y R_pos, q Q:
    q > 0
    x > y
    =>:
        x^q > y^q

forall x R_pos, q R:
    x^q > 0
    x^q != 0
    x^q * x^(-q) = x^(q + (-q))
    q + (-q) = 0
    x^(q + (-q)) = x^0
    x^0 = 1
    x^q * x^(-q) = 1
    x^(-q) = 1 / x^q

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

```

### 17. Special Number-Set Properties

- Category: `builtin rule`
- Purpose: Shows special builtin numeric facts.

```litex
## Order chains using <=, =, < (or >=, =, >) give transitive closure inside the same proof.
forall a, b, c, d R:
    a < b = c <= d
    =>:
        a < d
```

### 18. Standard Number Sets

- Category: `obj`
- Purpose: Shows membership and subset facts for N, Z, Q, and R.

```litex
have a, b R, c Z

a $in R
b $in R
c $in Z

1 $in N
1 $in N_pos
1 $in Z
1 $in Q
1 $in R

1 $in Q_pos
1 $in R_pos
-1 $in R_neg
-1.1 $in Q_neg
-1 $in Z_neg
1 $in Q_nz

1 + 1 $in N

-1 + 32.123 $in Q

2 - 9.5 + 10.5 $in Z

1 - 5 $in Z_neg
2 + 3 $in N_pos
4 - 1 $in N

-0.5 * 6 $in Q_neg
1 - 2.25 $in Q_neg
0 - 3 $in R_neg

-2 * 2.5 $in R_neg
7 - 3 $in Q_nz
10 - 10 + 1 $in Q_nz

3 - 1 $in Q_pos
1 + 0.5 $in Q_pos

forall a, b N:
    a + b $in N
    a * b $in N

forall a N_pos, b N:
    a + b $in N_pos
    b + a $in N_pos

forall a, b N_pos:
    a * b $in N_pos

forall a Q:
    a > 0
    =>:
        a $in Q_pos
        a / 2 $in Q_pos

forall a R:
    a > 0
    =>:
        a $in R_pos
```

### 19. Finite Sums And Products

- Category: `builtin rule`
- Purpose: Shows finite sums/products and induction with product facts.

```litex
sum(1, 3, fn(x Z) Z {x}) = sum(1, 3, fn(x Z) Z {x})
product(1, 3, fn(x Z) Z {x}) = product(1, 3, fn(x Z) Z {x})
sum(1, 3, fn(x Z) Z {x}) = sum(1, 3, fn(y Z) Z {y})
product(1, 3, fn(x Z) Z {x}) = product(1, 3, fn(y Z) Z {y})

eval sum(1, 3, fn(x Z) Z {x})
eval product(1, 3, fn(x Z) Z {x^2})
eval sum(1, 2, fn(x Z) Z {sum(2, 3, fn(y Z) Z {x + y})})


## Point-wise: sum f = sum g + sum h on the same range.
sum(1, 3, fn(x Z) Z {x + x}) = sum(1, 3, fn(x Z) Z {x}) + sum(1, 3, fn(x Z) Z {x})

## Point-wise order on the same range gives order between finite sums.
forall f, g fn(x Z) R:
    forall i Z:
        1 <= i <= 3
        =>:
            f(i) <= g(i)
    =>:
        sum(1, 3, fn(x Z) R {f(x)}) <= sum(1, 3, fn(x Z) R {g(x)})

## Finite-sum triangle inequality.
forall f fn(x Z) R:
    abs(sum(1, 3, fn(x Z) R {f(x)})) <= sum(1, 3, fn(x Z) R {abs(f(x))})

## Merge adjacent index ranges: sum(a..b) + sum((b+1)..c) = sum(a..c), same summand.
sum(1, 3, fn(x Z) Z {x + x}) + sum(4, 6, fn(x Z) Z {x + x}) = sum(1, 6, fn(x Z) Z {x + x})

## Constant summand: length * c when c does not use the index.
```

```litex
sketch:
    have c Z
    sum(1, 3, fn(x Z) Z {c}) = ((3 - 1) + 1) * c

## Finite-set sum: sum the function value over each element of a finite set.
finite_set_sum({1, 2, 3}, fn(x Z) Z {x}) = 1 + 2 + 3
finite_set_sum({}, fn(x Z) Z {x}) = 0
finite_set_sum(1...3, fn(x Z) Z {x}) = sum(1, 3, fn(x Z) Z {x})
finite_set_sum({1, 2}, fn(x Z) Z {x}) $in Z
finite_set_sum({1, 2}, fn(x N_pos) N_pos {x}) $in N_pos
```

```litex
sketch:
    have X finite_set
    have c Z
    finite_set_sum(X, fn(x X) Z {c}) = finite_set_size(X) * c
```

```litex
forall X power_set(Z):
    $is_finite_set(X)
    =>:
        finite_set_sum(X, fn(x X) Z {x + 0}) = finite_set_sum(X, fn(x X) Z {x})
```

```litex
thm finite_set_sum_substitution_example:
    ? forall X, Y finite_set, f fn(x X) R, g fn(y Y) X:
        forall x X:
            exist! y Y st {g(y) = x}
        =>:
            finite_set_sum(X, f) = finite_set_sum(Y, fn(y Y) R {f(g(y))})
    finite_set_sum(X, f) = finite_set_sum(Y, fn(y Y) R {f(g(y))})

thm finite_set_sum_range_bridge_example:
    ? forall a fn(i Z) R, m, n Z:
        m <= n
        =>:
            sum(m, n, fn(i Z) R {a(i)}) = finite_set_sum(m...n, fn(i m...n) R {a(i)})
    sum(m, n, fn(i Z) R {a(i)}) = finite_set_sum(m...n, fn(i m...n) R {a(i)})

thm finite_set_sum_disjoint_union_example:
    ? forall X, Y finite_set, f fn(z union(X, Y)) R:
        intersect(X, Y) = {}
        =>:
            finite_set_sum(union(X, Y), f) = finite_set_sum(X, fn(x X) R {f(x)}) + finite_set_sum(Y, fn(y Y) R {f(y)})
    finite_set_sum(union(X, Y), f) = finite_set_sum(X, fn(x X) R {f(x)}) + finite_set_sum(Y, fn(y Y) R {f(y)})

thm finite_set_sum_add_example:
    ? forall X finite_set, f, g fn(x X) R:
        finite_set_sum(X, fn(x X) R {f(x) + g(x)}) = finite_set_sum(X, f) + finite_set_sum(X, g)
    finite_set_sum(X, fn(x X) R {f(x) + g(x)}) = finite_set_sum(X, f) + finite_set_sum(X, g)

thm finite_set_sum_scalar_mul_example:
    ? forall X finite_set, f fn(x X) R, c R:
        finite_set_sum(X, fn(x X) R {c * f(x)}) = c * finite_set_sum(X, f)
    finite_set_sum(X, fn(x X) R {c * f(x)}) = c * finite_set_sum(X, f)

thm finite_set_sum_monotone_example:
    ? forall X finite_set, f, g fn(x X) R:
        forall x X:
            f(x) <= g(x)
        =>:
            finite_set_sum(X, f) <= finite_set_sum(X, g)
    finite_set_sum(X, f) <= finite_set_sum(X, g)

thm finite_set_sum_triangle_example:
    ? forall X finite_set, f fn(x X) R:
        abs(finite_set_sum(X, f)) <= finite_set_sum(X, fn(x X) R {abs(f(x))})
    abs(finite_set_sum(X, f)) <= finite_set_sum(X, fn(x X) R {abs(f(x))})

thm finite_double_sum_over_cartesian_product_example:
    ? forall X, Y finite_set, f fn(z cart(X, Y)) R:
        finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(cart(X, Y), f)
    finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(cart(X, Y), f)

thm finite_fubini_example:
    ? forall X, Y finite_set, f fn(z cart(X, Y)) R:
        finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(Y, fn(y Y) R {finite_set_sum(X, fn(x X) R {f((x, y))})})
    finite_set_sum(X, fn(x X) R {finite_set_sum(Y, fn(y Y) R {f((x, y))})}) = finite_set_sum(Y, fn(y Y) R {finite_set_sum(X, fn(x X) R {f((x, y))})})

## A finite-set sum defined by a bijective enumeration is independent of the enumeration.
prop is_bijection_from_index_range_to_finite_set(X finite_set, g fn(i closed_range(1, finite_set_size(X))) X):
    forall x X:
        exist! i closed_range(1, finite_set_size(X)) st {g(i) = x}

template<X finite_set, f fn(x X) R, g fn(i closed_range(1, finite_set_size(X))) X: finite_set_size(X) >= 1, $is_bijection_from_index_range_to_finite_set(X, g)>:
    have self_finite_set_sum R = sum(1, finite_set_size(X), fn(i closed_range(1, finite_set_size(X))) R {f(g(i))})

thm finite_set_sum_enumeration_well_defined:
    ? forall X finite_set, f fn(x X) R, g fn(i closed_range(1, finite_set_size(X))) X, h fn(i closed_range(1, finite_set_size(X))) X:
        finite_set_size(X) >= 1
        $is_bijection_from_index_range_to_finite_set(X, g)
        $is_bijection_from_index_range_to_finite_set(X, h)
        =>:
            \self_finite_set_sum<X, f, g> = \self_finite_set_sum<X, f, h>
    \self_finite_set_sum<X, f, g> = \self_finite_set_sum<X, f, h>

## Finite-set product: multiply the function value over each element of a finite set.
finite_set_product({2, 3, 4}, fn(x Z) Z {x}) = 2 * 3 * 4
finite_set_product({}, fn(x Z) Z {x}) = 1
finite_set_product(1...3, fn(x Z) Z {x}) = product(1, 3, fn(x Z) Z {x})
finite_set_product({1, 2}, fn(x Z) Z {x}) $in Z
finite_set_product({1, 2}, fn(x N_pos) N_pos {x}) $in N_pos
finite_set_product({}, fn(x N_pos) N_pos {x}) $in N_pos
```

```litex
sketch:
    have X finite_set
    have c R
    finite_set_product(X, fn(x X) R {c}) = c ^ finite_set_size(X)
```

```litex
forall X power_set(Z):
    $is_finite_set(X)
    =>:
        finite_set_product(X, fn(x X) Z {x + 0}) = finite_set_product(X, fn(x X) Z {x})

## Reindex: same summand, parallel shift of both bounds, pointwise on the (rhs) range.
sum(1, 3, fn(x Z) Z {x}) = sum(2, 4, fn(x Z) Z {x - 1})

## Last index: sum(s..e,f) = sum(s..e-1,f) + f(e) (same unary f); product analogue with *.
sum(1, 3, fn(x Z) Z {x}) = sum(1, 2, fn(x Z) Z {x}) + fn(x Z) Z {x}(3)
product(1, 3, fn(x Z) Z {x}) = product(1, 2, fn(x Z) Z {x}) * fn(x Z) Z {x}(3)

## Partition: sum(a..d,f) as edge-to-edge sub-sums (same f); product analogue with *.
sum(1, 10, fn(x Z) Z {x}) = sum(1, 3, fn(x Z) Z {x}) + sum(4, 8, fn(x Z) Z {x}) + sum(9, 10, fn(x Z) Z {x})
```

```litex
sketch:
    sum(1, 3, fn(x Z) Z {x}) = sum(1, 2, fn(x Z) Z {x}) + fn(x Z) Z {x}(3)
    product(1, 3, fn(x Z) Z {x}) = product(1, 2, fn(x Z) Z {x}) * fn(x Z) Z {x}(3)

    sum(1, 10, fn(x Z) Z {x}) = sum(1, 3, fn(x Z) Z {x}) + sum(4, 8, fn(x Z) Z {x}) + sum(9, 10, fn(x Z) Z {x})

```

```litex
sketch:
    by induc a from 1:
        ? product(1, a, fn(x N_pos) N_pos {x}) % a = 0 and a <= product(1, a, fn(x N_pos) N_pos {x})

        product(1, 1, fn(x N_pos) N_pos {x}) = 1
        1 <= product(1, 1, fn(x N_pos) N_pos {x})

        claim:
            ? forall k Z:
                k >= 1
                product(1, k, fn(x N_pos) N_pos {x}) % k = 0 and k <= product(1, k, fn(x N_pos) N_pos {x})
                =>:
                    product(1, k + 1, fn(x N_pos) N_pos {x}) % (k + 1) = 0 and k + 1 <= product(1, k + 1, fn(x N_pos) N_pos {x})

            product(1, k + 1, fn(x N_pos) N_pos {x}) = product(1, k, fn(x N_pos) N_pos {x}) * (k + 1)
            witness exist t Z st {product(1, k + 1, fn(x N_pos) N_pos {x}) = t * (k + 1)} from product(1, k, fn(x N_pos) N_pos {x})
            product(1, k + 1, fn(x N_pos) N_pos {x}) % (k + 1) = 0
            k + 1 <= product(1, k + 1, fn(x N_pos) N_pos {x})
```

---

## Objects And Statements

This is a reference page for Litex object syntax and statement behavior. It is
best after [00_start_here.md](#start-here), when you want to look up how a
particular expression or statement form behaves.

The object entries say what the notation means mathematically.  The statement
entries mirror `docs/cheatsheet.md`: first the well-definedness or structural
checks, then the proof obligation, then the environment effect.

Each `litex` block is intended to run on its own.

### Object Examples

#### 1. Numeric Objects And Arithmetic

Mathematical meaning: numeric literals denote numbers in the usual built-in
number systems, and arithmetic expressions denote the corresponding numeric
objects.  Litex uses exact arithmetic for integer and rational calculations.

```litex
1 + 2 = 3
3 - 1 = 2
2 * 3 = 6
6 / 2 = 3
5 % 2 = 1
2^3 = 8
-1 + 2 = 1
```

#### 2. Standard Number Sets

Mathematical meaning: `N`, `Z`, `Q`, and `R` are the built-in natural, integer,
rational, and real number sets.  Suffixes such as `_pos`, `_neg`, and `_nz`
name common subsets like positive or nonzero numbers.

```litex
0 $in N
0 $in Z
0 $in Q
0 $in R
1 $in N_pos
1 $in R_pos
-1 $in Z_neg
1 $in Z_nz
1 / 6 $in Q
6 / 3 $in Z
not 1 / 6 $in Z
not 0 $in Q_nz
```

#### 3. Finite Sets And Set Builders

Mathematical meaning: `{1, 2, 3}` is a displayed finite set, while
`{x R: x > 0}` is the subset of `R` cut out by the predicate `x > 0`.  A set
builder is best read as ordinary set-comprehension notation.

```litex
1 $in {1, 2, 3}
$is_finite_set({1, 2})
1 $in {x R: x > 0}

have positive_reals set = {x R: x > 0}
1 $in positive_reals
```

#### 4. Set Operations

Mathematical meaning: `union`, `intersect`, and `set_minus` are the ordinary
binary union, intersection, and relative complement of sets.  `set_diff` is the
symmetric-difference style object used by the current library.

```litex
2 $in union({1, 2}, {2, 3})
2 $in intersect({1, 2}, {2, 3})
2 $in set_minus({1, 2}, {1})
$is_finite_set(set_diff({1, 2}, {2, 3}))
{1, 2} $in power_set({1, 2, 3})
```

#### 5. Ranges

Mathematical meaning: `range(a, b)` is the integer-style half-open range from
`a` up to but not including `b`; `closed_range(a, b)` and `a...b` are closed
ranges.  These objects are useful when finite enumeration or indexed data is
intended.

```litex
2 $in range(0, 3)
3 $in closed_range(0, 3)
2 $in 0...3
```

#### 6. Tuples And Cartesian Products

Mathematical meaning: `(a, b)` is an ordered tuple, and `cart(A, B)` is the
Cartesian product of the factor sets.  Tuple projection uses one-based indexing
with square brackets.

```litex
(1, 2)[1] = 1
(1, 2)[2] = 2
(1, 2) $in cart(R, R)
cart_dim(cart(R, Q)) = 2
proj(cart(R, Q), 1) = R
```

#### 7. Functions And Anonymous Functions

Mathematical meaning: `fn(x R) R` is the set of functions from `R` to `R`, and
`have fn f(x R) R = ...` names one such function.  Anonymous functions such as
`fn(x R) R {x + 1}` are function values written directly at the point of use.

```litex
have fn shift(x R) R = x + 1

shift $in fn(x R) R
shift(2) = 3
fn(x R) R {x + 1}(2) = 3
$fn_eq(fn(x R) R {x}, fn(y R) R {y})
```

#### 8. Function Images

Mathematical meaning: `fn_range(f)` is the image of a function over its whole
domain.  `fn_range_on(f, S)` is the image of a unary function whose declared
domain is exactly `S`.

```litex
have fn shift(x R) R = x + 1

shift(2) $in fn_range(shift)
fn_range(shift) $subset R

have by preimage x from shift(2) $in fn_range(shift)
x $in R
shift(2) = shift(x)
```

```litex
have a finite_seq(R, 3) = [1, 2, 3]

fn(x 1...3) R {a(x)}(2) $in fn_range_on(fn(x 1...3) R {a(x)}, 1...3)
fn_range_on(fn(x 1...3) R {a(x)}, 1...3) $subset R
$is_finite_set(fn_range_on(fn(x 1...3) R {a(x)}, 1...3))

have by preimage k from fn(x 1...3) R {a(x)}(2) $in fn_range_on(fn(x 1...3) R {a(x)}, 1...3)
k $in 1...3
fn(x 1...3) R {a(x)}(2) = fn(x 1...3) R {a(x)}(k)
```

#### 9. Sequences, Finite Sequences, And Matrices

Mathematical meaning: `seq(R)` is the set of positive-integer-indexed real
sequences, `finite_seq(R, n)` is a length-`n` sequence, and `matrix(R, r, c)` is
an `r` by `c` rectangular array.  All three are function-like objects with
index application syntax.

```litex
have a finite_seq(R, 3) = [1, 2, 3]

a $in fn(x N_pos: x <= 3) R
a(1) = 1
a(2) = 2
a(3) = 3
finite_seq(R, 3) = fn(x N_pos: x <= 3) R
```

```litex
have s seq(R)
s(1) $in R

have M matrix(R, 2, 2) = [[1, 2], [3, 4]]
M(1, 1) = 1
M(2, 1) = 3
```

#### 10. Struct Objects

Mathematical meaning: a `struct` names a record-shaped subset of tuples, with
typed fields and optional defining conditions.  A value of `&Point` can be read
either by tuple index or by field projection through `&Point{...}.field`.

```litex
struct Point:
    x R
    y R

(1, 2) $in &Point
have p &Point = (1, 2)
&Point{p}.x = p[1]
&Point{p}.x = 1
&Point{(1, 2)}.y = 2
```

### Statement Examples

#### 1. Ordinary Fact Statement

Purpose: assert a mathematical fact and make it available later.

- Well-definedness / structural checks: the fact and every object inside it
  must be well-defined.
- Truth verification: Litex proves the fact from builtin rules, known facts,
  theorem instances, and local context.
- Environment effects: stores the proved fact and any inferred consequences.

```litex
1 + 1 = 2

forall x R:
    x = x
```

#### 2. Explicit Assumptions Without Proof

Purpose: introduce an assumption without proof, usually for explicit proof debt
or a background interface.

- Well-definedness / structural checks: rejected in strict mode; every assumed
  fact must be well-defined.
- Truth verification: none.
- Environment effects: stores the unsafe assumption and runs inference.

```litex
abstract_prop p(x)
trust $p(0)
$p(0)
```

#### 3. Trusted Local Names With `trust have`

Purpose: introduce local names together with assumed facts about them.

- Well-definedness / structural checks: rejected in strict mode; parameter
  declarations are checked, and attached facts must be well-defined.
- Truth verification: none for the attached facts.
- Environment effects: stores the names, their type facts, the attached facts,
  and inferred consequences.

```litex
trust have a R:
    a = 1

a $in R
a = 1
```

#### 4. Typed `have`

Purpose: introduce an arbitrary object of a nonempty type or set.

- Well-definedness / structural checks: the name must be unused and the type
  object must be well-defined.
- Truth verification: Litex verifies the type or set is nonempty.
- Environment effects: stores the new name, its membership fact, and inferred
  facts.

```litex
have x R
x $in R
```

#### 5. Definitional `have`

Purpose: introduce a name for a specific object.

- Well-definedness / structural checks: the name, declared type, and assigned
  object must be well-defined.
- Truth verification: Litex verifies the assigned object belongs to the
  declared type.
- Environment effects: stores the name, its type fact, the defining equality,
  and any value caches for sequence-like objects.

```litex
have a R = 1
a $in R
a = 1
```

#### 6. Opening An Existential With `obtain`

Purpose: name witnesses from an already known existential fact.

- Well-definedness / structural checks: the existential shape and requested
  witness count must match.
- Truth verification: verifies the source existential fact.
- Environment effects: stores witness names, witness type facts, body facts,
  and inferred consequences.

```litex
witness exist x R st {x = 1} from 1:
    1 = 1

obtain a from exist x R st {x = 1}
a $in R
a = 1
```

#### 7. Naming A Preimage

Purpose: name a preimage witness from a function-image membership fact.

- Well-definedness / structural checks: the source must be a supported range,
  replacement, or restricted-range membership fact, and the witness count must
  match.
- Truth verification: verifies the source membership fact.
- Environment effects: stores preimage names, domain facts, side conditions,
  and the equality connecting the value to the function application.

```litex
have fn shift(x R) R = x + 1

shift(2) $in fn_range(shift)
have by preimage x from shift(2) $in fn_range(shift)
x $in R
shift(2) = shift(x)
```

#### 8. Function Definition

Purpose: define a function by a single expression over its domain.

- Well-definedness / structural checks: checks the function set, parameter
  declarations, body, return set, and function name.
- Truth verification: verifies the body value belongs to the return set for
  every allowed input.
- Environment effects: stores the function name, function type, body data,
  equality to the anonymous function, and inferred facts.

```litex
have fn f(x R) R = x + 1
f $in fn(x R) R
f(2) = 3
```

#### 9. Case Function Definition

Purpose: define a function by cases on its input domain.

- Well-definedness / structural checks: checks the function set, cases,
  returned expressions, and function name.
- Truth verification: verifies each case returns a value in the return set and
  that the cases cover the domain.
- Environment effects: stores the function name, function type, and generated
  case facts.

```litex
have fn is_zero_indicator(x R) R by cases:
    case x = 0: 1
    case x != 0: 0

is_zero_indicator(0) = 1
```

#### 10. Recursive Function Definition

Purpose: define a function by induction over a decreasing integer-valued
measure.

- Well-definedness / structural checks: checks the function signature,
  induction measure, base and step cases, and recursive calls.
- Truth verification: verifies base and step obligations.
- Environment effects: stores the recursive function definition facts.

```litex
have fn count_from_zero(n Z: n >= 0) R by induc n from 0:
    case n = 0: 0
    case n > 0: count_from_zero(n - 1) + 1

count_from_zero(0) = 0
```

#### 11. Algorithm Definition And Evaluation

Purpose: attach an executable algorithm to a function so Litex can evaluate
calls.

- Well-definedness / structural checks: the target function must already exist
  and the algorithm parameters must match the function set.
- Truth verification: verifies each return expression is valid; if no default
  return exists, verifies case coverage.
- Environment effects: stores the algorithm definition for later `eval`.

```litex
have fn f(x R) R = x + 1

algo f(x):
    x + 1

eval f(2)
f(2) = 3
```

```litex
have fn as algo id_real(x R) R = x

eval id_real(3)
id_real(3) = 3
```

#### 12. Function From Unique Existence

Purpose: define a function when every input has a unique output satisfying a
property.

- Well-definedness / structural checks: the source `forall` must have the
  expected unique-existence shape.
- Truth verification: verifies the source `forall` or the proof block that
  establishes it.
- Environment effects: stores the function name, function type, property
  `forall`, and uniqueness fact.

```litex
have A set = R
have B set = R

have fn f by exist!:
    ? forall x A:
        exist! y B st {y = x}
    witness exist! y B st {y = x} from x:
        claim:
            ? forall y1, y2 B:
                y1 = x
                y2 = x
                =>:
                    y1 = y2
            y1 = x
            x = y2
            y1 = y2

forall x A:
    f(x) = x
```

#### 13. Symbolic Tuple, Cart, And Matrix Definitions

Purpose: define structured objects by coordinate or projection rules.

- Well-definedness / structural checks: the name must be unused, dimensions
  and coordinate expressions must be well-defined, and the left side must
  describe the object being defined.
- Truth verification: verifies the dimensions are positive and at least two
  when needed, and verifies entry values belong to the declared sets.
- Environment effects: stores tuple/cart/matrix markers, dimension facts, and
  coordinate or projection facts.

```litex
have n N_pos = 3
2 <= n

have tuple t for i <= n, t[i] = i
t[1] = 1

have cart R3 for i <= n, proj(R3, i) = R
R3 = cart(R, R, R)
```

```litex
have r N_pos = 2
have c N_pos = 2

have matrix M matrix(N_pos, r, c) for i <= r, j <= c, M(i, j) = j
M $in matrix(N_pos, r, c)
M(1, 2) = 2
```

#### 14. Defining Concrete And Abstract Predicates

Purpose: introduce named predicates for reusable mathematical properties.

- Well-definedness / structural checks: parameter declarations and definition
  facts must be well-defined; names must not conflict.
- Truth verification: `prop` definitions do not prove their body facts, and
  `abstract_prop` has no body to prove.
- Environment effects: stores the concrete or abstract predicate definition.

```litex
prop is_one(x R):
    x = 1

$is_one(1)

abstract_prop related(x, y)
trust $related(1, 1)
$related(1, 1)
```

#### 15. Record-Like Objects With `struct`

Purpose: define a record-like structure with typed fields and optional
equivalent facts.

- Well-definedness / structural checks: parameter domains, field types, and
  equivalent facts must be well-defined; the struct name must be unused.
- Truth verification: does not prove the equivalent facts at declaration time.
- Environment effects: stores the struct definition and enables membership and
  field-view facts.

```litex
struct Point:
    x R
    y R

have p &Point = (1, 2)
&Point{p}.x = 1
&Point{p}.y = 2
```

#### 16. Parameterized Families With `template`

Purpose: define a parameterized object or function family.

- Well-definedness / structural checks: template parameters and domains must
  be well-defined, and the body must execute in a local environment.
- Truth verification: the body is verified like ordinary Litex code.
- Environment effects: stores the template definition for later instantiation.

```litex
template<S set>:
    have carrier_alias set = S

\carrier_alias<R> = R

template<S set, z S>:
    have fn const_on_S(x S) S = z

\const_on_S<R, 0> $in fn(x R) R
```

#### 17. Named Theorems With `thm` And `by thm`

Purpose: store a reusable theorem and instantiate it later.

- Well-definedness / structural checks: the theorem statement must be
  well-defined; theorem names must be unique; theorem-call arguments must
  satisfy parameter types.
- Truth verification: the theorem proof verifies the target, and `by thm`
  verifies instantiated domain facts.
- Environment effects: stores the theorem definition, stores the theorem fact,
  and later stores instantiated conclusions.

```litex
thm add_zero_right:
    ? forall x R:
        x + 0 = x
    x + 0 = x

by thm add_zero_right(2)
2 + 0 = 2
```

#### 18. Local Proof Blocks With `claim`

Purpose: prove a local target and store it in the current environment.

- Well-definedness / structural checks: the claimed fact must be well-defined.
- Truth verification: the proof block must verify the claimed target or
  then-clauses.
- Environment effects: stores the claimed fact and runs inference.

```litex
claim:
    ? 1 + 1 = 2
    1 + 1 = 2
```

#### 19. Giving Witnesses

Purpose: prove an existential statement by giving explicit witnesses.

- Well-definedness / structural checks: witness count and witness types must
  match the existential target.
- Truth verification: verifies the existential body under the proposed
  witnesses.
- Environment effects: stores the existential fact and inferred consequences.

```litex
witness exist x, y R st {x > y} from 1, 0:
    1 > 0

exist a, b R st {a > b}
```

#### 20. Exploratory Blocks With `sketch` And `try`

Purpose: run checked exploratory code without committing it, or run a checked
batch that commits only if every nested statement succeeds.

- Well-definedness / structural checks: each nested statement performs its own
  checks; `try` rejects control statements such as `clear`, `import`, and
  `local import`.
- Truth verification: nested statements verify normally.
- Environment effects: `sketch` has no outer effect; `try` commits the child
  environment into the parent environment on success.

```litex
sketch:
    have local_value R = 1
    local_value = 1

try:
    have committed_value R = 2
    committed_value = 2

committed_value = 2
```

#### 21. Proof-By Statements

Purpose: tell Litex which proof shape to use for a local target.

- Well-definedness / structural checks: the proof statement checks the target,
  the shape-specific parameters, and any nested statements.
- Truth verification: verifies the shape-specific proof obligations, such as
  case coverage, contradiction, or both directions of extension.
- Environment effects: stores the target fact or generated `forall` fact.

```litex
by cases:
    ? 1 + 1 = 2
    case 1 + 1 = 2:
        do_nothing
    case 1 + 1 != 2:
        impossible 1 + 1 = 2
```

```litex
by contra:
    ? not exist x R st {x != x}
    obtain a from exist x R st {x != x}
    impossible a = a
```

```litex
by enumerate finite_set:
    ? forall x {1, 2}:
        x = 1 or x = 2
```

```litex
by extension:
    ? {1, 2} = {2, 1}
    by enumerate finite_set:
        ? forall x {1, 2}:
            x $in {2, 1}
    by enumerate finite_set:
        ? forall y {2, 1}:
            y $in {1, 2}

{1, 2} = {2, 1}
```

#### 22. Evaluating Algorithms With `eval`

Purpose: compute an evaluable object and store the resulting equality.

- Well-definedness / structural checks: the object must be evaluable.
- Truth verification: no separate proof of the original expression is needed;
  evaluation supplies the equality.
- Environment effects: stores the expression-value equality with an evaluation
  reason.

```litex
eval 1 + 2
1 + 2 = 3
```

#### 23. Readable Abbreviations With `macro`

Purpose: define a textual abbreviation used before parsing the expanded Litex
code.

- Well-definedness / structural checks: the macro name and replacement text
  must be parseable in later expanded positions.
- Truth verification: none for the macro definition itself.
- Environment effects: stores the macro expansion rule for following
  statements in the same file.

```litex
macro REAL "R"
macro HAVE_FN "have fn"

@HAVE_FN id_real(x @REAL) @REAL = x
id_real(1) = 1
```

#### 24. Empty Proof Steps

Purpose: make an explicit empty proof step.

- Well-definedness / structural checks: none.
- Truth verification: none.
- Environment effects: none.

```litex
do_nothing
```

#### 25. Module Commands

Purpose: load modules, bind sources declared in `litex.config`,
or clear the current environment. These examples are syntax only because they
depend on local project files.

- Well-definedness / structural checks: `litex.config` declarations and
  `local import` bindings are validated during discovery; `import` resolves a
  module; `clear` has no structural checks. `trust import` and
  `trust local import` use the same declared targets and validation.
- Truth verification: imported modules and declared files verify normally when
  loaded. A trusted import deliberately skips this phase for its target and
  transitive imports, and is rejected by strict mode.
- Environment effects: module commands update the module manager; `clear`
  removes the current user environment. Imported modules and project export
  nodes remain registered.

<!-- litex:skip-test -->
```litex
import Algebra
clear
```

`clear` only resets the current environment; it does not change the module
manager.

<!-- litex:skip-test -->
```litex
import Algebra

clear

# Algebra remains active after clear
```

---

## Small Worlds

This page bridges the syntax reference and the longer case studies. Each block
defines a tiny mathematical world: a few objects, the vocabulary that talks
about them, and one or two checked consequences.

### 1. Points And A Predicate

A `struct` names a record-shaped object. A `prop` can then talk about values of
that structure.

```litex
struct Point:
    x R
    y R

prop lies_on_x_axis(p &Point):
    &Point{p}.y = 0

have origin &Point = (0, 0)

&Point{origin}.x = 0
&Point{origin}.y = 0
$lies_on_x_axis(origin)
```

### 2. A Small Algebraic Interface

This is not a full group theory development. It shows the shape of a small
interface: a property, a structure carrying the data, and one concrete checked
instance.

```litex
prop HasAdditiveIdentity(s nonempty_set, op fn(x, y s) s, e s):
    forall x s:
        op(e, x) = x
        op(x, e) = x

struct PointedOperation<s nonempty_set>:
    op fn(x, y s) s
    e s
    <=>:
        $HasAdditiveIdentity(s, op, e)

$HasAdditiveIdentity(Z, fn(x, y Z) Z {x + y}, 0)

(fn(x, y Z) Z {x + y}, 0) $in &PointedOperation<Z>
```

### 3. A Template Family

Use `template` when the parameter belongs to the definition itself. Here the
same body defines a constant function on any chosen set and chosen value.

```litex
template<S set, z S>:
    have fn const_on_S(x S) S = z

\const_on_S<R, 0> $in fn(x R) R
```

The longer files build from the same ingredients: introduce objects, name the
vocabulary, state the intended facts, and let the verifier check each local
move.

---

## Case Studies

Larger proof developments and mathematical case studies that combine several
Litex features.

These examples are deliberately larger than the tutorial path. Some studies are
complete local proof developments; others are assumption-heavy sketches that
use `abstract_prop` to focus on the shape of the interface. Read the category
and purpose lines before treating a block as a finished theorem-library proof.

### 1. A Tiny Axiomatic Geometry Setup

- Category: `case study`
- Purpose: Shows an axiomatic geometry development using abstract props.

```litex
have Point nonempty_set, Line nonempty_set
abstract_prop lies_on(P, L)

forall P Point, L Line:
    $lies_on(P, L)
    =>:
        $lies_on(P, L)
```

### 2. The Real Numbers Are Infinite

- Category: `case study`
- Purpose: Shows an infinity argument for R.

```litex
by contra not $is_finite_set(R):
    forall x 0...finite_set_size(R):
        x $in Z
        x $in R

    0...finite_set_size(R) $subset R

    finite_set_size(R) + 1 = finite_set_size(R) - 0 + 1 = finite_set_size(0...finite_set_size(R)) <= finite_set_size(R)

    impossible finite_set_size(R) + 1 <= finite_set_size(R)
```

### 3. A High-Level Cantor-Schroeder-Bernstein Sketch

- Category: `case study`
- Purpose: Shows a high-level CSB construction with abstract partition facts.

```litex
abstract_prop has_injections_both_ways(A, B)
abstract_prop same_size(A, B)

forall A, B set:
    forall S, T set:
        $has_injections_both_ways(S, T)
        =>:
            $same_size(S, T)
    $has_injections_both_ways(A, B)
    =>:
        $same_size(A, B)
```

### 4. Euclid's Theorem On Arbitrarily Large Primes

- Category: `case study`
- Purpose: Detailed Euclid-style proof that there are arbitrarily large primes.

```litex
prop prime(a N_pos):
    2 <= a
    forall b N_pos:
        2 <= b < a
        =>:
            a % b != 0

claim:
    ? forall a N_pos:
        product(1, a, fn(x N_pos) N_pos {x}) % a = 0 and a <= product(1, a, fn(x N_pos) N_pos {x})

    by induc a from 1:
        ? product(1, a, fn(x N_pos) N_pos {x}) % a = 0 and a <= product(1, a, fn(x N_pos) N_pos {x})

        product(1, 1, fn(x N_pos) N_pos {x}) = 1
        1 <= product(1, 1, fn(x N_pos) N_pos {x})

        claim:
            ? forall k Z:
                k >= 1
                product(1, k, fn(x N_pos) N_pos {x}) % k = 0 and k <= product(1, k, fn(x N_pos) N_pos {x})
                =>:
                    product(1, k + 1, fn(x N_pos) N_pos {x}) % (k + 1) = 0 and k + 1 <= product(1, k + 1, fn(x N_pos) N_pos {x})

            product(1, k + 1, fn(x N_pos) N_pos {x}) = product(1, k, fn(x N_pos) N_pos {x}) * (k + 1)
            witness exist t Z st {product(1, k + 1, fn(x N_pos) N_pos {x}) = t * (k + 1)} from product(1, k, fn(x N_pos) N_pos {x})
            product(1, k + 1, fn(x N_pos) N_pos {x}) % (k + 1) = 0
            k + 1 <= product(1, k + 1, fn(x N_pos) N_pos {x})

claim:
    ? forall a, k N_pos:
        k <= a
        =>:
            product(1, a, fn(x N_pos) N_pos {x}) % k = 0

    by cases:
        ? product(1, a, fn(x N_pos) N_pos {x}) % k = 0
        case k = a:
            product(1, a, fn(x N_pos) N_pos {x}) % a = 0
            product(1, a, fn(x N_pos) N_pos {x}) % k = product(1, a, fn(x N_pos) N_pos {x}) % a = 0
        case k < a:
            product(1, a, fn(x N_pos) N_pos {x}) = product(1, k, fn(x N_pos) N_pos {x}) * product(k + 1, a, fn(x N_pos) N_pos {x})
            product(1, k, fn(x N_pos) N_pos {x}) % k = 0
            obtain r from exist r Z st {product(1, k, fn(x N_pos) N_pos {x}) = r * k}
            witness exist t Z st {product(1, a, fn(x N_pos) N_pos {x}) = t * k} from r * product(k + 1, a, fn(x N_pos) N_pos {x}):
                product(1, a, fn(x N_pos) N_pos {x}) = product(1, k, fn(x N_pos) N_pos {x}) * product(k + 1, a, fn(x N_pos) N_pos {x}) = (r * k) * product(k + 1, a, fn(x N_pos) N_pos {x}) = (r * product(k + 1, a, fn(x N_pos) N_pos {x})) * k
            product(1, a, fn(x N_pos) N_pos {x}) % k = 0

claim:
    ? forall a N_pos:
        a <= product(1, a, fn(x N_pos) N_pos {x})

    product(1, a, fn(x N_pos) N_pos {x}) % a = 0 and a <= product(1, a, fn(x N_pos) N_pos {x})

claim:
    ? forall a N_pos:
        2 <= a
        =>:
            exist k N_pos st {$prime(k), a % k = 0}

    by strong_induc x from 2:
        ? exist k N_pos st {$prime(k), x % k = 0}

        claim:
            ? forall b N_pos:
                2 <= b < 2
                =>:
                    2 % b != 0
            by contra 2 % b != 0:
                impossible b < 2
        $prime(2)

        witness exist t Z st {2 = t * 2} from 1
        2 % 2 = 0
        witness exist k N_pos st {$prime(k), 2 % k = 0} from 2

        claim:
            ? forall n Z:
                n >= 2
                forall m Z:
                    2 <= m
                    m <= n
                    =>:
                        exist k N_pos st {$prime(k), m % k = 0}
                =>:
                    exist k N_pos st {$prime(k), (n + 1) % k = 0}

            by cases exist k N_pos st {$prime(k), (n + 1) % k = 0}:
                case $prime(n+1):
                    witness exist t Z st {n + 1 = t * (n + 1)} from 1
                    (n + 1) % (n + 1) = 0
                    witness exist k N_pos st {$prime(k), (n + 1) % k = 0} from n+1
                case not $prime(n+1):
                    by contra:
                        ? not forall b N_pos:
                            2 <= b < n + 1
                            =>:
                                (n + 1) % b != 0
                        2 <= n + 1
                        $prime(n+1)
                        impossible $prime(n+1)

                    obtain c from exist b N_pos st {2 <= b < n+1, not (n + 1) % b != 0}

                    2 <= c < n+1

                    (n+1) % c = 0
                    c <= n or c >= n + 1
                    by cases:
                        ? c <= n
                        case c <= n:
                            ...
                        case c >= n + 1:
                            impossible c < n + 1

                    obtain d from exist k N_pos st {$prime(k), c % k = 0}

                    obtain e from exist k Z st {(n+1) = k * c}

                    obtain f from exist k Z st {c = k * d}

                    witness exist t Z st {e * f * d = t * d} from e * f
                    (e * f * d) % d = 0

                    witness exist k N_pos st {$prime(k), (n + 1) % k = 0} from d:
                        n + 1 = e * c = e * (f * d) = (e * f) * d
                        (n + 1) % d = ((e * f) * d) % d = 0

claim forall! a N_pos: 2 <= a => {exist k N_pos st {k > a, $prime(k)}}:
    2 <= a <= product(1, a, fn(x N_pos) N_pos {x}) <= product(1, a, fn(x N_pos) N_pos {x}) + 1
    obtain k from exist k N_pos st {$prime(k), (product(1, a, fn(x N_pos) N_pos {x}) + 1) % k = 0}
    by cases k > a:
        case k <= a:
            product(1, a, fn(x N_pos) N_pos {x}) % k = 0
            (product(1, a, fn(x N_pos) N_pos {x}) + 1) % k = (product(1, a, fn(x N_pos) N_pos {x}) % k + 1 % k) % k = (0 + 1) % k = 1
            impossible (product(1, a, fn(x N_pos) N_pos {x}) + 1) % k = 0
        case k > a:
            do_nothing
    witness exist k N_pos st {k > a, $prime(k)} from k
```

### 5. The Euclidean Algorithm And Bezout Coefficients

- Category: `case study`
- Purpose: Large checked development of division, gcd, and extended gcd.

```litex
claim:
    ? forall x, y R:
        0 <= x
        0 <= y
        x^2 < y^2
        =>:
            x < y

    by contra:
        ? x < y
        y <= x
        y^2 <= x^2
        impossible x^2 < y^2

claim:
    ? forall n, d Z:
        n * d < 0
        =>:
            abs(2 * (n + d) - d)^2 < abs(2 * n - d)^2

    0 < -(n * d)
    0 < 8
    0 < 8 * (-(n * d))
    8 * (-(n * d)) = -8 * n * d
    0 < -8 * n * d
    (2 * (n + d) - d)^2 < (2 * (n + d) - d)^2 + (-8 * n * d) = (2 * n - d)^2
    abs(2 * (n + d) - d)^2 = (2 * (n + d) - d)^2 < (2 * n - d)^2 = abs(2 * n - d)^2

claim:
    ? forall n, d Z:
        n * d < 0
        =>:
            abs(2 * (n + d) - d) < abs(2 * n - d)

    0 <= abs(2 * (n + d) - d)
    0 <= abs(2 * n - d)
    abs(2 * (n + d) - d)^2 < abs(2 * n - d)^2

claim:
    ? forall n, d Z:
        n * d >= 0
        0 < d * (n - d)
        =>:
            abs(2 * (n - d) - d)^2 < abs(2 * n - d)^2

    0 < 8
    0 < 8 * (d * (n - d))
    8 * (d * (n - d)) = 8 * d * (n - d)
    0 < 8 * d * (n - d)
    (2 * (n - d) - d)^2 < (2 * (n - d) - d)^2 + 8 * d * (n - d) = (2 * n - d)^2
    abs(2 * (n - d) - d)^2 = (2 * (n - d) - d)^2 < (2 * n - d)^2 = abs(2 * n - d)^2

claim:
    ? forall n, d Z:
        n * d >= 0
        0 < d * (n - d)
        =>:
            abs(2 * (n - d) - d) < abs(2 * n - d)

    0 <= abs(2 * (n - d) - d)
    0 <= abs(2 * n - d)
    abs(2 * (n - d) - d)^2 < abs(2 * n - d)^2

have fn fmod(n Z, d Z) Z by induc abs(2 * n - d) from 0:
    case n * d < 0: fmod(n + d, d)
    case n * d >= 0:
        case 0 < d * (n - d): fmod(n - d, d)
        case 0 >= d * (n - d):
            case n = d: 0
            case n != d: n

have fn fdiv(n Z, d Z) Z by induc abs(2 * n - d) from 0:
    case n * d < 0: fdiv(n + d, d) - 1
    case n * d >= 0:
        case 0 < d * (n - d): fdiv(n - d, d) + 1
        case 0 >= d * (n - d):
            case n = d: 1
            case n != d: 0

prop fmod_add_fdiv_at_measure(m Z):
    forall u, v Z:
        abs(2 * u - v) = m
        =>:
            fmod(u, v) + v * fdiv(u, v) = u

claim:
    ? forall n, d Z:
        abs(2 * n - d) = 0
        =>:
            fmod(n, d) + d * fdiv(n, d) = n

    by cases:
        ? fmod(n, d) + d * fdiv(n, d) = n
        case n * d < 0:
            abs(2 * (n + d) - d) < abs(2 * n - d) = 0
            0 <= abs(2 * (n + d) - d)
            impossible abs(2 * (n + d) - d) < 0
        case n * d >= 0:
            by cases:
                ? fmod(n, d) + d * fdiv(n, d) = n
                case 0 < d * (n - d):
                    abs(2 * (n - d) - d) < abs(2 * n - d) = 0
                    0 <= abs(2 * (n - d) - d)
                    impossible abs(2 * (n - d) - d) < 0
                case 0 >= d * (n - d):
                    by cases:
                        ? fmod(n, d) + d * fdiv(n, d) = n
                        case n = d:
                            fmod(n, d) = 0
                            fdiv(n, d) = 1
                            fmod(n, d) + d * fdiv(n, d) = 0 + d * 1 = d = n
                        case n != d:
                            fmod(n, d) = n
                            fdiv(n, d) = 0
                            fmod(n, d) + d * fdiv(n, d) = n + d * 0 = n

$fmod_add_fdiv_at_measure(0)

claim:
    ? forall m Z:
        m >= 0
        forall y Z:
            y >= 0
            y <= m
            =>:
                $fmod_add_fdiv_at_measure(y)
        =>:
            $fmod_add_fdiv_at_measure(m + 1)

    claim:
        ? forall n, d Z:
            abs(2 * n - d) = m + 1
            =>:
                fmod(n, d) + d * fdiv(n, d) = n

        by cases:
            ? fmod(n, d) + d * fdiv(n, d) = n
            case n * d < 0:
                abs(2 * (n + d) - d) >= 0
                abs(2 * (n + d) - d) < abs(2 * n - d) = m + 1
                abs(2 * (n + d) - d) <= m or abs(2 * (n + d) - d) >= m + 1
                by cases:
                    ? abs(2 * (n + d) - d) <= m
                    case abs(2 * (n + d) - d) <= m:
                        do_nothing
                    case abs(2 * (n + d) - d) >= m + 1:
                        impossible abs(2 * (n + d) - d) < m + 1
                $fmod_add_fdiv_at_measure(abs(2 * (n + d) - d))
                n + d $in Z
                abs(2 * (n + d) - d) = abs(2 * (n + d) - d)
                fmod(n + d, d) + d * fdiv(n + d, d) = n + d
                fmod(n, d) = fmod(n + d, d)
                fdiv(n, d) = fdiv(n + d, d) - 1
                fmod(n, d) + d * fdiv(n, d) = fmod(n + d, d) + d * (fdiv(n + d, d) - 1) = fmod(n + d, d) + d * fdiv(n + d, d) - d = n + d - d = n
            case n * d >= 0:
                by cases:
                    ? fmod(n, d) + d * fdiv(n, d) = n
                    case 0 < d * (n - d):
                        abs(2 * (n - d) - d) >= 0
                        abs(2 * (n - d) - d) < abs(2 * n - d) = m + 1
                        abs(2 * (n - d) - d) <= m or abs(2 * (n - d) - d) >= m + 1
                        by cases:
                            ? abs(2 * (n - d) - d) <= m
                            case abs(2 * (n - d) - d) <= m:
                                do_nothing
                            case abs(2 * (n - d) - d) >= m + 1:
                                impossible abs(2 * (n - d) - d) < m + 1
                        $fmod_add_fdiv_at_measure(abs(2 * (n - d) - d))
                        n - d $in Z
                        abs(2 * (n - d) - d) = abs(2 * (n - d) - d)
                        fmod(n - d, d) + d * fdiv(n - d, d) = n - d
                        fmod(n, d) = fmod(n - d, d)
                        fdiv(n, d) = fdiv(n - d, d) + 1
                        fmod(n, d) + d * fdiv(n, d) = fmod(n - d, d) + d * (fdiv(n - d, d) + 1) = fmod(n - d, d) + d * fdiv(n - d, d) + d = n - d + d = n
                    case 0 >= d * (n - d):
                        by cases:
                            ? fmod(n, d) + d * fdiv(n, d) = n
                            case n = d:
                                fmod(n, d) = 0
                                fdiv(n, d) = 1
                                fmod(n, d) + d * fdiv(n, d) = 0 + d * 1 = d = n
                            case n != d:
                                fmod(n, d) = n
                                fdiv(n, d) = 0
                                fmod(n, d) + d * fdiv(n, d) = n + d * 0 = n

    $fmod_add_fdiv_at_measure(m + 1)

by strong_induc m from 0:
    ? $fmod_add_fdiv_at_measure(m)

    ? from m = 0:
        $fmod_add_fdiv_at_measure(0)

    ? strong_induc:
        $fmod_add_fdiv_at_measure(m + 1)

claim:
    ? forall n, d Z:
        fmod(n, d) + d * fdiv(n, d) = n

    forall n1, d1 Z:
        abs(2 * n1 - d1) >= 0
        $fmod_add_fdiv_at_measure(abs(2 * n1 - d1))
        fmod(n1, d1) + d1 * fdiv(n1, d1) = n1

claim:
    ? forall x, y Z:
        0 < y
        x * y >= 0
        =>:
            0 <= x

    by contra:
        ? 0 <= x
        x < 0
        x * y < 0
        impossible x * y >= 0

claim:
    ? forall x, y Z:
        0 < y
        0 >= y * (x - y)
        =>:
            x <= y

    by contra:
        ? x <= y
        y < x
        0 < x - y
        0 < y * (x - y)
        impossible 0 >= y * (x - y)

claim:
    ? forall x, y Z:
        x <= y
        x != y
        =>:
            x < y

    by contra:
        ? x < y
        x >= y
        x = y
        impossible x != y

prop fmod_bound_at_measure(m Z):
    forall u, v Z:
        abs(2 * u - v) = m
        0 < v
        =>:
            abs(fmod(u, v)) < abs(v)

claim:
    ? forall a, b Z:
        abs(2 * a - b) = 0
        0 < b
        =>:
            abs(fmod(a, b)) < abs(b)

    by cases:
        ? abs(fmod(a, b)) < abs(b)
        case a * b < 0:
            abs(2 * (a + b) - b) < abs(2 * a - b) = 0
            0 <= abs(2 * (a + b) - b)
            impossible abs(2 * (a + b) - b) < 0
        case a * b >= 0:
            by cases:
                ? abs(fmod(a, b)) < abs(b)
                case 0 < b * (a - b):
                    abs(2 * (a - b) - b) < abs(2 * a - b) = 0
                    0 <= abs(2 * (a - b) - b)
                    impossible abs(2 * (a - b) - b) < 0
                case 0 >= b * (a - b):
                    by cases:
                        ? abs(fmod(a, b)) < abs(b)
                        case a = b:
                            fmod(a, b) = 0
                            abs(fmod(a, b)) = abs(0) = 0
                            abs(b) = b
                            0 < abs(b)
                            abs(fmod(a, b)) < abs(b)
                        case a != b:
                            fmod(a, b) = a
                            by contra:
                                ? 0 <= a
                                a < 0
                                a * b < 0
                                impossible a * b >= 0
                            by contra:
                                ? a <= b
                                b < a
                                0 < a - b
                                0 < b * (a - b)
                                impossible 0 >= b * (a - b)
                            by contra:
                                ? a < b
                                a >= b
                                a = b
                                impossible a != b
                            abs(a) = a
                            abs(b) = b
                            0 <= fmod(a, b)
                            abs(fmod(a, b)) = fmod(a, b) = a < b = abs(b)

$fmod_bound_at_measure(0)

claim:
    ? forall m Z:
        m >= 0
        forall y Z:
            y >= 0
            y <= m
            =>:
                $fmod_bound_at_measure(y)
        =>:
            $fmod_bound_at_measure(m + 1)

    claim:
        ? forall a, b Z:
            abs(2 * a - b) = m + 1
            0 < b
            =>:
                abs(fmod(a, b)) < abs(b)

        by cases:
            ? abs(fmod(a, b)) < abs(b)
            case a * b < 0:
                abs(2 * (a + b) - b) >= 0
                abs(2 * (a + b) - b) < abs(2 * a - b) = m + 1
                abs(2 * (a + b) - b) <= m or abs(2 * (a + b) - b) >= m + 1
                by cases:
                    ? abs(2 * (a + b) - b) <= m
                    case abs(2 * (a + b) - b) <= m:
                        do_nothing
                    case abs(2 * (a + b) - b) >= m + 1:
                        impossible abs(2 * (a + b) - b) < m + 1
                $fmod_bound_at_measure(abs(2 * (a + b) - b))
                a + b $in Z
                abs(2 * (a + b) - b) = abs(2 * (a + b) - b)
                abs(fmod(a + b, b)) < abs(b)
                fmod(a, b) = fmod(a + b, b)
                fmod(a, b) - fmod(a + b, b) = 0
                abs(fmod(a, b)) - abs(fmod(a + b, b)) <= abs(fmod(a, b) - fmod(a + b, b)) = abs(0) = 0
                abs(fmod(a, b)) <= abs(fmod(a + b, b))
                abs(fmod(a, b)) <= abs(fmod(a + b, b)) < abs(b)
                abs(fmod(a, b)) < abs(b)
            case a * b >= 0:
                by cases:
                    ? abs(fmod(a, b)) < abs(b)
                    case 0 < b * (a - b):
                        abs(2 * (a - b) - b) >= 0
                        abs(2 * (a - b) - b) < abs(2 * a - b) = m + 1
                        abs(2 * (a - b) - b) <= m or abs(2 * (a - b) - b) >= m + 1
                        by cases:
                            ? abs(2 * (a - b) - b) <= m
                            case abs(2 * (a - b) - b) <= m:
                                do_nothing
                            case abs(2 * (a - b) - b) >= m + 1:
                                impossible abs(2 * (a - b) - b) < m + 1
                        $fmod_bound_at_measure(abs(2 * (a - b) - b))
                        a - b $in Z
                        abs(2 * (a - b) - b) = abs(2 * (a - b) - b)
                        abs(fmod(a - b, b)) < abs(b)
                        fmod(a, b) = fmod(a - b, b)
                        fmod(a, b) - fmod(a - b, b) = 0
                        abs(fmod(a, b)) - abs(fmod(a - b, b)) <= abs(fmod(a, b) - fmod(a - b, b)) = abs(0) = 0
                        abs(fmod(a, b)) <= abs(fmod(a - b, b))
                        abs(fmod(a, b)) <= abs(fmod(a - b, b)) < abs(b)
                        abs(fmod(a, b)) < abs(b)
                    case 0 >= b * (a - b):
                        by cases:
                            ? abs(fmod(a, b)) < abs(b)
                            case a = b:
                                fmod(a, b) = 0
                                abs(fmod(a, b)) = abs(0) = 0
                                abs(b) = b
                                0 < abs(b)
                                abs(fmod(a, b)) < abs(b)
                            case a != b:
                                fmod(a, b) = a
                                by contra:
                                    ? 0 <= a
                                    a < 0
                                    a * b < 0
                                    impossible a * b >= 0
                                by contra:
                                    ? a <= b
                                    b < a
                                    0 < a - b
                                    0 < b * (a - b)
                                    impossible 0 >= b * (a - b)
                                by contra:
                                    ? a < b
                                    a >= b
                                    a = b
                                    impossible a != b
                                abs(a) = a
                                abs(b) = b
                                0 <= fmod(a, b)
                                abs(fmod(a, b)) = fmod(a, b) = a < b = abs(b)

    $fmod_bound_at_measure(m + 1)

by strong_induc m from 0:
    ? $fmod_bound_at_measure(m)

    ? from m = 0:
        $fmod_bound_at_measure(0)

    ? strong_induc:
        $fmod_bound_at_measure(m + 1)

claim:
    ? forall a, b Z:
        0 < b
        =>:
            abs(fmod(a, b)) < abs(b)

    forall a1, b1 Z:
        0 < b1
        =>:
            abs(2 * a1 - b1) >= 0
            $fmod_bound_at_measure(abs(2 * a1 - b1))
            abs(fmod(a1, b1)) < abs(b1)

claim:
    ? forall a, b Z:
        b < 0
        =>:
            abs(fmod(a, -b)) < abs(b)

    0 < -b
    -b $in Z
    abs(fmod(a, -b)) < abs(-b)
    b <= 0
    abs(b) = -b
    abs(-b) = -b
    abs(-b) = abs(b)
    abs(fmod(a, -b)) < abs(b)

have fn gcd(a Z, b Z) Z by induc abs(b) from 0:
    case 0 < b: gcd(b, fmod(a, b))
    case 0 >= b:
        case b < 0: gcd(b, fmod(a, -b))
        case b >= 0:
            case 0 <= a: a
            case 0 > a: -a

have fn egcd_pair(a Z, b Z) cart(Z, Z) by induc abs(b) from 0:
    case 0 < b: (egcd_pair(b, fmod(a, b))[2], egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2])
    case 0 >= b:
        case b < 0: (egcd_pair(b, fmod(a, -b))[2], egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2])
        case b >= 0:
            case 0 <= a: (1, 0)
            case 0 > a: (-1, 0)

have fn egcd_l(a Z, b Z) Z = egcd_pair(a, b)[1]

have fn egcd_r(a Z, b Z) Z = egcd_pair(a, b)[2]

prop egcd_identity_at_measure(m Z):
    forall u, v Z:
        abs(v) = m
        =>:
            egcd_l(u, v) * u + egcd_r(u, v) * v = gcd(u, v)

claim:
    ? forall a, b Z:
        abs(b) = 0
        =>:
            egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)

    b = 0
    0 >= b
    b >= 0
    by cases:
        ? egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)
        case 0 <= a:
            egcd_pair(a, b) = (1, 0)
            egcd_l(a, b) = egcd_pair(a, b)[1] = (1, 0)[1] = 1
            egcd_r(a, b) = egcd_pair(a, b)[2] = (1, 0)[2] = 0
            gcd(a, b) = a
            egcd_l(a, b) * a + egcd_r(a, b) * b = 1 * a + 0 * b = a = gcd(a, b)
        case 0 > a:
            egcd_pair(a, b) = (-1, 0)
            egcd_l(a, b) = egcd_pair(a, b)[1] = (-1, 0)[1] = -1
            egcd_r(a, b) = egcd_pair(a, b)[2] = (-1, 0)[2] = 0
            gcd(a, b) = -a
            egcd_l(a, b) * a + egcd_r(a, b) * b = -1 * a + 0 * b = -a = gcd(a, b)

$egcd_identity_at_measure(0)

claim:
    ? forall m Z:
        m >= 0
        forall y Z:
            y >= 0
            y <= m
            =>:
                $egcd_identity_at_measure(y)
        =>:
            $egcd_identity_at_measure(m + 1)

    claim:
        ? forall a, b Z:
            abs(b) = m + 1
            =>:
                egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)

        by cases:
            ? egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)
            case 0 < b:
                abs(fmod(a, b)) >= 0
                abs(fmod(a, b)) < abs(b) = m + 1
                abs(fmod(a, b)) <= m or abs(fmod(a, b)) >= m + 1
                by cases:
                    ? abs(fmod(a, b)) <= m
                    case abs(fmod(a, b)) <= m:
                        do_nothing
                    case abs(fmod(a, b)) >= m + 1:
                        impossible abs(fmod(a, b)) < m + 1
                $egcd_identity_at_measure(abs(fmod(a, b)))
                fmod(a, b) $in Z
                abs(fmod(a, b)) = abs(fmod(a, b))
                egcd_l(b, fmod(a, b)) * b + egcd_r(b, fmod(a, b)) * fmod(a, b) = gcd(b, fmod(a, b))
                egcd_pair(a, b) = (egcd_pair(b, fmod(a, b))[2], egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2])
                egcd_l(a, b) = egcd_pair(a, b)[1] = (egcd_pair(b, fmod(a, b))[2], egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2])[1] = egcd_pair(b, fmod(a, b))[2]
                egcd_r(b, fmod(a, b)) = egcd_pair(b, fmod(a, b))[2]
                egcd_l(a, b) = egcd_r(b, fmod(a, b))
                egcd_r(a, b) = egcd_pair(a, b)[2] = (egcd_pair(b, fmod(a, b))[2], egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2])[2] = egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2]
                egcd_l(b, fmod(a, b)) = egcd_pair(b, fmod(a, b))[1]
                egcd_pair(b, fmod(a, b))[1] = egcd_l(b, fmod(a, b))
                egcd_pair(b, fmod(a, b))[2] = egcd_r(b, fmod(a, b))
                egcd_r(a, b) = egcd_pair(b, fmod(a, b))[1] - fdiv(a, b) * egcd_pair(b, fmod(a, b))[2] = egcd_l(b, fmod(a, b)) - fdiv(a, b) * egcd_r(b, fmod(a, b))
                fmod(a, b) + b * fdiv(a, b) = a
                a = fmod(a, b) + b * fdiv(a, b)
                a - b * fdiv(a, b) = fmod(a, b) + b * fdiv(a, b) - b * fdiv(a, b) = fmod(a, b)
                gcd(a, b) = gcd(b, fmod(a, b))
                egcd_l(a, b) * a + egcd_r(a, b) * b = egcd_r(b, fmod(a, b)) * a + (egcd_l(b, fmod(a, b)) - fdiv(a, b) * egcd_r(b, fmod(a, b))) * b = egcd_l(b, fmod(a, b)) * b + egcd_r(b, fmod(a, b)) * (a - b * fdiv(a, b)) = egcd_l(b, fmod(a, b)) * b + egcd_r(b, fmod(a, b)) * fmod(a, b) = gcd(b, fmod(a, b)) = gcd(a, b)
            case 0 >= b:
                by cases:
                    ? egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)
                    case b < 0:
                        abs(fmod(a, -b)) >= 0
                        abs(fmod(a, -b)) < abs(b) = m + 1
                        abs(fmod(a, -b)) <= m or abs(fmod(a, -b)) >= m + 1
                        by cases:
                            ? abs(fmod(a, -b)) <= m
                            case abs(fmod(a, -b)) <= m:
                                do_nothing
                            case abs(fmod(a, -b)) >= m + 1:
                                impossible abs(fmod(a, -b)) < m + 1
                        $egcd_identity_at_measure(abs(fmod(a, -b)))
                        fmod(a, -b) $in Z
                        abs(fmod(a, -b)) = abs(fmod(a, -b))
                        egcd_l(b, fmod(a, -b)) * b + egcd_r(b, fmod(a, -b)) * fmod(a, -b) = gcd(b, fmod(a, -b))
                        egcd_pair(a, b) = (egcd_pair(b, fmod(a, -b))[2], egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2])
                        egcd_l(a, b) = egcd_pair(a, b)[1] = (egcd_pair(b, fmod(a, -b))[2], egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2])[1] = egcd_pair(b, fmod(a, -b))[2]
                        egcd_r(b, fmod(a, -b)) = egcd_pair(b, fmod(a, -b))[2]
                        egcd_l(a, b) = egcd_r(b, fmod(a, -b))
                        egcd_r(a, b) = egcd_pair(a, b)[2] = (egcd_pair(b, fmod(a, -b))[2], egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2])[2] = egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2]
                        egcd_l(b, fmod(a, -b)) = egcd_pair(b, fmod(a, -b))[1]
                        egcd_pair(b, fmod(a, -b))[1] = egcd_l(b, fmod(a, -b))
                        egcd_pair(b, fmod(a, -b))[2] = egcd_r(b, fmod(a, -b))
                        egcd_r(a, b) = egcd_pair(b, fmod(a, -b))[1] + fdiv(a, -b) * egcd_pair(b, fmod(a, -b))[2] = egcd_l(b, fmod(a, -b)) + fdiv(a, -b) * egcd_r(b, fmod(a, -b))
                        fmod(a, -b) + (-b) * fdiv(a, -b) = a
                        a = fmod(a, -b) + (-b) * fdiv(a, -b)
                        a + b * fdiv(a, -b) = fmod(a, -b) + (-b) * fdiv(a, -b) + b * fdiv(a, -b) = fmod(a, -b)
                        gcd(a, b) = gcd(b, fmod(a, -b))
                        egcd_l(a, b) * a + egcd_r(a, b) * b = egcd_r(b, fmod(a, -b)) * a + (egcd_l(b, fmod(a, -b)) + fdiv(a, -b) * egcd_r(b, fmod(a, -b))) * b = egcd_l(b, fmod(a, -b)) * b + egcd_r(b, fmod(a, -b)) * (a + b * fdiv(a, -b)) = egcd_l(b, fmod(a, -b)) * b + egcd_r(b, fmod(a, -b)) * fmod(a, -b) = gcd(b, fmod(a, -b)) = gcd(a, b)
                    case b >= 0:
                        b = 0
                        by cases:
                            ? egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)
                            case 0 <= a:
                                egcd_pair(a, b) = (1, 0)
                                egcd_l(a, b) = egcd_pair(a, b)[1] = (1, 0)[1] = 1
                                egcd_r(a, b) = egcd_pair(a, b)[2] = (1, 0)[2] = 0
                                gcd(a, b) = a
                                egcd_l(a, b) * a + egcd_r(a, b) * b = 1 * a + 0 * b = a = gcd(a, b)
                            case 0 > a:
                                egcd_pair(a, b) = (-1, 0)
                                egcd_l(a, b) = egcd_pair(a, b)[1] = (-1, 0)[1] = -1
                                egcd_r(a, b) = egcd_pair(a, b)[2] = (-1, 0)[2] = 0
                                gcd(a, b) = -a
                                egcd_l(a, b) * a + egcd_r(a, b) * b = -1 * a + 0 * b = -a = gcd(a, b)

    $egcd_identity_at_measure(m + 1)

by strong_induc m from 0:
    ? $egcd_identity_at_measure(m)

    ? from m = 0:
        $egcd_identity_at_measure(0)

    ? strong_induc:
        $egcd_identity_at_measure(m + 1)

claim:
    ? forall a, b Z:
        egcd_l(a, b) * a + egcd_r(a, b) * b = gcd(a, b)

    forall a1, b1 Z:
        abs(b1) >= 0
        $egcd_identity_at_measure(abs(b1))
        egcd_l(a1, b1) * a1 + egcd_r(a1, b1) * b1 = gcd(a1, b1)
```

### 6. A Bijection From `N^2` To `N`

- Category: `case study`
- Purpose: Shows a bijection between N^2 and N.

```litex
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

prop exist_bijection(S, T set):
    exist f fn(x S) T st {$bijective_fn(S, T, f)}

claim:
    ? forall n N:
        exist! y N st {2 * y = n * (n + 1)}

    by cases:
        ? n * (n + 1) % 2 = 0
        case n % 2 = 0:
            n * (n + 1) % 2 = (n % 2) * ((n + 1) % 2) % 2 = 0 * ((n + 1) % 2) % 2 = 0 % 2 = 0
        case n % 2 = 1:
            (n + 1) % 2 = (n % 2 + 1 % 2) % 2 = 0
            n * (n + 1) % 2 = (n % 2) * ((n + 1) % 2) % 2 = 1 * 0 % 2 = 0 % 2 = 0
    obtain r from exist r N st {n * (n + 1) = 2 * r}
    witness exist y N st {2 * y = n * (n + 1)} from r:
        n * (n + 1) = 2 * r
        2 * r = n * (n + 1)
    forall y1, y2 N:
        2 * y1 = n * (n + 1)
        2 * y2 = n * (n + 1)
        =>:
            y1 = n * (n + 1) / 2 = y2
    exist! y N st {2 * y = n * (n + 1)}

have fn tri by exist!:
    ? forall n N:
        exist! y N st {2 * y = n * (n + 1)}

claim:
    ? tri(0) = 0
    2 * tri(0) = 0 * (0 + 1)
    tri(0) = (2 * tri(0)) / 2 = (0 * (0 + 1)) / 2 = 0

claim:
    ? forall n N:
        tri(n + 1) = tri(n) + n + 1
    2 * tri(n + 1) = (n + 1) * ((n + 1) + 1) = (n + 1) * (n + 2)
    2 * tri(n) = n * (n + 1)
    2 * (tri(n) + n + 1) = 2 * tri(n) + 2 * n + 2 = n * (n + 1) + 2 * n + 2 = (n + 1) * (n + 2)
    tri(n + 1) = (2 * tri(n + 1)) / 2 = ((n + 1) * (n + 2)) / 2 = (2 * (tri(n) + n + 1)) / 2 = tri(n) + n + 1

prop triangular_interval(n, s N):
    tri(s) <= n
    n < tri(s + 1)

have fn diagonal_index(u cart(N, N)) N = tri(u[1]) + u[2]

claim:
    ? forall u cart(N, N):
        u[2] <= u[1]
        =>:
            tri(u[1]) <= diagonal_index(u)
            diagonal_index(u) < tri(u[1] + 1)
    tri(u[1]) <= tri(u[1]) + u[2] = diagonal_index(u)
    diagonal_index(u) = tri(u[1]) + u[2] <= tri(u[1]) + u[1] < tri(u[1]) + u[1] + 1 = tri(u[1] + 1)

claim:
    ? forall a, b N:
        a < b
        =>:
            tri(a + 1) <= tri(b)
    a + 1 <= b
    2 * tri(a + 1) = (a + 1) * ((a + 1) + 1) <= b * (b + 1) = 2 * tri(b)
    tri(a + 1) = (2 * tri(a + 1)) / 2 <= (2 * tri(b)) / 2 = tri(b)

claim:
    ? forall u, v cart(N, N):
        u[2] <= u[1]
        v[2] <= v[1]
        u[1] < v[1]
        =>:
            diagonal_index(u) < diagonal_index(v)
    diagonal_index(u) < tri(u[1] + 1) <= tri(v[1]) <= diagonal_index(v)

## If two valid diagonal positions have the same number, they are on the same diagonal.
claim:
    ? forall u, v cart(N, N):
        u[2] <= u[1]
        v[2] <= v[1]
        diagonal_index(u) = diagonal_index(v)
        =>:
            u[1] = v[1]
    by contra:
        ? not u[1] < v[1]
        diagonal_index(u) < diagonal_index(v)
        impossible diagonal_index(u) = diagonal_index(v)
    by contra:
        ? not v[1] < u[1]
        diagonal_index(v) < diagonal_index(u)
        impossible diagonal_index(u) = diagonal_index(v)
    u[1] = v[1]

have fn cantor_pair(t cart(N, N)) N = tri(t[1] + t[2]) + t[2]

## On one diagonal, the offset determines the position.
claim:
    ? forall u, v cart(N, N):
        u[1] = v[1]
        diagonal_index(u) = diagonal_index(v)
        =>:
            u[2] = v[2]
    tri(u[1]) + u[2] = diagonal_index(u) = diagonal_index(v) = tri(v[1]) + v[2]
    u[2] = (tri(u[1]) + u[2]) - tri(u[1]) = (tri(v[1]) + v[2]) - tri(v[1]) = v[2]

claim:
    ? forall t1, t2 cart(N, N):
        cantor_pair(t1) = cantor_pair(t2)
        =>:
            t1 = t2
    have u cart(N, N) = (t1[1] + t1[2], t1[2])
    have v cart(N, N) = (t2[1] + t2[2], t2[2])
    u[2] = t1[2] <= t1[1] + t1[2] = u[1]
    v[2] = t2[2] <= t2[1] + t2[2] = v[1]
    diagonal_index(u) = tri(t1[1] + t1[2]) + t1[2] = cantor_pair(t1)
    diagonal_index(v) = tri(t2[1] + t2[2]) + t2[2] = cantor_pair(t2)
    u[1] = v[1]
    u[2] = v[2]
    t1[2] = u[2] = v[2] = t2[2]
    t1[1] = (t1[1] + t1[2]) - t1[2] = u[1] - u[2] = v[1] - v[2] = (t2[1] + t2[2]) - t2[2] = t2[1]
    t1 = (t1[1], t1[2]) = (t2[1], t2[2]) = t2

claim:
    ? forall a, b N:
        b <= a
        =>:
            a - b $in N
    a - b >= 0
    a - b $in Z
    a - b $in N

claim:
    ? forall n, s N:
        $triangular_interval(n, s)
        =>:
            n - tri(s) <= s
    n < tri(s + 1) = tri(s) + s + 1
    n <= (tri(s) + s + 1) - 1 = tri(s) + s
    n - tri(s) <= (tri(s) + s) - tri(s) = s

by induc n from 0:
    ? exist s N st {$triangular_interval(n, s)}

    ? from n = 0:
        tri(0) <= 0
        tri(0 + 1) = tri(0) + 0 + 1 = 1
        0 < 1 = tri(0 + 1)
        witness exist s N st {$triangular_interval(0, s)} from 0:
            $triangular_interval(0, 0)

    ? induc:
        obtain s from exist s N st {$triangular_interval(n, s)}
        by cases:
            ? exist t N st {$triangular_interval(n + 1, t)}
            case n + 1 < tri(s + 1):
                tri(s) <= n <= n + 1
                witness exist t N st {$triangular_interval(n + 1, t)} from s:
                    $triangular_interval(n + 1, s)
            case n + 1 >= tri(s + 1):
                tri((s + 1) + 1) = tri(s + 1) + (s + 1) + 1 = tri(s + 1) + s + 2
                n + 1 < n + 2 <= tri(s + 1) + s + 2 = tri((s + 1) + 1)
                witness exist t N st {$triangular_interval(n + 1, t)} from s + 1:
                    $triangular_interval(n + 1, s + 1)

claim:
    ? forall n N:
        exist t cart(N, N) st {n = cantor_pair(t)}
    obtain s from exist s N st {$triangular_interval(n, s)}
    have b N = n - tri(s)
    n - tri(s) <= s
    have a N = s - b
    a + b = (s - b) + b = s
    have p cart(N, N) = (a, b)
    cantor_pair(p) = tri(p[1] + p[2]) + p[2] = tri(a + b) + b = tri(s) + b = tri(s) + (n - tri(s)) = n
    witness exist t cart(N, N) st {n = cantor_pair(t)} from p:
        n = cantor_pair(p)

claim:
    ? $exist_bijection(cart(N, N), N)
    witness exist f fn(x cart(N, N)) N st {$bijective_fn(cart(N, N), N, f)} from cantor_pair
```

### 7. Every Integer Is Odd Or Even

- Category: `case study`
- Purpose: Shows an integer parity proof.

```litex
claim:
    ? forall n Z:
        n % 2 = 0 or n % 2 = 1
    by induc n from 0:
        ? n % 2 = 0 or n % 2 = 1
        0 % 2 = 0
        0 % 2 = 0 or 0 % 2 = 1

        claim:
            ? forall x Z:
                x >= 0
                x % 2 = 0 or x % 2 = 1
                =>:
                    (x + 1) % 2 = 0 or (x + 1) % 2 = 1

            by cases:
                ? (x + 1) % 2 = 0 or (x + 1) % 2 = 1
                case x % 2 = 0:
                    (x + 1) % 2 = (x % 2 + 1 % 2) % 2 = (0 + 1) % 2 = 1
                case x % 2 = 1:
                    (x + 1) % 2 = (x % 2 + 1 % 2) % 2 = (1 + 1) % 2 = 0
    by cases:
        ? n % 2 = 0 or n % 2 = 1
        case n >= 0:
            do_nothing
        case n < 0:
            -n >= 0
            (-n) % 2 = 0 or (-n) % 2 = 1
            by cases:
                ? (n) % 2 = 0 or (n) % 2 = 1
                case -n % 2 = 0:
                    (n) % 2 = (-(-n)) % 2 = (2 - ((-n) % 2)) % 2 = (2 - 0) % 2 = 0
                case -n % 2 = 1:
                    (n) % 2 = (-(-n)) % 2 = (2 - (-n) % 2) % 2 = (2 - 1) % 2 = 1
```

### 8. Nonnegative Integers Modulo 2

- Category: `case study`
- Purpose: Shows residue cases modulo 2.

```litex
claim:
    ? forall x Z:
        0 <= x
        =>:
            x % 2 = 0 or x % 2 = 1

    by induc x from 0:
        ? x % 2 = 0 or x % 2 = 1

        0 % 2 = 0

        claim:
            ? forall y Z:
                0 <= y
                y % 2 = 0 or y % 2 = 1
                =>:
                    (y + 1) % 2 = 0 or (y + 1) % 2 = 1

            by cases:
                ? (y + 1) % 2 = 0 or (y + 1) % 2 = 1
                case y % 2 = 0:
                    (y + 1) % 2 = (y % 2 + 1 % 2) % 2 = (0 + 1) % 2 = 1
                case y % 2 = 1:
                    (y + 1) % 2 = (y % 2 + 1 % 2) % 2 = (1 + 1) % 2 = 0
```

### 9. Induction For A Summation Formula

- Category: `case study`
- Purpose: Shows induction for a finite summation identity.

```litex
claim:
    ? forall n N_pos:
        sum(0, n, fn(x R) R {x}) = n * (n + 1) / 2

    by induc n from 1:
        ? sum(0, n, fn(x R) R {x}) = n * (n + 1) / 2

        ? from n = 1:
            sum(0, 0, fn(x R) R {x}) = 0
            sum(0, 1, fn(x R) R {x}) = sum(0, 0, fn(x R) R {x}) + fn(x R) R {x}(1)
            fn(x R) R {x}(1) = 1
            sum(0, 1, fn(x R) R {x}) = sum(0, 0, fn(x R) R {x}) + 1 = 0 + 1 = 1 = 1 * (1 + 1) / 2

        ? induc:
            sum(0, n + 1, fn(x R) R {x}) = sum(0, n, fn(x R) R {x}) + fn(x R) R {x}(n + 1)
            fn(x R) R {x}(n + 1) = n + 1
            sum(0, n + 1, fn(x R) R {x}) = sum(0, n, fn(x R) R {x}) + (n + 1) = n * (n + 1) / 2 + (n + 1) = (n + 1) * (n + 2) / 2 = (n + 1) * ((n + 1) + 1) / 2
```

---
