<div align="center">
  <img src="./assets/logo.PNG" alt="The Litex logo" width="300">

# Litex

### Write math as it is. See why it holds.

Created and maintained by Jiachen Shen.

*Litex is a set-theoretic formal language designed to be easy to learn and use.
Its source follows ordinary mathematical writing: users state objects and facts
directly—what they want to prove—while the system verifies bottom-up and returns
the grounds for each step, or where checking stops. It is also designed to
compile to Lean; some scenarios are already covered, with broader coverage
expected by the end of 2026. Together with humans and AI, this aims to form a
collaboration loop that can accumulate checkable verification work for Math for
AI.*

> **Litex is an experimental hobby project in beta; expect rough edges.**

Natural language is easy to understand but hard to verify rigorously; formal
code can be verified but is often hard to understand. Litex aims to bridge the
two: even if you are not a formalization expert and do not use Lean day to day,
you can still bring rigorous checking into your own work.

This README is a short introduction. For the full design argument, comparisons,
and trust boundaries, read the
[Litex Blueprint](docs/Litex_Blueprint.md)
([中文蓝图](docs/Litex中文蓝图.md)).
</div>

<!--
Litex positioning layers:
- Scientific object: how checkable knowledge is represented and constructed step by step.
- Scientific hypothesis: whether fact-oriented representation and transactional interaction form a useful formal-language design paradigm.
- Result variables: how that paradigm changes the cost of constructing, understanding, reviewing, repairing, and reusing checked knowledge.
- Potential impact: broader participation in verification; longer-term safer and more efficient AI reasoning.
The first three are the scientific core. The fourth is possible downstream impact, not an established result.
-->

## Start with the mathematics

Write the next fact you want to establish:

```litex
1 + 1 = 2
```

Litex checks well-definedness, finds a supported route when it can, and
records that route. When the context and rules cannot establish a fact, it
stops instead of silently accepting it. Accepted conclusions enter the context
for later reasoning—bottom-up, like an ordinary mathematical draft.

## Equality verification structure

Equality verification checks both objects first, then tries structural identity,
mathematical builtin rules, and one unified known-equality-class search. Class
search first cites stored equality paths; if necessary, it compares class
members with a restricted proof and retains both citation paths. Existing
object-definition, strategy, matching, forall and rewrite stages follow under
their original search permissions. See the
[step-by-step equality design](src/execute/execute_fact_stmt/verify_atomic_fact/verify_equality/README.md)
for the interfaces, result tree, recursion limits, and a membership example.

## The human–AI–Litex loop

```text
write what to prove
    → Litex verifies and returns grounds or a stopping point
    → keep valid progress
    → repair the local failure
    → continue from the checked context
```

Failed attempts can roll back without polluting the accepted context. Five
design lines carry this loop (see the Blueprint for detail):

| Line | What the author sees |
| --- | --- |
| **Set-theoretic objects** | Sets, elements, functions, and relations first. |
| **Fact-centered** | Write what should hold; the verifier searches by shape. |
| **Bottom-up** | Accepted facts extend the context for later steps. |
| **Traceable proof flow** | Readable dependencies; clear stop points on failure. |
| **Lean rechecking** | Compile supported routes to Lean for independent checking. |

Litex and Lean take nearly inverse defaults—one source leans toward *how*, the
other toward *what*. That is not a replacement claim; it is another entrance
into formalization for different habits of thought.

## Write in Litex. Recheck in Lean.

```text
Litex source → Litex verifier → ToLean → Lean proof terms → Lean kernel
```

Coverage is still partial. A Litex success is not automatically a Lean-kernel
success until the route is compiled and accepted by Lean. See
[ToLean](lean/README.md) and the
[Litex → Lean → Mathlib showcase](showcases/Litex_to_Lean_Mathlib_Pipeline/README.md).

## Try Litex

[Try Litex](https://litexlang.com) ·
[Blueprint](docs/Litex_Blueprint.md) ·
[中文蓝图](docs/Litex中文蓝图.md) ·
[Learner Cheatsheet](docs/Litex_Learner_Cheatsheet.md) ·
[Manual](docs/Manual.md) ·
[GitHub](https://github.com/litexlang/golitex)

Local install (macOS / Linux with Homebrew):

```bash
brew install litexlang/tap/litex
litex -version
litex -e '1 = 1'
```

See the [setup guide](docs/setup.md), [examples](examples/README.md), and
[CLI reference](docs/cli.md).

## Source gallery

A short look at what Litex source can look like. These snippets match the
Blueprint gallery; they are not a tutorial. For a larger runnable build-out, see
[Example of Building a Math System With Litex](showcases/Example_of_Building_A_Math_System_With_Litex/README.md).

The simplest equality:

```litex
1 + 1 = 2
```

A polynomial identity:

```litex
forall a, b R:
    (a + b)^2 = a^2 + 2 * a * b + b^2
```

A set fact:

```litex
forall s, t, u set:
    s $subset t
    =>:
        intersect(s, u) $subset intersect(t, u)
```

Nonnegative numbers stay nonnegative under addition:

```litex
forall x, y R:
    0 <= x
    0 <= y
    =>:
        0 <= x + y
```

A well-defined call when the domain condition is already known:

```litex
forall f fn(t R: t > 0) R, x R:
    x > 0
    =>:
        f(x) = f(x)
```

A proposition—define once, then use as an atomic fact:

```litex
prop is_positive(x R):
    x > 0

forall a, b R:
    $is_positive(a)
    a = b
    =>:
        $is_positive(b)
```

A known `forall` fact used to prove a concrete atomic fact:

<!-- litex:skip-test -->
```litex
prop is_positive(n R):
    exist a R+ st {n > a}

claim:
    ? forall x R:
        x > 10
        =>:
            $is_positive(x)
    witness exist a R+ st {x > a} from 10

have a R:
    a > 10

$is_positive(a)
```

Existential quantifiers—witness first, then obtain from the `exist` fact:

```litex
witness exist x R st {x = 0} from 0

obtain zero from exist x R st {x = 0}
zero = 0
```

A theorem—name a reusable conclusion, then cite it (transitivity of divisibility):

<!-- litex:skip-test -->
```litex
prop divides_by(d, n Z):
    exist k Z st {n = d * k}

thm divides_transitive:
    ? forall a, b, c Z:
        $divides_by(a, b)
        $divides_by(b, c)
        =>:
            $divides_by(a, c)
    obtain k from $divides_by(a, b)
    obtain m from $divides_by(b, c)
    c = b * m = (a * k) * m = a * (k * m)
    witness $divides_by(a, c) from k * m:
        c = a * (k * m)

witness $divides_by(2, 6) from 3
witness $divides_by(6, 30) from 5

by thm divides_transitive(2, 6, 30) => $divides_by(2, 30)
```

A named function:

<!-- litex:skip-test -->
```litex
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(2) = 1 / 2
```

A local `claim`—write the equalities that should hold along the way, without naming rewrite directions:

```litex
claim:
    ? forall a, b, c, d, g, f R:
        a * b = c * d
        g = f
        =>:
            a * (b * g) = c * (d * f)
    a * (b * g) = (a * b) * g = (c * d) * g = (c * d) * f = c * (d * f)
```

Proof by contradiction—show that “every real satisfies `x^2 >= x`” fails:

<!-- litex:skip-test -->
```litex
by contra:
    ? not forall x R:
        x^2 >= x
    impossible 0.5^2 >= 0.5
```

Proof by cases—exhaust the split, then close the goal in each branch:

```litex
have fn k(x R) R by cases:
    case x = 2: 3
    case x != 2: 4

have x R

by cases:
    ? k(x) > 2
    case x = 2:
        k(x) = 3 > 2
    case x != 2:
        k(x) = 4 > 2
```

Proof by induction—the sum of the first `n` odd positives is `n^2`:

<!-- litex:skip-test -->
```litex
have fn kth_odd(k Z) Z = 2 * k - 1

thm sum_first_odds:
    ? forall n Z:
        n >= 1
        =>:
            sum(1, n, kth_odd) = n^2
    by induc n from 1:
        ? sum(1, n, kth_odd) = n^2

        ? from n = 1:
            kth_odd(1) = 2 * 1 - 1 = 1
            sum(1, 1, kth_odd) = kth_odd(1) = 1 = 1^2

        ? induc:
            kth_odd(n + 1) = 2 * (n + 1) - 1
            sum(1, n + 1, kth_odd) = sum(1, n, kth_odd) + kth_odd(n + 1) = n^2 + (2 * (n + 1) - 1) = (n + 1)^2
```

A `struct`—a group: operation, identity, inverse on a carrier, and uniqueness of the identity:

```litex
struct Group<s nonempty_set>:
    mul fn(x, y s) s
    one s
    inv fn(x s) s
    <=>:
        forall x, y, z s:
            mul(mul(x, y), z) = mul(x, mul(y, z))
        forall x s:
            mul(x, one) = x
            mul(one, x) = x
            mul(inv(x), x) = one

forall s nonempty_set, G &Group<s>, identity s:
    forall a s:
        G.mul(identity, a) = a
        G.mul(a, identity) = a
    =>:
        identity = G.mul(G.one, identity) = G.one
```

A `template`—a parameterized definition family, then `\name<args>` to materialize:

<!-- litex:skip-test -->
```litex
struct Triple<X set>:
    first X
    second X
    third X

template<X set>:
    have fn triple(a, b, c X) &Triple<X> = (a, b, c)

\triple<R>(1, 2, 3) = (1, 2, 3)

have p &Triple<R> = \triple<R>(1, 2, 3)
p.first = 1
```

A simple word problem—identifiers may be written in Chinese:

<!-- litex:skip-test -->
```litex
# Mom's age is 3 times Xiao Ming's age plus 4; Xiao Ming is 15. How old is Mom?
have 小明年龄 R = 15
have 妈妈年龄 R = 3 * 小明年龄 + 4
妈妈年龄 = 3 * 15 + 4 = 49
```

## About

I am Jiachen Shen (沈嘉辰), a mathematics PhD student at Fudan University.
Lean showed me that mathematics and programming can meet in a real language.
Litex explores whether formal source can follow more closely the mental flow
of solving mathematical problems.

Special thanks to Wei Lin, Siqi Sun, Peng Sun, Chenxuan Huang, Yan Lu,
Sheng Xu, Keyao Zhu and Zhaoxuan Hong for their support and advice.

Litex is released under the [Apache License 2.0](LICENSE).
