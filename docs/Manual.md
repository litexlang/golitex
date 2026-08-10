# Manual

Jiachen Shen and The Litex Team, 2026-07-28. Email: litexlang@outlook.com

Run the examples in a browser: https://litexlang.com/doc/Manual

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual.md

## Manual Introduction

This manual is the reference for the public Litex language. It is organized so
that every concept has one main explanation: objects and their domain
conditions, facts, statements, the proof process, builtin verification, and
builtin inference. The [Syntax Reference](#syntax-reference) is an index into
those sections, not a second tutorial.

> **Litex is an experimental hobby project still in beta. Expect rough edges.**

### The core reading model

A Litex file is read from top to bottom. A successful statement may introduce
a name, define vocabulary, verify a fact, or add information that later
statements can reuse.

```litex
have x R = 2

x + 1 = 3
x^2 = 4
```

The first line introduces a real object `x` and records `x = 2`. The next two
lines state facts. Litex checks them from the current context and stores the
accepted facts for later use.

Keep three language categories separate:

| Category | Meaning | Examples |
|---|---|---|
| **Object** | A mathematical value or expression | `x`, `R`, `C`, `i`, `{1, 2}`, `x + 1`, `fn(t R) R` |
| **Fact** | A proposition about objects | `x = 2`, `x $in R`, `$prime(n)` |
| **Statement** | An action that checks or changes the context | `have`, a bare fact, `prop`, `claim`, `thm` |

For a factual statement, the user-facing outcomes are:

| Result | Meaning | Next action |
|---|---|---|
| `success` | Litex found a verification route. | Inspect the route when its provenance matters. |
| `unknown` | The fact is meaningful, but the current routes did not prove it. | Add a smaller equality, membership, domain fact, or lemma. |
| `error` | The statement could not be checked, often because of syntax or well-definedness. | Fix the statement or its object obligations first. |

A top-level runner may wrap an unresolved fact in an `error` result while
retaining its underlying `unknown_result`; the distinction remains visible in
the nested output. AI-generated explanations and Litex drafts are untrusted
until the displayed formal code has been checked.

A common mistake is to read `unknown` as false:

```text
have x R
x = 0
```

The second line is normally `unknown`, not a proof that `x != 0`. The context
only says that `x` is real.

### Reading path

Read [Objects](#objects), [Well-Defined Objects](#well-defined-objects),
[Factual Statements](#factual-statements), and the common parts of
[Statements](#statements) first. Read [Proof Process](#proof-process) when a
fact does not close. The rule and inference catalogues are lookup sections.

Long worked developments belong in [Litex Examples](Examples.md). Design
rationale belongs in the [FAQ](FAQ.md) and [Litex
Blueprint](Litex_Blueprint.md). Focused interface comparisons belong in
[Representative Lean–Litex Example
Comparisons](Representative_Lean_Litex_Example_Comparisons.md).

### Trust boundary

Litex is not a replacement for Lean, Coq, or Isabelle. Its checker, builtin
objects, builtin verification and inference rules, imported assumptions, and
every explicit `trust` or `axiom` are relevant to the trusted boundary.
`trust` records an assumption; it is not a proof. The current To-Lean code is a
deliberately partial compiler, not a general compiler. Its checked subset now
includes selected declarations, recursive proof certificates, explicit-value
`have`, checked real-carrier selection such as `have x R`, binary `by cases`,
atomic `by contra`, positive `witness exist`, and positive existential
extraction through `obtain` or body-style `have`, alongside a limited set of
object and builtin-rule backends. Selection and extraction consume retained
existential certificates and emit `Exists.choose` plus `choose_spec`; they do
not invent opaque values. `exist!`, `not exist`, and preimage extraction remain
outside this slice. Unsupported statements remain explicit instead of becoming
`sorry` or implicit axioms, so reliability claims must stay grounded in
inspectable rules, tests, verifier output, and trust reporting.

---

## Objects

An **object** is a mathematical value or expression. Objects do not assert
facts by themselves; a predicate or relation turns them into facts.

### Names, numbers, and arithmetic

Names refer to builtin objects, earlier declarations, local binders, or
module-qualified declarations. Arithmetic uses ordinary precedence:
parentheses and indexing bind tightly, then powers, multiplication and
division, then addition and subtraction.

```litex
have x R = 3

(x - 1)^2 = 4
abs(-x) = 3
sqrt(4) = 2
```

| Form | Meaning |
|---|---|
| `name`, `Module::name` | Local or module-qualified name |
| `2`, `3.5` | Exact numeric literal |
| `e`, `pi` | Native Euler and circle constants |
| `gcd(a, b)` | Native positive greatest common divisor for integer arguments, with `a != 0 or b != 0` |
| `lcm(a, b)` | Native nonnegative least common multiple for integer arguments; `lcm(0, 0) = 0` |
| `floor(a)`, `ceil(a)` | Native integer floor and ceiling of a real argument |
| `min(a, b)`, `max(a, b)` | Native binary minimum and maximum of real arguments |
| `exp(a)`, `ln(a)` | Native real exponential and natural logarithm |
| `sign(a)` | Native real sign function with values `-1`, `0`, and `1` |
| `factorial(n)` | Native natural-number factorial |
| `a + b`, `a - b`, `a * b`, `a / b` | Arithmetic operations |
| `a % b` | Euclidean integer remainder |
| `a^b` | Exponentiation |
| `abs(a)`, `sqrt(a)`, `log(base, a)` | Standard numeric objects |
| `sin(a)`, `cos(a)`, `tan(a)`, `cot(a)` | Native symbolic real trigonometric objects |
| `re(z)`, `img(z)`, `C_abs(z)` | Real coordinate, imaginary coordinate, and complex modulus |
| `finite_set_max(S)`, `finite_set_min(S)` | Extremum of a suitable finite set |

Concrete gcd calls normalize inside ordinary facts, so
`gcd(54, -24) = 6` verifies directly and `gcd(54, -24) + 1 = 7` behaves like
ordinary arithmetic. Write `eval gcd(54, -24)` when an explicit evaluation
statement is the intended presentation. Signs do not affect the positive
result. The pair `(0, 0)` is intentionally outside the object's domain.

Native `lcm`, integer rounding, and binary extrema likewise normalize exact
numeric inputs:

```litex
lcm(12, -18) = 36
lcm(0, 0) = 0
floor(3.75) = 3
floor(-3.75) = -4
ceil(3.25) = 4
min(7, -2) = -2
max(7, -2) = 7
```

Floor and ceiling return integers, expose their characteristic bounds, preserve
weak order, commute with integer translation, and are dual under negation.
`min` and `max` expose their argument bounds, componentwise monotonicity, and
the usual commutative, associative, idempotent, and absorption laws. Native
`lcm` is symmetric, divides by either nonzero input in the Euclidean-remainder
sense, is bounded by every positive common multiple, and satisfies
`lcm(a, b) * gcd(a, b) = abs(a * b)` for non-all-zero integer pairs.

```litex
forall x R:
    floor(x) $in Z
    ceil(x) $in Z
    floor(x) <= x
    x < floor(x) + 1
    ceil(x) - 1 < x
    x <= ceil(x)

forall a, b R:
    a <= b
    =>:
        min(a, b) = a
        max(a, b) = b

forall a, b R:
    a <= b
    =>:
        floor(a) <= floor(b)
        ceil(a) <= ceil(b)

forall x R, n Z:
    floor(x + n) = floor(x) + n
    floor(-x) = -ceil(x)
```

The five names are hard-reserved. LaTeX uses the conventional floor, ceiling,
minimum, maximum, and least-common-multiple notation. Python extraction uses
`math.floor`, `math.ceil`, `min`, `max`, and `math.lcm`. These objects are
outside the current checked To-Lean subset.

The second native-function batch adds `exp`, `ln`, `sign`, and `factorial`.
Their exact special values and finite integer calculations normalize directly:

```litex
exp(0) = 1
ln(1) = 0
sign(-9) = -1
sign(0) = 0
sign(2.5) = 1
factorial(10) = 3628800
```

`exp` maps reals to positive reals and preserves strict and weak order. `ln`
accepts positive real arguments, agrees with `log(e, x)`, and preserves strict
and weak order on that domain. Both functions also reflect strict/weak order
and equality, so their outputs can be used to recover input facts. The two
functions expose their inverse and elementary algebra laws. Litex does not
decimal-approximate transcendental values: `exp(2)` and `ln(2)` remain symbolic.

```litex
forall x R:
    exp(x) $in R+
    exp(x) = e^x
    ln(exp(x)) = x

forall x R:
    x > 0
    =>:
        exp(ln(x)) = x
        ln(x) = log(e, x)

forall a, b R:
    exp(a + b) = exp(a) * exp(b)

forall a, b R:
    a < b
    =>:
        exp(a) < exp(b)

forall a, b R+:
    a <= b
    =>:
        ln(a) <= ln(b)

forall a, b R:
    exp(a) = exp(b)
    =>:
        a = b

forall a, b R+:
    ln(a) < ln(b)
    =>:
        a < b
```

`sign` always returns an integer between `-1` and `1`, preserves weak order,
is odd and multiplicative, and characterizes zero and nonzero arguments. It
also satisfies `sign(x) * abs(x) = x`. `factorial` accepts `N`, returns `N+`,
exposes the successor recurrence, preserves weak order (and strict order away
from the `0! = 1!` boundary), and makes every earlier factorial divide a later
one. All four names are hard-reserved. Python extraction uses `math.exp`,
`math.log`, a conditional sign expression, and `math.factorial`. These objects
are outside the current checked To-Lean subset.

The parser does not make an invalid expression meaningful:

```text
have x R
sqrt(x) = 0
```

This is an `error` unless the context proves `0 <= x`; the problem occurs
before equality verification.

### Native real constants (beta preview)

`e` and `pi` are primitive scalar objects. They are parsed directly into
dedicated object forms: neither is a decimal `Number`, an ordinary `Atom`, nor
a name introduced by a Litex declaration. In particular, `std/basics` does not
define or trust either constant.

The kernel provides their carrier, positivity, and nonzero facts:

```litex
e $in R+
pi $in R+
e $in R
pi $in R
e $in C
pi $in C
0 < e
0 < pi
e != 0
pi != 0
```

Both names are hard-reserved and cannot be rebound as declarations,
parameters, indices, or fields. Longer names such as `e1`, `epsilon`, and
`pi_value` remain ordinary identifiers.

The output backends preserve the named constants rather than inserting decimal
approximations:

| Backend | `e` | `pi` |
|---|---|---|
| LaTeX | `\mathrm{e}` | `\pi` |
| Python extractor | `math.e` | `math.pi` |

The current checked To-Lean subset does not lower these symbolic constants.

The symbolic evaluator likewise does not assign decimal runtime values to
these constants.

### Native real trigonometry (beta preview)

`sin(x)`, `cos(x)`, `tan(x)`, and `cot(x)` are dedicated builtin object forms,
not source-defined functions or ordinary function calls. Their arguments are
real angles in radians. `sin` and `cos` are total on `R`; `tan(x)` is
well-defined only when `cos(x) != 0`, and `cot(x)` only when `sin(x) != 0`.

The kernel keeps one centralized symbolic interface. Its core consists of the
values at `0` and `pi / 2`, the sine and cosine addition formulas, the
unit-circle identity, and the quotient definitions of tangent and cotangent:

```litex
sin(0) = 0
cos(0) = 1
sin(pi / 2) = 1
cos(pi / 2) = 0

forall x, y R:
    sin(x + y) = sin(x) * cos(y) + cos(x) * sin(y)
    cos(x + y) = cos(x) * cos(y) - sin(x) * sin(y)

forall x R:
    sin(x)^2 + cos(x)^2 = 1
```

A single canonical normalizer builds the derived layers from that interface.
It handles parity, difference and double-angle formulas, values at integral
and supported half-integral multiples of `pi`, cofunction and shift formulas,
periodicity, and the `[-1, 1]` bounds. Those are not maintained as unrelated
copies:

```litex
forall x R:
    sin(-x) = -sin(x)
    cos(-x) = cos(x)
    sin(2 * x) = 2 * sin(x) * cos(x)
    cos(2 * x) = 1 - 2 * sin(x)^2
    sin(x + 2 * pi) = sin(x)
    cos(x + 2 * pi) = cos(x)
    -1 <= sin(x) <= 1
    -1 <= cos(x) <= 1

sin(pi) = 0
cos(pi) = -1
```

Tangent and cotangent uses must expose the appropriate denominator fact:

```litex
forall x R:
    cos(x) != 0
    =>:
        tan(x) = sin(x) / cos(x)
        cos(x + pi) != 0
        tan(x + pi) = tan(x)

forall x R:
    sin(x) != 0
    =>:
        cot(x) = cos(x) / sin(x)
        sin(x + pi) != 0
        cot(x + pi) = cot(x)
```

The kernel also supplies `3 < pi < 4`, the standard sign intervals for sine,
cosine, tangent, and cotangent, and local monotonicity for sine on
`[-pi/2, pi/2]`, cosine on `[0, pi]`, tangent on `(-pi/2, pi/2)`, and
cotangent on `(0, pi)`. Tangent and cotangent statements must still make each
argument's open-domain bounds available for well-definedness.

The preview intentionally does not assign every familiar special-angle value;
for example, `sin(pi / 6) = 1 / 2` still needs an explicit source fact.
Complex trigonometry, inverse trigonometric functions, analytic definitions,
and continuity theorems are also outside this interface.

The names `sin`, `cos`, `tan`, and `cot` are hard-reserved. Their bare names
are not first-class function values; higher-order code can use
`fn(x R) R {sin(x)}`. LaTeX emits standard trigonometric notation. The
evaluator and current Python extractor report native trigonometric expressions
as unsupported. They are also outside the current checked To-Lean subset rather
than being assigned a library semantics silently.

### Complex scalars (beta preview)

`C` is the largest builtin scalar set, and `C*` is its nonzero subset
`C \ {0}`. The standard inclusion chain is `N` through `Z`, `Q`, and `R` into
`C`; on the nonzero branch, `R* $subset C*` and `C* $subset C`. Membership in
`C*` therefore supplies both complex membership and disequality from zero.
Arithmetic does not erase narrower information: an operation whose operands
are known integers or reals keeps the existing narrow result whenever that
rule applies, and falls back to `C` only when a complex carrier is needed.

The native imaginary unit and coordinate interface are symbolic builtin
objects:

```litex
i $in C
i * i = -1
i^2 = -1
i^4 = 1
i^(-1) = -i
i $in C*
not 0 $in C*

have w C*
w $in C
w != 0

re(3) = 3
img(3) = 0
re(i) = 0
img(i) = 1

forall a, b R:
    re(a + b * i) = a
    img(a + b * i) = b

forall z C:
    z = re(z) + img(z) * i
    C_abs(z) = sqrt(re(z)^2 + img(z)^2)
    0 <= C_abs(z)
```

`re(z)`, `img(z)`, and `C_abs(z)` are dedicated unary builtin expression
forms with domain `C` and result set `R`, at the same object-model level as
`abs(z)`. Their bare names are not first-class function values; higher-order
code can use `fn(z C) R {re(z)}` and the analogous lambdas. For a real input,
`C_abs(r) = abs(r)`, while `C_abs(i) = 1`. Equality and inequality (`=`, `!=`)
are available for complex objects. Ordered comparisons, signs, real intervals,
`abs`, `sqrt`, and `log` remain real-domain operations.

Known complex equalities can be observed through `re` and `img`. The verifier
also supplies the standard coordinate formulas for native complex addition,
subtraction, multiplication, division/inverses, and natural successor powers.
The modulus is multiplicative, satisfies the triangle and reverse-triangle
inequalities, and is strictly positive exactly away from zero. Thus a proof can
reason directly about `re(z * w)`, `img(z / w)`, and `C_abs(z * w)` without
introducing a coordinate-pair compatibility layer.

Natural powers `z^n` are defined for `z` in `C` and `n` in `N`, including the
existing convention `0^0 = 1`. The additional integer-exponent branch requires
a nonzero complex base; the ordinary exponent-addition law remains available
on that branch. General `C^R` or `C^C` exponentiation is not part of this
preview.

The following are deliberately invalid domain examples:

<!-- litex:skip-test -->
```litex
i < 1
abs(i)
sqrt(i)
log(2, i)
i^(1 / 2)
0^(-1)
```

`C`, `i`, `re`, `img`, and `C_abs` are hard-reserved builtin names and cannot
be rebound as declarations, parameters, indices, or fields. See the
[complex scalar migration guide](Complex_Scalar_Migration.md) for mechanical
renaming advice and compatibility boundaries.

### Sets and set-forming objects

Litex exposes sets, membership, and set operations directly.

```litex
2 $in union({1, 2}, {2, 3})
2 $in intersect({1, 2}, {2, 3})
2 $in set_minus({1, 2}, {1})

by def {x R: 0 <= x} $subset R
```

| Form | Meaning |
|---|---|
| `N`, `Z`, `Q`, `R`, `C` | Standard number sets |
| `N+`, `Z+`, `Q+`, `R+` | Strictly positive standard subsets; `Z+` is the same set as `N+` |
| `Z-`, `Q-`, `R-` | Strictly negative standard subsets |
| `Z*`, `Q*`, `R*`, `C*` | Nonzero standard subsets |
| `{a, b, ...}` | Displayed finite set |
| `{x S: facts}` | Set comprehension over `S` |
| `union(A, B)`, `intersect(A, B)` | Binary union and intersection |
| `set_minus(A, B)` | Relative complement; write symmetric difference as `union(set_minus(A, B), set_minus(B, A))` |
| `big_union(F)`, `big_intersect(F)` | Union or intersection of a family |
| `power_set(A)` | Set of subsets of `A` |
| `replacement(P, A)` | Replacement set defined by a functional predicate `P` |
| `general_cart(I, S, g)` | Choice functions selecting one value from each factor `g(alpha)` |

The suffix must be adjacent to its base. These compact forms are canonical;
the verifier prints the same spelling.

```litex
have n N+
n $in N+
have z Z-
z $in Z-
have x R*
x $in R*
have w C*
w $in C
w != 0
```

The signs are strict: `+` means greater than zero, `-` means less than zero,
and `*` means nonzero. `N*` is not a standard spelling; use `N+` for nonzero
naturals.

Set-builder conditions are facts, not arbitrary statements:

```text
{x R: have y R = x}
```

This is a parse `error`. Use facts such as `{x R: x >= 0}` inside the builder.

For a family `g` of nonempty sets indexed by `I`, `general_cart(I, S, g)` is
the set of choice functions selecting an element of each `g(alpha)`:

```litex
have I set
have S nonempty_set
trust forall A S => {$is_nonempty_set(A)}
have g fn(alpha I) S

by thm general_cart_nonempty_by_choice_from_family(general_cart(I, S, g))
general_cart(I, S, g) = {f fn(t I) big_union(S): forall alpha I => {f(alpha) $in g(alpha)}}
```

The `trust` line makes the required factor-nonemptiness background explicit,
and the named builtin theorem makes the axiom-of-choice step explicit. The
equality shows the canonical mathematical shape of the general product.

### Functions, application, and range

`fn(...) ReturnSet` is a function set. Adding `{body}` produces an anonymous
function value. Function calls are ordinary objects, but the argument and all
domain conditions must be verified.

```litex
have fn square_plus_one(t R) R = t^2 + 1

square_plus_one(3) = 10
fn(x R) R {x + 1}(2) = 3
square_plus_one(3) $in fn_range(square_plus_one)
```

| Form | Meaning |
|---|---|
| `fn(x S) T` | Functions from `S` to `T` |
| `fn(x S: conditions) T` | Function set with domain conditions |
| `fn(x S) T {body}` | Anonymous function value |
| `f(a)` or `f(a)(b)` | Function application, including curried application |
| `fn_range(f)` | Image of the known domain of `f` |
| `fn_range(fn(x A) T {f(x)})` | Image of an explicit restriction to `A` |

Function parameter domains are read from left to right, so a later domain may
cite an earlier parameter. The return set is checked in the scope of all
function parameters and may cite them too. At application, Litex substitutes
the actual arguments into that return set before checking later calls or
membership facts:

```litex
have g fn(S power_set(R)) fn(x S) R
g(R)(0) = g(R)(0)
```

Here the first application instantiates the return set of `g(R)` as
`fn(x R) R`. This is controlled set-valued dependency inside Litex's
set-theoretic function model. It does not make the binder kinds `set`,
`nonempty_set`, or `finite_set` into ordinary function domains; use `template`
for a family parameterized by an arbitrary set.

A declared codomain does not waive the input condition:

```text
have fn reciprocal(x R: x != 0) R = 1 / x
reciprocal(0) = 0
```

The call is an `error` because `0 != 0` cannot be established.

### Products, tuples, sequences, and matrices

Cartesian products and indexed data remain ordinary set-theoretic objects.

```litex
(1, 2) $in cart(R, Z)
tuple_dim((1, 2)) = 2
proj(cart(R, Z), 1) = R
(1, 2)[1] = 1

[1, 2, 3] $in finite_seq(N+, 3)
[[1, 0], [0, 1]] $in matrix(Z, 2, 2)
```

| Form | Meaning |
|---|---|
| `cart(A, B, ...)` | Cartesian product |
| `cart_dim(c)`, `proj(c, i1)` | Product dimension and the `i1`-th factor set |
| `(a, b, ...)`, `tuple_dim(t)` | Tuple and tuple dimension |
| `finite_seq(S, n)`, `seq(S)` | Finite or infinite sequence set |
| `[a, b, ...]`, `a[i1]` | Displayed finite sequence and index access |
| `matrix(S, r, c)` | Matrix set |
| `[[...], [...]]` | Displayed matrix |
| `A '+ B`, `A '- B`, `A '* B` | Matrix addition, subtraction, multiplication |
| `c *' A`, `A '^ n` | Scalar multiplication and matrix power |

Dimensions are checked, not inferred from wishful notation:

```text
[[1, 2], [3]] $in matrix(Z, 2, 2)
```

This is an `error` because the displayed rows do not have one common width.

### Cardinality, finite aggregation, and intervals

Finite sets, integer ranges, and real intervals have dedicated object forms.

```litex
finite_set_size({1, 2, 3}) = 3
sum(1, 3, fn(i1 Z) Z {i1}) = sum(1, 2, fn(i1 Z) Z {i1}) + fn(i1 Z) Z {i1}(3)
product(1, 3, fn(i1 Z) Z {i1}) = product(1, 2, fn(i1 Z) Z {i1}) * fn(i1 Z) Z {i1}(3)
reduce(1, 3, fn(i1 Z) Z {i1}, fn(x, y Z) Z {x - y}, 0) = -6
finite_set_reduce({3, 1, 2}, fn(i1 Z) Z {i1}, fn(x, y Z) Z {x + y}, 0) = 6

2 $in range(0, 3)
3 $in closed_range(0, 3)
1 $in '[0, 1]
```

| Form | Meaning |
|---|---|
| `finite_set_size(S)` | Cardinality of a finite set |
| `finite_set_sum(S, f)`, `finite_set_product(S, f)` | Aggregate over a finite set |
| `sum(first, last, f)`, `product(first, last, f)` | Aggregate over a closed integer index range |
| `reduce(first, last, f, op, seed)` | Ascending left fold over a closed integer index range |
| `finite_set_reduce(S, f, op, seed)` | Order-independent fold over a finite set |
| `range(a, b)` | Integers `a <= x < b` |
| `closed_range(a, b)`, `a...b` | Integers `a <= x <= b` |
| `'(a, b)`, `'(a, b]`, `'[a, b)`, `'[a, b]` | Bounded real intervals |
| `'(a,)`, `'[a,)`, `'(,b)`, `'(,b]` | Real rays |

All four aggregate forms require the iterand to be unary and to declare a
scalar return carrier: Litex must prove `return_set $subset C` under the
function's parameter and domain assumptions. The function body must separately
belong to that declared return carrier. Range `sum` and `product` also require
integer endpoints with `first <= last`; finite-set aggregates require a finite
set and a function defined on the aggregated domain.
Consequently, `finite_set_sum(3...1, fn(k Z) Z {0}) = 0` and the analogous
empty product equal to `1` are well-defined, while range `sum(3,1,...)` and
`product(3,1,...)` remain outside the nonempty range-aggregate contract.

Closed-range sums distribute over pointwise subtraction when all three
summands use the same endpoints and their declared scalar return sets embed in
an additive carrier (`Z`, `Q`, `R`, or `C`). Unary negation is the existing
scalar-multiplication rule with scalar `-1`:

```litex
have f fn(k Z) R
have g fn(k Z) R

sum(1, 3, fn(k Z) R {f(k) - g(k)}) = sum(1, 3, fn(k Z) R {f(k)}) - sum(1, 3, fn(k Z) R {g(k)})
sum(1, 3, fn(k Z) R {-f(k)}) = -sum(1, 3, fn(k Z) R {f(k)})
```

This rule does not totalize natural subtraction: a function declared to return
`N` must still prove that its pointwise difference belongs to `N`.

The generic folds are not restricted to scalar arithmetic. For both forms,
`op` must have an unconditional homogeneous signature `fn(x, y T) T`, `f`
must be unary with return set `T`, and `seed` must belong to `T`; the result
then belongs to `T`. `reduce` visits the closed integer interval from left to
right and returns `seed` when `last < first`. Thus its defining nonempty step
is `op(reduce(first, last - 1, f, op, seed), f(last))`. Equivalently, it may
consume the first value into the seed and continue at `first + 1`:
`reduce(first + 1, last, f, op, op(seed, f(first)))`.

Because a finite set has no iteration order, `finite_set_reduce` additionally
requires Litex to verify that `op` is associative and commutative on `T`.
Displayed-set order is used only to produce an evaluation witness. The empty
set returns `seed`; `seed` need not be an identity element. If order matters
or `op` is noncommutative, provide an explicit integer enumeration and use
`reduce` instead.

Generic reductions connect to the existing aggregate and function interfaces
through the following direct rules:

| Verified shape | Required relationship |
|---|---|
| `reduce(a,b,f,op,0) = sum(a,b,g)` | Same bounds, `f` and `g` pointwise equal on `a...b`, and `op(x,y) = x + y` on its carrier |
| `reduce(a,b,f,op,1) = product(a,b,g)` | Same bounds, pointwise-equal functions, and `op(x,y) = x * y` |
| `finite_set_reduce(S,f,op,0) = finite_set_sum(S,g)` | Equal finite sets, pointwise equality on `S`, and additive `op` |
| `finite_set_reduce(S,f,op,1) = finite_set_product(S,g)` | Equal finite sets, pointwise equality on `S`, and multiplicative `op` |
| two reductions with otherwise equal arguments | `$fn_eq_in(f,g,a...b)` or `$fn_eq_in(f,g,S)` |
| `reduce(a,b,f,op,s) = reduce(c,d,fn(k Z) T {f(a+(k-c))},op,s)` | `a <= b` and `b-a = d-c`; this is an order-preserving translation, so no operation law is needed |
| `reduce(a,b,f,op,s) = reduce(a+1,b,f,op,op(s,f(a)))` | `a <= b`; consume the first value into the seed |
| `reduce(a,b,f,op,s) = op(reduce(a,b-1,f,op,s),f(b))` | `a <= b`; consume the last value after the prefix |
| `reduce(a,c,f,op,s) = reduce(b+1,c,f,op,reduce(a,b,f,op,s))` | `a <= b < c`; no commutativity assumption |
| `finite_set_reduce(union(A,B),f,op,s) = finite_set_reduce(A,f,op,finite_set_reduce(B,f,op,s))` | `intersect(A,B) = {}` |
| a finite-set pullback written as `fn(y B) T {f(g(y))}` | `$bijective(B,A,g)`; a checked named function may unfold once to the same shape |

The operation test is extensional rather than name-based. A user-defined prop
may provide `forall x, y T: op(x,y) = x + y`; once that prop is verified and
its definition has unfolded into the proof context, the sum bridge can use the
fact. Likewise, congruence consumes the existing `$fn_eq_in` predicate, and
reindexing consumes the existing `$bijective` predicate. These are one-step
builtin rules: they use relationships already present in the context but do
not invent a pointwise proof, disjointness fact, or bijection.

For interval translation, the target index `k` is sent to
`a + (k - c)`. Equal differences `b - a = d - c` ensure that the two closed
integer ranges have the same length, and the pullback condition ensures that
the folds see the same value sequence. The common zero-based form takes
`c = 0` and `d = b - a`. If `b < a`, equally long translated intervals are
both empty and therefore return the same seed.

This rule is deliberately not arbitrary bijective reindexing. A
`closed_range` is a set object, but `reduce` uses its ascending enumeration;
a bijection may reverse that order. When `op` is associative and commutative,
first bridge the range reduction to `finite_set_reduce` and use its existing
`$bijective` substitution rule. Otherwise the translation must preserve the
index order.

The disjoint-union formula deliberately nests the second reduction as the
first reduction's seed. Writing `op(reduce(A,...,s), reduce(B,...,s))` would
count a non-identity seed twice, so that more familiar formula is not a generic
law. With additive seed `0` or multiplicative seed `1`, first bridge to
`finite_set_sum` or `finite_set_product` and use their existing union rules.

Integer ranges are always subsets of `Z` (and its standard supersets). If the
lower endpoint is known in `N` or `N+`, the range is also a subset of that
carrier. A set-builder over any finite base is finite, so a finite, nonempty
filtered integer range can feed `finite_set_min` or `finite_set_max` without a
separate trust boundary.

Finite sums also respect proved pointwise equality on their closed index
range. This applies both to sums with the same bounds and to integer-shifted
bounds: prove the corresponding guarded `forall` for the shared or target
range, then state the aggregate equality. A common anonymous summand carrier
such as `N+` is preserved while checking the pointwise premise.

The operations still require suitable domains:

```text
finite_set_size(R) = 1
```

This is an `error`, because the context does not establish that `R` is finite.

All four aggregate forms use the function return set to select their result
carrier. A `C`-valued function gives a result in `C`; functions returning
`N`, `Z`, `Q`, or `R` keep their narrower established result. Empty finite
sums and products remain `0` and `1`. The interval forms still require the
first index to be at most the last. Ordered, positive, and absolute-value
aggregate rules still require a real-valued iterand.

### Struct objects and explicit or default-view field access (preview)

A `struct` defines a named view of a Cartesian product. `&Name<args>` is the
set-like struct object. Select a view explicitly with `&Name{obj}.field`, or
bind a fresh name with an explicit struct type and then use `obj.field`.

A structure with two or more fields uses that Cartesian-product
representation. A one-field structure is instead a named view of the sole
field carrier, and selecting its only field is an identity projection. This
supports mathematically natural objects such as a metric space carrying only
its distance operation or a partial order carrying only its order relation,
without inventing a dummy field. A structure must still declare at least one
field.

```litex
struct Point:
    x R
    y R

by thm struct_member((1, 2), &Point)
have p &Point = (1, 2)

&Point{p}.x = 1
p.y = 2
```

Inside a parenthesized function, proposition, or theorem argument list,
`unfold` is a compile-time argument spread. For a struct value it contributes
all declared fields, strictly in declaration order:

```litex
struct Point:
    x R
    y R

by thm struct_member((1, 2), &Point)
have p &Point = (1, 2)

prop has_point_coordinates(x, y R):
    x = x

by def:
    ? $has_point_coordinates(unfold p)
by def:
    ? $has_point_coordinates(unfold &Point{p})
```

Both calls elaborate to `$has_point_coordinates(p.x, p.y)`. The first uses
the default view selected by `p &Point`; the second selects the view
explicitly and still verifies `p $in &Point`. Only fields are spread. Struct
header parameters and `<=>:` facts are not positional arguments. Consequently,
adding, removing, or reordering a struct field intentionally changes the
argument list produced by `unfold`.

Tuple literals can also be spread, as in `f(unfold (a, b, c))`. A named tuple
is accepted when its arity is known at compile time, including a binder typed
by `cart(A, B, C)`; it elaborates to `f(t[1], t[2], t[3])`. A tuple known only
to satisfy `$is_tuple(t)` has no static arity and is rejected. `unfold` is not
a runtime object, and ordinary arity, membership, and function-domain checks
run on the expanded arguments.

If a selected field is itself declared directly with a struct type, field
notation may continue through that declared view:

```litex
struct Coordinates:
    x R
    y R

struct TaggedPoint:
    point &Coordinates
    tag N

by thm struct_member((1, 2), &Coordinates)
by thm struct_member(((1, 2), 0), &TaggedPoint)
have item &TaggedPoint = ((1, 2), 0)
item.point.x $in R
```

Here `item.point.x` lowers to
`&Coordinates{&TaggedPoint{item}.point}.x`. Parameterized and
module-qualified struct field types work the same way. A final field may be
called, as in `space.scalars.mul(a, b)`, but field access after a call, index,
or parenthesized expression is not currently supported; select that next view
explicitly with `&Struct{expr}.field`.

When `expr` is a materialized template-selected struct object, a callable
field projects through the selected tuple value before application. Thus an
entries field defined by an anonymous function can be evaluated directly once
the selected object's struct membership is known.

A vector-space structure can own its scalar system rather than asking each
single-space theorem to carry scalar operations separately. With
`space &VectorSpace<s,V>`, ordinary code can write
`space.smul(space.scalars.mul(a,b),v)`. A relation that joins two spaces, such
as linearity of a map, records one compatibility fact
`Vspace.scalars = Wspace.scalars`; callers then pass the spaces themselves.

A later membership fact does not choose a default view retroactively:

```text
struct Point:
    x R
    y R

have p cart(R, R) = (1, 2)
by thm struct_member(p, &Point)
p.x = 1
```

The last line is a parse `error`. Bind `p &Point` or write
`&Point{p}.x` explicitly. Chained notation follows only a field declared
directly as `&Struct<...>`; it does not follow a named set definition or search known
membership facts for a possible view.

### Template instances

`template` defines a family whose parameters belong to the definition itself.
The current instance syntax is `\name<args>`.

```litex
template<S set>:
    have carrier_copy set = S

\carrier_copy<R> = R
\carrier_copy<Z> = Z
```

A template parameter such as `S set` is not a function argument ranging over a
set of all sets. The body is checked once in the parameterized context and is
materialized at an instance.

When a template selects a set-builder value, the instantiated object preserves
that defining view in both directions:

```litex
abstract_prop marked(x)

template<S set>:
    have marked_elements power_set(S) = {x S: $marked(x)}

trust $marked(1)
by thm defined_set_member(1, \marked_elements<R>)
```

Conversely, known membership in `\marked_elements<R>` exposes `$marked(1)`.
The explicit builtin theorem still requires the base-set membership and every
defining fact; the named definition does not invent membership.

```text
template<S set>:
    have carrier_copy set = S

carrier_copy<R> = R
```

With the current parser, omitting the backslash is a parse `error`; bare
`name<...>` template instances are a separate syntax proposal.

---

## Well-Defined Objects

Before Litex tries to prove a fact, it checks that every object in that fact is
meaningful in the current context. A well-definedness failure is an `error`,
not an `unknown` theorem.

### Domain obligations

Function definitions are checked under the parameter types and domain facts
written in their signature.

```litex
have fn reciprocal(x R: x != 0) R = 1 / x
have fn root(x R: 0 <= x) R = sqrt(x)

reciprocal(2) = 1 / 2
sqrt(4) = 2
root(4) = 2
```

The same expressions fail when their obligations are absent:

```text
have x R
1 / x = 1
sqrt(x) = 0
```

Both factual lines produce `error`: the first lacks `x != 0`; the second lacks
`0 <= x`.

### Ordered assumptions during well-definedness

The premises of a `forall` and the facts in an `exist` body are checked
from left to right in their temporary binder scope. After one fact is known to
be well-defined, Litex records it there as an assumption and runs its sound
inference. A positive concrete predicate may therefore expose its definition,
including a universal clause needed by a later object obligation.

```litex
prop nonzero_on(E power_set(R), g fn(x E) R):
    forall x E:
        g(x) != 0

forall E power_set(R), f, g fn(x E) R:
    $nonzero_on(E, g)
    =>:
        fn(x E) R {f(x) / g(x)} $in fn(x E) R
```

Here the checked predicate premise exposes `forall x E: g(x) != 0`, so the
anonymous function body is meaningful throughout `E`. This is scoped
definition use, not unrestricted proof search: recursion guards still apply,
an `abstract_prop` has no body to expose, and omitting the predicate premise
still leaves the division ill-defined. The temporary assumptions and inferred
facts do not escape the quantified or existential check.

The equivalent facts in a `struct` `<=>:` block are also checked from left to
right in a temporary field scope. Each successful fact is staged without
definition inference before the next fact is checked. This lets a filter guard
justify a later partial expression, both when the struct is declared and when
an instantiated struct carrier is checked:

```litex
struct NonzeroRealView:
    value R
    <=>:
        value != 0
        1 / value = 1 / value
```

Source order is significant: omitting `value != 0`, or placing it after the
reciprocal, leaves the reciprocal ill-defined. These temporary filter facts do
not escape the struct check and are not proved merely by appearing in the
definition.

### Main object criteria

Every row also requires its subobjects to be well-defined.

| Object | Required information |
|---|---|
| A name | The name is builtin, locally introduced, or imported. |
| `a + b`, `a - b`, `a * b` | `a, b $in C`. |
| `a / b` | `a, b $in C` and `b != 0`. |
| `abs(a)` | `a $in R`; use complex modulus for a general `C` argument. |
| `a % b` | `a, b $in Z` and `b != 0`. |
| `a^b` | One of Litex's supported real/integer power-domain combinations holds. |
| `sqrt(a)` | `a $in R` and `0 <= a`. |
| `log(base, a)` | Real arguments, `base > 0`, `a > 0`, and `base != 1`. |
| `lcm(a, b)` | `a, b $in Z`. |
| `floor(a)`, `ceil(a)` | `a $in R`. |
| `min(a, b)`, `max(a, b)` | `a, b $in R`. |
| `exp(a)` | `a $in R`. |
| `ln(a)` | `a $in R` and `a > 0`. |
| `sign(a)` | `a $in R`. |
| `factorial(n)` | `n $in N`. |
| `finite_set_size(S)` | `S` is finite. |
| `finite_set_max(S)`, `finite_set_min(S)` | `S` is finite, nonempty, and real-valued. |
| A set operation | Its operands have the required set or family-of-sets shape. |
| A set comprehension | The base is a set and every filter fact is well-defined. |
| `replacement(P, A)` | `A` is a set and `P` gives a unique output for each input used. |
| `general_cart(I, S, g)` | `I` is a set, `S` is nonempty, and `g $in fn(alpha I) S`; factor nonemptiness is needed for nonemptiness. |
| `fn(...) T` | Parameter domains, conditions, and return set `T` are well-defined. |
| `fn(...) T {body}` | The function-space conditions hold, `body` is well-defined under them, and `body $in T` is provable there. |
| `f(args)` | `f` has a known function set and the arguments satisfy all domains. |
| `fn_range(f)` | `f` has a known function set. |
| Tuple or product projection | The product shape, dimension, and index are valid. |
| Sequence or matrix access | The index lies in the declared bounds. |
| A finite sum or product | The index domain is suitable, the unary iterand is defined throughout it, and its declared return set is a subset of `C`. |
| A real interval | Finite endpoints are real; reversed endpoints denote an empty interval rather than an ill-defined object. |
| `&Struct<args>` or field access | The struct, arguments, field, and membership obligations check. |
| `unfold value` in an argument list | The value has a compile-time tuple arity or an explicit/default struct view; every expanded argument then passes its ordinary checks. |
| `\Template<args>` | The template exists and its parameter obligations check. |

After `fn(...) T {body}` has passed these checks, Litex can prove that it
belongs to an alpha-equivalent `fn(...) T` directly from the matching
signature. That membership rule relies on the already-checked obligation
`body $in T`; signature matching does not bypass return-value checking.

### Introducing an object is also checked

`have x S` requires Litex to know that `S` is nonempty. It is not a way to
manufacture an element of an arbitrary set.

```litex
have A nonempty_set
have x A

x $in A
```

```text
have A set
have x A
```

The second line is an `error` unless nonemptiness of `A` is available.

---

## Factual Statements

A **fact** is a proposition Litex can try to verify. A top-level accepted fact
is stored in the current context; a fact nested inside a quantifier or proof
block follows that form's scope.

### Atomic facts

An atomic fact applies one builtin relation or named predicate to objects.

```litex
2 + 3 = 5
2 < 3
2 $in {1, 2, 3}
not 4 $in {1, 2, 3}
$prime(97)
not $prime(0)
not $prime(1)
```

`$prime(p)` is a native predicate on `N`. It is false at `0` and `1`;
concrete natural literals that fit in `u64` are decided exactly, while larger
literals are left to proof rather than guessed. `by def $prime(p)` exposes the
symbolic trial-divisor contract (`2 <= p` and no divisor in `range(2, p)`). An
arbitrary integer or real argument is still rejected unless its membership in
`N` is known.

An object expression alone is not a fact:

```text
2 + 3
```

As a top-level statement this is a parse `error`; add a relation such as
`2 + 3 = 5`, or use `eval 2 + 3` when evaluation is the goal.

### Conjunctions, chains, and disjunctions

Use `and` for a conjunction on one line, adjacent binary relations for a
chain, and `or` for alternatives.

```litex
1 < 2 and 2 < 3
1 <= 2 = 2 < 3
1 < 2 or 1 >= 2
```

The fact grammar has a deliberate canonical hierarchy rather than arbitrary
recursive nesting. A conjunction is a flat list of atomic facts. A disjunction
is the outer layer, and each of its branches is one atomic fact, one relation
chain, or one flat conjunction. Thus the grammar/AST layer for `or` sits above
the `and` layer; in the usual operator-binding terminology, `and` binds more
tightly than `or`.

For example:

```text
$p(a) and $q(a) or $t(a)
```

has two `or` branches: `($p(a) and $q(a))` and `$t(a)`. It is not read as
`$p(a) and ($q(a) or $t(a))`. Allowing an `or` branch to be a completed
conjunction preserves this fixed hierarchy; it does not make `and` or `or`
arbitrarily nestable.

Verification of an `or` proves that at least one branch holds; it does not add
an arbitrary branch as a known fact.

```text
have x R
x = 0 or x != 0
x = 0
```

The disjunction is true, but the last line remains `unknown`.

### Existential facts

`exist` states existence, `exist!` states unique existence, and `not exist`
states non-existence. Witness variables are local to the fact.

```litex
witness exist x R st {x^2 = 4} from 2:
    2^2 = 4

exist! x R st {x = 0}

by contra:
    ? not exist x R st {x != x}
    obtain x from exist x R st {x != x}
    impossible x != x
```

Knowing an existential does not put its bound name in the outer context:

```text
exist x R st {x = 1}
x = 1
```

The second line is an `error` because the existential `x` is out of scope. Use
`obtain` to introduce a fresh witness name.

Existential bodies may contain atomic facts, conjunctions, chains,
disjunctions, and compact `forall` conditions. Braces delimit the body:

```litex
forall:
    exist f fn(x R) R st {forall x R => {f(x) = x}}
    =>:
        exist f fn(x R) R st {forall x R => {f(x) = x}}
```

### Universal facts

`forall` introduces arbitrary parameters, optional assumptions, and
conclusions. With no assumptions, write conclusions directly rather than an
empty `=>:` block.

```litex
forall x R:
    x^2 >= 0

forall x R:
    x = 2
    =>:
        x + 1 = 3
```

As a preview convenience, the sole direct conclusion of a positive `forall`
may itself be a `forall`. Litex combines the parameters and assumptions before
well-definedness, verification, and storage:

```litex
forall x R:
    x > 0
    =>:
        forall y R:
            y > 0
            =>:
                x + y > 0
```

The stored rule is the flat fact
`forall x R, y R: x > 0; y > 0 => x + y > 0`. The nested universal must be the
only fact in its direct conclusion block; mixing it with a sibling conclusion
is an `error`. This normalization does not apply to a universal premise, to
`not forall`, or to either side of `forall ... <=>:`.

An assumption is local; it does not become a global fact:

```text
forall x R:
    x = 2
    =>:
        x + 1 = 3

x = 2
```

The last line is an `error` because the bound `x` no longer exists.

#### Named universal settings

`setting` gives a name to a parameter prefix and its shared assumptions. It is
useful when a chapter repeatedly quantifies over the same mathematical
objects:

```litex
setting EqualPair:
    X nonempty_set
    x, y X
    x = y

forall [EqualPair], z X:
    z = z

forall [EqualPair] => {x = y}
```

This elaborates to the ordinary fact:

```litex
forall X nonempty_set, x, y X, z X:
    x = y
    =>:
        z = z
```

Parameter lines must precede shared-assumption lines in a `setting`. The
setting does not introduce global objects and does not assert its assumptions;
it only abbreviates the corresponding `forall` prefix. Every use allocates
fresh binders, even when the same setting is used several times. Extra
parameters require a comma after the closing bracket.

Settings are supported in block `forall [Name]` headers and in the inline form
`forall [Name] => {...}`. The inline form uses exactly the parameters and
shared assumptions stored by the setting; add extra parameters with block
syntax. Goal and negated universal positions use the same expansion paths. A
module-qualified setting may be referenced as `forall [Module::Name]:` or
`forall [Module::Name] => {...}`. Settings do not expand in definition
headers, template headers, or object expressions.

Inside braced fact bodies, `forall` is forced into its one-line form because
that syntactic position cannot own an indented body:

```litex
forall x R => {x = x}
```

### Universal equivalence and negated universals

`forall ... <=>:` stores both directions of an equivalence. The left side is
introduced after `=>:` even when it has no shared assumptions.

Well-definedness is checked separately for the two generated universal
directions. Each check receives the shared assumptions and its own antecedent,
but it cannot borrow a side condition from the opposite side. Put any side
condition needed to make both directions meaningful before `=>:` as a shared
assumption.

```litex
forall x, y R:
    =>:
        x = y
    <=>:
        y = x
```

`not forall` negates a universal claim:

```litex
by contra:
    ? not forall x R:
        x > 0
    impossible 0 > 0
```

Do not replace `not forall` with an unsupported prefix on a block:

```text
not:
    forall x R:
        x > 0
```

This is a parse `error`; write `not forall ...` on one header.

### Fact-shape summary

| Shape | Syntax |
|---|---|
| Atomic | `a = b`, `a $in A`, `$P(a)` |
| Flat conjunction | `atomic and atomic` |
| Chain | `a <= b = c < d` |
| Outer disjunction | `(atomic, chain, or flat-conjunction branch) or branch` |
| Existence | `exist params st {facts}` |
| Unique existence | `exist! params st {facts}` |
| Non-existence | `not exist params st {facts}` |
| Universal implication | `forall params: assumptions =>: conclusions` |
| Nested universal conclusion (preview; flattened before storage) | `forall outer: assumptions =>: forall inner: assumptions =>: conclusions` |
| Universal equivalence | `forall params: =>: left <=>: right` |
| Inline universal | `forall params => {facts}` |
| Negated universal | `not forall params: facts` |
| Inline negated universal | `not forall params => {facts}` |

---

## Builtin Predicates

Builtin predicates have parser, well-definedness, verifier, or inference
support. User-defined predicates use the same fact syntax but obtain their
meaning from `prop`, `abstract_prop`, known facts, or named interfaces.

### Equality, order, membership, and set predicates

```litex
$is_set({1, 2})
$is_nonempty_set({1})
$is_finite_set({1, 2})

1 $in {1, 2}
by def {1} $subset {1, 2}
by def {1, 2} $superset {1}
```

| Positive form | Negative form | Meaning |
|---|---|---|
| `a = b` | `a != b` | Equality |
| `a < b`, `a > b` | `not a < b`, `not a > b` | Strict order |
| `a <= b`, `a >= b` | `not a <= b`, `not a >= b` | Weak order |
| `$is_set(A)` | `not $is_set(A)` | Set shape |
| `$is_nonempty_set(A)` | `not $is_nonempty_set(A)` | Nonemptiness |
| `$is_finite_set(A)` | `not $is_finite_set(A)` | Finiteness |
| `x $in A` | `not x $in A` | Membership |
| `$is_cart(c)` | `not $is_cart(c)` | Cartesian-product shape |
| `$is_tuple(t)` | `not $is_tuple(t)` | Tuple shape |
| `A $subset B` | `not A $subset B` | Subset relation |
| `A $superset B` | `not A $superset B` | Superset relation |
| `A $proper_subset B` | `not A $proper_subset B` | Proper subset relation |
| `A $proper_superset B` | `not A $proper_superset B` | Proper superset relation |

Negated set relations do not automatically select a witness or a disjunct:

```text
have A, B set
not A $subset B
have x A
not x $in B
```

Even if the first fact were available, the last two lines do not follow for an
arbitrary `x`; a counterexample witness must be obtained through an applicable
fact or theorem.

### Function predicates

`$fn_eq_in(f, g, S)` means pointwise equality on `S`. `$fn_eq(f, g)` means
global equality after compatible function-space information is checked.

```litex
have fn f(x R) R = x
have fn g(x R) R = x

by def $fn_eq_in(f, g, R)
by def $fn_eq(f, g)
```

Once a verified `$fn_eq(f, g)` is stored, forward inference also stores the
ordinary equality `f = g`. Normal known-equality congruence can therefore reuse
it inside a larger object, such as `power_set(f) = power_set(g)`. The local
predicate `$fn_eq_in(f, g, S)` does not imply global equality.

For named functions with alpha-equivalent declared function carriers, a bare
`$fn_eq(f, g)` can also consume the exact already-known pointwise `forall`
directly. It does not synthesize pointwise equalities or bridge different
domain or return carriers.

Mapping predicates describe standard function properties:

| Form | Meaning |
|---|---|
| `$fn_eq_in(f, g, S)` | `f` and `g` agree on `S` |
| `$fn_eq(f, g)` | Globally equal compatible functions |
| `$injective(A, B, f)` | `f : A -> B` is injective |
| `$surjective(A, B, f)` | `f : A -> B` is surjective |
| `$bijective(A, B, f)` | `f : A -> B` is bijective |

Function equality needs a compatible function interface, not merely two
objects with the same value at one point:

```text
have f, g set
f(0) = g(0)
$fn_eq(f, g)
```

This produces `error` before equality verification because `f` and `g` do not
have known function sets.

### User-defined predicates

`prop` gives a predicate a concrete definition. `abstract_prop` declares only
its name and parameter shape.

```litex
prop is_zero(x R):
    x = 0

by def $is_zero(0)
```

```text
abstract_prop prime(n)
$prime(17)
```

The second line is `unknown`: declaring an abstract predicate does not prove
any instance.

---

## Statements

A **statement** is a top-level or block-level action. It may verify a fact,
introduce a name, store a definition, open a proof context, or control the
runtime. This section gives each statement family one canonical home.

### Bare facts and `have`

Write a fact directly when it should follow from the current context. Use
`have` to introduce a fresh object, optionally with a value or local witness
conditions.

```litex
have x R = 2
have y R:
    y > x

x + 1 = 3
y > 2
```

Common binder forms are:

| Form | Effect |
|---|---|
| `let x = value` | Preview: introduce `x` without declaring a set or type, then store `x = value`. |
| `have x S` | Introduce `x $in S`; `S` must be nonempty. |
| `have x S = value` | Introduce `x`, its membership, and its defining equality. |
| `have x S:` followed by facts | Introduce a witness satisfying a supported body. |
| `have A set` | Introduce a set. |
| `have A nonempty_set` | Introduce a nonempty set. |
| `have A finite_set` | Introduce a finite set. |

`let` is the minimal form for naming an already well-defined object:

```litex
let x = 1
x = 1
```

Litex checks the right side before committing the new name, then records the
ordinary equality `x = value`. The declaration itself does not require or
create a declared type or membership fact. It accepts exactly one fresh name
and one value: `let x = x` fails when there was no earlier `x`, and multiple
bindings, destructuring, recursive definitions, and template-body `let` forms
are not part of this preview. The word `let` is reserved and cannot be reused
as an identifier.

If a later application uses a `let` name, callable well-definedness first
looks for a signature registered directly on that name. If none exists, it may
reuse the signature of an object in the name's already stored equality class.
For example, after `let g = f`, a checked signature and definition for `f` can
justify `g(a)` and one checked unfolding of that application. This fallback
does not prove a new equality, instantiate a `forall`, or skip the original
function's arity, domain, or side-condition checks.

The words `set`, `nonempty_set`, and `finite_set` are binder kinds, not one
ordinary set containing all sets. They cannot be used as function input sets:

```text
have fn identity_set(A set) set = A
```

This is an `error`. Use a `template<A set>` when the definition itself is
parameterized by an arbitrary set.

### Predicate and struct definitions

`prop` defines a predicate by its conditions. `abstract_prop` declares an
uninterpreted predicate interface. `struct` defines a named product view with
fields and optional membership filters.

```litex
prop is_origin(x, y R):
    x = 0
    y = 0

struct Point:
    x R
    y R

by def $is_origin(0, 0)
by thm struct_member((0, 0), &Point)
```

An abstract declaration adds no instances:

```text
abstract_prop connected(x, y)
$connected(1, 2)
```

The call is `unknown` until a fact, theorem, definition, or explicit assumption
supports it.

### Constants and symbolic indexed data

Use dedicated `have` forms when a tuple, Cartesian product, sequence, or matrix
has a symbolic dimension or coordinate formula.

```litex
have n N+ = 3
have tuple t for i1 <= n, t[i1] = i1
have cart c for i1 <= n, proj(c, i1) = R

have finite_seq s finite_seq(N+, n) for i1 <= n, s(i1) = i1
have matrix M matrix(N+, 2, n) for i1 <= 2, j <= n, M(i1, j) = j

t[2] = 2
s(3) = 3
M(2, 3) = 3
```

| Statement | Purpose |
|---|---|
| `have tuple t for i1 <= n, t[i1] = expr` | Symbolic tuple coordinates |
| `have cart c for i1 <= n, proj(c, i1) = expr` | Symbolic product factors |
| `have seq s seq(S) for i1, s(i1) = expr` | Infinite sequence entries |
| `have finite_seq s finite_seq(S, n) for i1 <= n, ...` | Finite sequence entries |
| `have matrix M matrix(S, r, c) for i1 <= r, j <= c, ...` | Matrix entries |

The declared bounds and object type must agree:

```text
have matrix M matrix(Z, 2, 3) for i1 <= 3, j <= 2, M(i1, j) = 0
```

This is an `error`; the row and column bounds are reversed.

### Functions from an expression or cases

Use `have fn ... = ...` for one formula and `have fn ... by cases` for a
piecewise definition. Case conditions must cover the domain and be mutually
exclusive; their order does not create priority.

```litex
have fn successor(x Z) Z = x + 1

have fn sign_value(x R) Z by cases:
    case x > 0: 1
    case x = 0: 0
    case x < 0: -1

successor(2) = 3
sign_value(-2) = -1
```

Overlapping conditions are rejected:

```text
have fn bad(x R) R by cases:
    case x = 0: 0
    case x != 0: 1
    case x > 0: 2
```

This is an `error`: `x != 0` and `x > 0` overlap.

### Functions from unique existence

`have fn name by exist!` turns a proved unique-existence statement into a
function. The proof must establish both existence and uniqueness.
Inside a template, the proof may use local `obtain` and `witness` statements;
materializing the template substitutes the template arguments through those
local proof statements before committing the selected function. Local
`have candidate T = value`, `have fn ... = ...`, `have fn ... by cases`,
`by cases`, and `by extension` steps are materialized in the same way. This
permits a selected function to be built from a local object or piecewise
function candidate and proved unique by extensionality. If the selected return
carrier is itself a refined function space, the materialized result remains
callable.

```litex
have fn identity_choice by exist!:
    ? forall x R:
        exist! y R st {y = x}
    witness exist! y R st {y = x} from x:
        claim:
            ? forall y1, y2 R:
                y1 = x
                y2 = x
                =>:
                    y1 = y2
            y1 = x = y2

forall x R:
    identity_choice(x) = x
```

Giving a witness without uniqueness is insufficient:

```text
have fn choose_square_root by exist!:
    ? forall x R:
        x >= 0
        =>:
            exist! y R st {y^2 = x}
    witness exist y R st {y^2 = x} from sqrt(x)
```

This is an `error`: the goal asks for `exist!`, and the displayed body neither
uses `witness exist!` nor proves uniqueness. The mathematical statement is
also false without selecting a sign.

### Recursive functions by an integer measure

`have fn ... by induc measure from lower` defines a recursive function. Litex
checks that the measure and lower bound are integers, recursive calls stay in
the domain, and each recursive measure is smaller but not below the bound.

```litex
have fn countdown(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: countdown(n - 1)

forall n N:
    countdown(n) $in N
```

A merely decreasing real measure is not accepted:

```text
have fn dense(x R+) N by induc x from 0:
    case x <= 1: 0
    case x > 1: dense(x / 2)
```

This is an `error` because the induction measure must be integer-valued.

### Templates

`template<params>:` checks one supported definition statement in a
parameterized context and stores a reusable family. Use `\name<args>` to
materialize it. The complete instance example is in
[Template instances](#template-instances).

```litex
template<S set, z S>:
    have fn const_on_S(x S) S = z

\const_on_S<R, 0>(2) = 0
```

The template body defines exactly one object or function:

```text
template<S set>:
    have A set = S
    have B set = S
```

This is a parse `error` because a template definition expects one body
statement and one family name.

### Executable implementations and `eval`

`have algo for f(args)` attaches an executable presentation to an already
declared function. `eval expr` evaluates supported concrete expressions using
exact symbolic arithmetic.

```litex
have fn parity_value(n Z) Z by cases:
    case n % 2 = 0: 0
    case n % 2 != 0: 1

have algo for parity_value(n):
    case n % 2 = 0: 0
    case n % 2 != 0: 1

eval parity_value(4)
parity_value(4) = 0
```

An implementation must match the mathematical function facts:

```text
have fn f(x R) R = x
have algo for f(x):
    x + 1
```

This is an `error`; the implementation does not agree with the declared
function.

### Local proof blocks: `claim`, `sketch`, and `try`

`claim` proves one target and commits that target to the surrounding context.
Temporary proof steps remain local. `sketch` checks a local block and commits
nothing. `try` checks a candidate block atomically and commits it only if every
step succeeds.

```litex
claim:
    ? forall x R:
        x = 2
        =>:
            (x + 1)^2 = 9
    x + 1 = 3
    (x + 1)^2 = 9

try:
    have x R = 1
    x + 1 = 2

x = 1
```

`? fact` is an internal proof target, not a top-level assertion:

```text
? 1 = 1
```

This is a parse `error`. Put the target under `claim`, `thm`, `strategy`, or a
statement that explicitly expects a goal.

### Named interfaces: `thm`, `axiom`, and `by thm`

`thm` proves and names a reusable fact. A universal theorem is available both
for explicit `by thm` calls and ordinary known-`forall` matching. `axiom` gives
the same named interface to a trusted fact without proving it.

```litex
thm positive_is_nonzero:
    ? forall x R:
        x > 0
        =>:
            x != 0
    x != 0

by thm positive_is_nonzero(1)
```

The preview selection form keeps the ordinary theorem application explicit but
commits only one requested atomic consequence. It accepts either the inline
arrow or the uniform bodyless goal-block spelling:

```litex
thm expose_zero_sides:
    ? forall x R:
        x + 0 = x
        0 + x = x
    x + 0 = x
    0 + x = x

by thm expose_zero_sides(2) => 2 + 0 = 0 + 2

by thm expose_zero_sides(2):
    ? 2 + 0 = 0 + 2
```

For `by thm name(args) => fact`, or its `:` plus one `? fact` equivalent,
`fact` must already be well-defined in the parent context. Litex then applies
the theorem with the existing `by thm` semantics in a temporary child
environment, so all instantiated conclusions and their ordinary inferred
consequences are available while the full atomic verifier checks `fact`. The
child is discarded afterward. On success, only `fact` is committed as the
parent seed and ordinary inference runs from that seed; on failure, the parent
environment is unchanged. The target may be a positive or negative atomic fact
and need not be a direct theorem conclusion, but compound, quantified,
existential, disjunctive, conjunctive, and chain targets are not accepted. The
goal-block form is intentionally bodyless: it accepts no proof statements after
the single atomic goal.

Detailed output uses `"mode": "select_atomic_fact"`, reports the scoped
conclusions as `temporary_then_facts`, records `target_check`, and separates
the committed `parent_stored_facts`. The legacy call without `=>` remains
`"mode": "release_all"` and stores every instantiated conclusion as before.

There is no separate `lemma` keyword in the current parser:

```text
lemma self_equal:
    ? forall x R:
        x = x
```

This is a parse `error`; use `thm`.

### Explicit assumptions: `trust`, `trust have`, and `axiom`

Use trust forms only when an assumption or proof-debt boundary is intentional
and visible.

```litex
abstract_prop background(x)

axiom background_at_zero:
    ? forall x R:
        x = 0
        =>:
            $background(x)

trust have a R:
    a = 0

$background(a)
```

Each `trust` or `trust have` statement commits atomically. Litex stages its
bindings, assumed facts, and inferred consequences in a temporary child
environment. Facts later in the same statement may use facts staged earlier
in that child, but the parent environment receives the complete child only
after every fact succeeds. If any binding, well-definedness check, storage
step, or inference fails, none of that statement's effects escape.

This is a statement boundary, not a process boundary. A persistent REPL may
continue after the error with its parent environment unchanged, while an
earlier, separately successful `trust` statement remains committed. Audit
summaries and graphs count only committed trust statements and their effects;
the failed attempt remains visible in its error object.

Do not use `trust` to make an ordinary worked example appear complete:

```text
trust 1 = 2
```

The statement succeeds only by assumption injection. It should be reported as
trusted background or proof debt, never as a checked proof of the conclusion.

### Strategies

A `strategy` proves and registers a restricted atomic proof pattern. It is
enabled when defined; `use strategy` enables it again and `stop strategy`
disables strategy search. The proved universal fact remains available for
ordinary matching.

```litex
prop is_one(x R):
    x = 1

strategy use_is_one:
    ? forall x R:
        x = 1
        =>:
            $is_one(x)
    x = 1
    by def $is_one(x)

$is_one(1)
stop strategy use_is_one
use strategy use_is_one
```

Activate a strategy with `use strategy name`.

### Modules and manifests (preview)

A maintained project is an ordered module tree. Each participating directory
has one `litex.config` and declares either a top-level `module` or an exported
`submodule`.

```ini
[hierarchy]
module

[import]
Algebra = "../Algebra"

[import std]
basics

[export]
chap1 = "./chapter01.lit"
Part2 = "./Part2"
chap3 = "./chapter03.lit"
```

Important rules:

1. `[export]` is ordered and each entry names one direct `.lit` file or one
   configured child directory.
2. Direct child `.lit` files and configured submodule directories appear once;
   Markdown and other non-Litex sidecars are not exports.
3. Only a `module` imports. `[import]` mounts another module; `[import std]`
   mounts an installed standard package.
4. An optional module-only `[module] flatten = true` removes one file namespace
   layer and requires exactly one `.lit` export.
5. Canonical names follow the mounted module and export path, for example
   `Algebra::chapter::name`.

Source-level `import "../Algebra" as Algebra` and `import std basics` are
available only in an isolated source session. Repository module sources use
their manifest; dynamic imports there are rejected.

```text
[hierarchy]
submodule

[import std]
basics
```

This manifest is invalid because a `submodule` cannot declare imports.

Execution commands:

| Command | Behavior |
|---|---|
| `litex` | Start an isolated REPL. |
| `litex -r path/to/module` | Run the selected module or submodule export tree. |
| `litex -f path/to/file.lit` | Run the project prefix ending at an exported file. |
| `litex -isolated -f path/to/file.lit` | Run one file outside project discovery, then keep an isolated session. |
| `litex -session` | Use the persistent session protocol. |
| `litex -session -f path/to/file.lit` | Load the project prefix through one file, then continue in the same persistent session Runtime. |
| `litex -session -before path/to/file.lit` | Load the project prefix before one registered file, then continue in that file's environment without executing its current contents. |
| `litex -strict ...` | Verify imports and trusted project prefix sources; reject user trust forms. |
| `litex -f path/to/file.lit -trust-before-line X` | Preview: trust target-file top-level statements before the exact header line `X`, then verify normally from `X`. |
| `litex -compact`, `litex -detail` | Select compact or detailed output. |
| `litex -lang <code>` | Select a supported output language. |

`-trust-before-line` is a development-only direct-file shortcut. `X` must be
the exact one-based physical line of a top-level statement header; nested
proof lines and lines inside a statement are not valid boundaries. The prefix
is still parsed and registered, but its well-definedness and proofs are
trusted. Prefix statements report `verification_status: trusted_prefix`, while
normally checked suffix statements report `verification_status: verified`.
The runtime does not propagate trust metadata from the prefix into suffix
results. It cannot be combined with `-strict` or used with repository,
session, runner, graph, Python, or LaTeX commands.

### Utility statements

| Statement | Purpose |
|---|---|
| `eval expr` | Evaluate a supported object expression. |
| `do_nothing` | Explicit successful no-op inside a proof context. |
| `clear` | Reset the current user environment. |
| `impossible fact` | Close a contradiction branch by identifying the impossible fact. |

```litex
eval (1 + 2)^2

sketch:
    do_nothing
```

`do_nothing` does not prove an unsolved goal:

```text
claim:
    ? 1 = 2
    do_nothing
```

The claim is `unknown` because the target was never established.

### Statement index

| Family | Public forms |
|---|---|
| Facts and binders | bare fact; `let`; `have`; `trust have`; `obtain`; `have by preimage` |
| Definitions | `prop`; `abstract_prop`; `struct`; `template`; `setting`; all `have fn` forms; symbolic tuple/cart/sequence/matrix forms |
| Proof interfaces | `claim`; `thm`; `axiom`; `by thm`; `sketch`; `try`; `trust` |
| Proof control | `witness`; `by cases`; `by contra`; `by def`; enumeration; induction; `by for`; `by extension` |
| Predicate properties | `by reflexive_prop`; `by transitive_prop`; `by symmetric_prop`; `by antisymmetric_prop` |
| Trusted previews | `by zorn_lemma`; `by axiom_of_choice`; `by regularity_axiom` |
| Strategy control | `strategy`; `use strategy`; `stop strategy` |
| Runtime | `have algo for`; `eval`; `clear`; `do_nothing`; imports in isolated sessions |

---

## Syntax Reference

This section is a navigation index. The linked section is the canonical
explanation; this index does not repeat its examples.

### Binder syntax

| Meaning | Form | Canonical section |
|---|---|---|
| Object in a set | `x S` | [Bare facts and `have`](#bare-facts-and-have) |
| Set parameter | `S set` | [Bare facts and `have`](#bare-facts-and-have) |
| Nonempty set parameter | `S nonempty_set` | [Bare facts and `have`](#bare-facts-and-have) |
| Finite set parameter | `S finite_set` | [Bare facts and `have`](#bare-facts-and-have) |
| Multiple names in one domain | `x, y R` | [Universal facts](#universal-facts) |
| Domain condition | `x R: x != 0` | [Domain obligations](#domain-obligations) |
| Parameterized definition | `template<S set, x S>:` | [Templates](#templates) |
| Named universal prefix | `setting Name: ...`, then `forall [Name], ...:` or `forall [Name] => {...}` | [Named universal settings](#named-universal-settings) |
| Struct parameter | `struct Group<S nonempty_set>:` | [Struct objects](#struct-objects-and-explicit-or-default-view-field-access-preview) |

### Object syntax index

| Family | Forms | Canonical section |
|---|---|---|
| Names and arithmetic | names, literals, `+ - * / % ^`, `abs`, `sqrt`, `log`, `gcd`, `lcm`, `floor`, `ceil`, `min`, `max`, `exp`, `ln`, `sign`, `factorial` | [Names, numbers, and arithmetic](#names-numbers-and-arithmetic) |
| Sets | standard number sets, displays, builders, union/intersection/differences, power set, replacement, general product | [Sets and set-forming objects](#sets-and-set-forming-objects) |
| Functions | `fn`, anonymous functions, application, `fn_range` | [Functions, application, and range](#functions-application-and-range) |
| Structured data | `cart`, `proj`, tuples, sequences, matrices, indexing | [Products, tuples, sequences, and matrices](#products-tuples-sequences-and-matrices) |
| Finite objects | size, extrema, sums, products, integer and real intervals | [Cardinality, finite aggregation, and intervals](#cardinality-finite-aggregation-and-intervals) |
| Named views | `&Struct<args>`, field access, `\Template<args>` | [Struct objects](#struct-objects-and-explicit-or-default-view-field-access-preview) and [Template instances](#template-instances) |

### Fact syntax index

| Family | Forms | Canonical section |
|---|---|---|
| Atomic | equality, order, membership, set relations, named predicates | [Atomic facts](#atomic-facts) |
| Compound | `and`, relation chains, `or` | [Conjunctions, chains, and disjunctions](#conjunctions-chains-and-disjunctions) |
| Existential | `exist`, `exist!`, `not exist` | [Existential facts](#existential-facts) |
| Universal | `forall`, `forall [Setting]`, `forall`, `forall ... <=>:`, `not forall` | [Universal facts](#universal-facts) |
| Function predicates | `$fn_eq_in`, `$fn_eq`, mapping properties | [Function predicates](#function-predicates) |

### Statement syntax index

| Family | Canonical section |
|---|---|
| Introductions and definitions | [Statements](#statements) |
| Witnesses and proof blocks | [Proof Process](#proof-process) |
| Modules and CLI | [Modules and manifests](#modules-and-manifests-preview) |
| Builtin proof routes | [Builtin Verification Rules](#builtin-verification-rules) |
| Consequences stored automatically | [Builtin Inference](#builtin-inference) |

### Operator and delimiter notes

- `^` binds more tightly than multiplicative operators; multiplication and
  division bind more tightly than addition and subtraction.
- `[]` is index access. Function arguments use `()`.
- `{a, b}` is a displayed set; `{x S: facts}` is a set comprehension.
- `st { ... }` delimits an existential body; `forall ... => { ... }` is the
  compact universal form inside such bodies.
- `#` starts a line comment. Indentation defines block structure.
- Matrix operators contain an apostrophe: `'+`, `'-`, `'*`, `*'`, and `'^`.

---

## Proof Process

The proof process answers one question: why may the current statement be added
to the verified context? The checker follows a small set of routes and reports
the route that succeeded or the point that failed.

For a proof route written as `by ...:` followed by one or more `?` goals, the
ordinary proof-statement list may be empty. In that case Litex installs the
route's generated assumptions, runs zero user proof statements, and immediately
performs the same final goal checks. This is not an admission: an unclosed goal
still fails. Structural declarations remain required where the method needs
them, such as `case` arms and the base/step headers of finite-set induction.
`by contra` is the sole exception to the empty-tail rule: its last statement
must always be an explicit `impossible fact`.

### The core loop

For an ordinary atomic fact, the main order is:

1. Parse the statement and check every object for well-definedness.
2. Check an already known non-`forall` atomic fact with the same predicate
   shape, using known equalities.
3. Try bounded builtin mathematical rules.
4. For an equality at outer round 0, compare matching object constructors by
   recursively proving their corresponding arguments equal.
5. At outer round 0, try the target's concrete definition with the full
   verifier.
6. Try an applicable known `forall` fact
   and verify its instantiated premises.
7. Try registered predicate properties or enabled strategies where applicable.
8. On success, store the fact and run builtin inference.

During step 1, function application uses direct callable metadata first. Only
when the callee has no direct signature does it inspect the callee's stored
equality representatives for already registered callable metadata. This is a
bounded context lookup, not an invocation of the equality verifier; truth
verification still starts only after well-definedness succeeds.

```litex
abstract_prop P(x)

forall x, y R:
    $P(x)
    x = y
    =>:
        $P(y)
```

Here the conclusion matches the known local fact `$P(x)` after equality
matching. No theorem name is required.

Matching is not arbitrary search:

```text
abstract_prop P(x, y)
trust $P(1, 1)
$P(1, 2)
```

The last fact is `unknown`; no known equality makes the second arguments match.

### Known facts, universal facts, and theorem calls

An accepted fact becomes available to later statements. A `forall` fact can be
instantiated when its parameter domains and assumptions hold. A `thm` adds the
same universal interface and also permits explicit citation.

```litex
forall x R:
    x > 0
    =>:
        x != 0

have a R = 2
a > 0
a != 0
```

Litex can also package an instantiated implication into its classical
disjunction. If `P(t) => Q(t)` is available, then
`not P(t) or Q(t)` verifies by checking `Q(t)` in the temporary `P(t)` case.
This rule does not reverse the implication.

Do not add a theorem call merely to repeat the same fact after it has already
matched:

```text
by thm positive_is_nonzero(a)
a != 0
```

The second line is usually redundant if `by thm` already stored its
conclusions. Keep an explicit restatement only when a verifier run shows that a
bridge fact is needed.

### Explicit definitions and `by def` (preview)

At the outer verification round, an ordinary positive concrete predicate may
be proved from its definition before Litex tries known `forall` facts or user
strategies. Litex instantiates the `prop`, verifies every clause with the full
verifier, and accepts the positive predicate only after all clauses succeed.
This includes packaging an exact existential clause already established by a
`witness`. Once an accepted positive predicate is stored, forward inference may
also expose its positive defining consequences; that is the other direction.

Use the canonical inline form when the proof should request and record the
definition route explicitly:

```text
by def $P(args)
```

Unlike ordinary atomic verification, explicit `by def` rechecks the definition
even if the target predicate is already known. It accepts exactly one positive
atomic target. The older `by def:` goal block remains accepted for compatibility.

`by def` also names the mathematical-definition route for these builtin
positive forms: subset, superset, proper subset, proper superset,
`$injective`, `$surjective`, `$bijective`, `$fn_eq_in`, and `$fn_eq`.

When a grouped universal law binds shared convenience variables, a conclusion
may use only some of them. Litex stores the corresponding reduced universal
rule when every omitted parameter has an independent, known-nonempty domain.
For example, a clause using only `a` and `x` inside
`forall a, b R, x, y E` becomes reusable as a rule over `a` and `x` when `E`
is nonempty. It does not make this projection across an empty or unresolved
omitted domain.

Automatic definition verification does not manufacture witnesses for
existential clauses such as basis, span, and linear combination. It can package
the predicate after the required existential fact has already been proved.

```litex
prop is_unit_pair(x, y R):
    x = 1
    y = 1

by def $is_unit_pair(1, 1)
```

`by def` requires a positive concrete `prop` call:

```text
abstract_prop P(x)
by def $P(1)
```

This is an `error` because an abstract predicate has no definition to unfold.

### Witnesses, `obtain`, and preimages

Use `witness` to prove an existential or nonempty-set goal. Use `obtain` to
name witnesses from an already known existential. Use `have by preimage` to
name a preimage from known range or replacement membership.

`obtain` exposes each direct fact in the existential body. Positive concrete
predicates among those facts may expose positive clauses through forward
inference. Conversely, already proved defining clauses may automatically close
a positive concrete predicate; use `by def` to request that route explicitly.

```litex
witness exist u R st {0 < u, u < 1} from 1 / 2:
    0 < 1 / 2
    1 / 2 < 1

obtain w from exist u R st {0 < u, u < 1}
w $in R
0 < w < 1

witness $is_nonempty_set({1, 2}) from 1:
    1 $in {1, 2}
```

The checked To-Lean subset currently lowers positive `witness exist` and
positive extraction by `obtain` or `have x T: ...`. It preserves alpha-renamed
existential citations, introduces file-scope or proof-local witness names with
ordered `Exists.choose`, and exports only the exact parameter and direct-body
facts justified by `choose_spec`. Unique/non-existence and preimage forms still
report an explicit compiler boundary.
If two distinct Litex identifiers would sanitize to the same Lean binder name,
the compiler asks for a rename rather than emitting a captured quantifier.

The witness must satisfy the displayed body:

```text
witness exist x R st {x^2 = 4} from 1:
    1 $in R
```

This proof is `unknown`: the witness membership is not enough to establish
`1^2 = 4`.

For function range membership:

```litex
sketch:
    have fn square(x R) R = x^2
    square(2) $in fn_range(square)
    have by preimage a from square(2) $in fn_range(square)
    a $in R
    square(2) = square(a)
```

For a multi-argument function, supply one fresh preimage name per parameter.
For `y $in replacement(P, A)`, the analogous `have by preimage x from ...`
introduces `x $in A` and `$P(x, y)`.

### Proof by cases

`by cases` splits a goal along an exhaustive disjunction. Each branch is
checked under its case assumption.

```litex
have fn k(x R) R by cases:
    case x = 2: 3
    case x != 2: 4

have x R

by cases:
    ? k(x) > 2
    case x = 2:
        k(x) = 3
        k(x) > 2
    case x != 2:
        k(x) = 4
        k(x) > 2
```

When a case assumption already proves every target, omit both the branch body
and its colon. The bodyless form runs zero proof statements and still performs
the ordinary branch-final checks:

```litex
by cases:
    ? 1 = 1
    case 1 = 1
    case 1 != 1:
        impossible 1 = 1
```

This shorthand is only for proof `by cases`. Function and algorithm cases
still require their return expressions.

Every branch must establish the target:

```text
have x R
x = 0 or x != 0

by cases:
    ? x > 0
    case x = 0:
        do_nothing
    case x != 0:
        do_nothing
```

This proof is `unknown`; an exhaustive split does not make the unrelated goal
`x > 0` true in either branch.

### Proof by contradiction

`by contra` assumes the opposite form of its target. `impossible fact` closes
the block when both that atomic fact and its opposite are available.

```litex
by contra:
    ? not forall x R:
        x^2 >= x
    impossible 0.5^2 >= 0.5
```

Merely writing `impossible` does not create a contradiction:

```text
by contra:
    ? not 1 = 2
    impossible 2 = 3
```

This is `unknown` because the temporary assumption concerns `1 = 2`, while the
named impossible fact `2 = 3` was never derived.

### Finite enumeration and range cases

Enumeration expands a concrete finite domain. `by closed_range as cases`
records equality cases for a known closed-range member.

```litex
have P finite_set = {1, 2, 3}

by enumerate finite_set:
    ? forall x P:
        x = 1 or x = 2 or x = 3

by enumerate finite_set forall y {1, 2, 3} => {y = 1 or y = 2 or y = 3}

have i1 closed_range(1, 3)
by closed_range as cases: i1 $in 1...3
```

The inline form is available when enumeration needs no user-written proof
statements. It accepts exactly one inline `forall` target and constructs the
same finite-set enumeration proof as the block form. If helper statements are
needed, keep the target in the indented `? forall ...` block.

Enumeration is not an unbounded decision procedure:

```text
by enumerate finite_set:
    ? forall x N:
        x = 0
```

This is an `error` because `N` is not a finite displayed domain available for
exhaustive enumeration.

The related forms are `by enumerate range` and `by enumerate closed_range`.

### Integer and finite-set induction

`by induc n from base` proves a discrete target from a base case and a
successor step. `by strong_induc` supplies the corresponding bounded universal
induction hypothesis. Structured goals use `? from`, `? induc`, and
`? strong_induc`.

```litex
abstract_prop P(n)

claim:
    ? forall n Z:
        $P(0)
        forall k Z:
            k >= 0
            $P(k)
            =>:
                $P(k + 1)
        n >= 0
        =>:
            $P(n)
    by induc n from 0:
        ? $P(n)
        ? from n = 0:
            $P(0)
        ? induc:
            $P(n + 1)
```

The induction parameter and base must have the required integer information:

```text
have x R
by induc x from 0:
    ? x = x
```

This is an `error`; an arbitrary real is not a valid discrete induction
measure.

`by induc S` also supports structural induction on finite sets. The restricted
form `by induc S in A` proves the result only for finite subsets of `A`.
Its empty-set and insertion headers remain necessary, but either branch may be
bodyless when the generated assumptions already close the target. Omit the
colon on an empty branch:

```litex
by induc P:
    ? P = P
    ? from P = {}
    ? induc x, S
```

### Bounded iteration and extensionality

`by for` is a bounded proof shell for integer ranges and supported finite
Cartesian products. `by extension` proves set equality through mutual
membership.

When the generated obligations close without helper statements, put the
complete target on the same line:

```litex
by for forall i1 range(0, 3) => {i1 < 3}
by extension {1} = {1}
```

These inline forms do not accept an indented body. Use the goal-block forms
when the proof needs additional statements:

```litex
by for:
    ? forall i1 range(0, 3) => {i1 < 3}

by extension:
    ? {1, 2} = {2, 1}
    by enumerate finite_set:
        ? forall x {1, 2}:
            x $in {2, 1}
    by enumerate finite_set:
        ? forall x {2, 1}:
            x $in {1, 2}
```

Extensionality still has to prove both membership directions:

```text
by extension:
    ? 1 = 2
```

The proof reaches `unknown` because membership in `1` and `2` does not match;
the runner reports the failed subset obligation. Use direct equality reasoning
when extensional membership is not the mathematical route.

### Registering predicate properties

The following proof forms verify and register reusable behavior for a
user-defined binary predicate:

| Form | Required mathematical shape | Later use |
|---|---|---|
| `by reflexive_prop` | `P(x, x)` | Close reflexive positive goals. |
| `by symmetric_prop` | One nontrivial argument permutation | Retry positive goals in that permutation. |
| `by transitive_prop` | `P(x, y)` and `P(y, z)` imply `P(x, z)` | Store non-adjacent chain consequences. |
| `by antisymmetric_prop` | `P(x, y)` and `P(y, x)` imply `x = y` | Close equality from both directions. |

```litex
prop same(x set, y set):
    x = y

by symmetric_prop:
    ? forall x, y set:
        $same(x, y)
        =>:
            $same(y, x)
    x = y
    y = x

forall a, b set:
    $same(a, b)
    =>:
        $same(b, a)
```

These registrations require exact predicate shapes:

```text
by symmetric_prop:
    ? forall x, y set:
        x = y
        =>:
            y = x
```

This is an `error` because the domain and conclusion must be positive calls to
the same user-defined predicate.

### Trusted preview proof steps

Three preview statements expose set-theoretic background as explicit trusted
steps:

| Form | Checked obligations | Trusted conclusion |
|---|---|---|
| `by zorn_lemma S from P` | Set, nonemptiness, order properties, chain upper bounds | Existence of a maximal element |
| `by axiom_of_choice: set S` | `S` is a set of nonempty sets | Existence of a choice function |
| `by regularity_axiom(A)` | `A` is nonempty | A member of `A` disjoint from `A` |

```litex
claim:
    ? forall S set:
        forall A S:
            $is_nonempty_set(A)
        =>:
            exist f fn(A S) big_union(S) st {forall A S => {f(A) $in A}}
    by axiom_of_choice: set S
```

These forms are not ordinary derived proofs. Their statement form and output
keep the direct boundary visible; `-strict` rejects them. Litex does not taint
later theorems or facts with transitive trust metadata.

### Reading verifier output

Normal output should identify the statement, its result, nested proof results,
and the reason a fact verified. A direct builtin route includes a rule
description; structural recursion is labeled `builtin strategy`; a theorem
route includes citation information. `-compact` reduces detail.
`-detail` retains raw phases, requirements, instantiations, and inference
effects useful for debugging.

When a result is `unknown`, read the failed node rather than adding broad
automation immediately:

| Unknown shape | Useful next question |
|---|---|
| Atomic | Is an equality, membership, sign, domain condition, or matching lemma missing? |
| Conjunction | Which component failed? |
| Chain | Which adjacent step failed? |
| Universal | Which local conclusion failed under the displayed assumptions? |
| Universal equivalence | Which direction and clause failed? |

Do not infer trust from a natural-looking success message. Inspect citations,
trusted imports, `trust` summaries, and the builtin or inference rule involved.

---

## Builtin Verification Rules

Builtin verification rules are small mathematical patterns implemented by the
checker. They close the current goal; they are different from inference, which
stores useful consequences after a statement has already been accepted.

An automatic builtin rule is deliberately one layer deep. Its premises may use
already-known non-`forall` atomic facts and deterministic computation, but may
not invoke a second builtin rule. A dedicated rule state records whether that
single direct-rule layer has already been used; there is no shared node counter
or same-family/cross-family exception.

Separate builtin strategies handle only strictly structural descent, such as
arithmetic carrier trees, additive or multiplicative sign trees, finite and
nonempty set constructors, set membership/containment constructors, and tuple
coordinates. Finite-product congruence likewise descends to one factor
equality at a fresh member of the common finite set. Every strategy layer first tries known non-`forall` facts and one
fresh direct builtin rule for each immediate child, then repeats only its own
strictly smaller structural pattern. It never enters known `forall` matching,
definitions, user strategies, or the full verifier. Detailed output preserves
the child proof tree and labels the outer route as `builtin strategy`.

Finite-endpoint nonemptiness has a direct fast path when its endpoint order is
already known or computationally decidable. When that order itself needs one
builtin step, the structural route reduces `closed_range(a, b)` to `a <= b`
and the half-open `range(a, b)` to `a < b`. For real intervals, `'[a, b]` uses
`a <= b`; any open endpoint uses `a < b`. This order fact is a strictly smaller
child, so a local stronger bound such as `2 <= n` may establish the needed
`1 <= n` or `1 < n` through one fresh direct rule. No order premise means no
positive nonemptiness result, and `range(n, n)` and `'(x, x)` remain empty.

For an ordinary atomic goal the search order is: known non-`forall` fact,
one-layer builtin rule, builtin strategy, an applicable known `forall`, then a
user-defined strategy. A multi-step semantic implication is not automatic
unless it has its own reviewed direct rule. For example, `sqrt(t) != 0` now has
the dedicated direct premise `t > 0`; the weaker `t >= 0` does not trigger it.

Not-equality symmetry is one such direct one-premise rule: an exact known
`a != b` proves `b != a`. Detailed output retains `a != b` as the checked child
of `not-equality symmetry`; with neither orientation known, the rule remains
`unknown`.

Direct rules may package a fixed elementary implication when all of their
premises are already known. In particular, `n $in N` together with `n > 0`
proves `n - 1 $in N`. This lets a recursive `have fn` over `N` call itself at
`n - 1` inside its positive branch without adding a source-level carrier lemma.
An already positive-natural `n $in N+` also directly proves `n - 1 $in N`.
The parallel strict-positive result uses the stronger bound `n > 1` to prove
`n - 1 $in N+`.

Several definition-facing strategies are intentionally one layer deep. A
literal tuple can be checked as a dependent struct constructor field by field,
and a callable struct field can project through one checked tuple/function or
template constructor. Membership in a literal set builder, in a set builder
returned by one checked function/template application, or in a named set with
one exact indexed set-builder equality unfolds only that one definition and
verifies its base carrier plus atomic predicate obligations. The exact index
avoids an environment-wide named-definition scan.

Integer discreteness includes both singleton endpoint orientations. For known
integers, `n <= x` with `x < n + 1` proves `x = n`, while `n < x` with
`x <= n + 1` proves `x = n + 1`. Both bounds are required.

An exact known pointwise `forall` can package `$fn_eq(f, g)` when the declared
function carriers are alpha-equivalent. This route does not reconstruct
dependent mutual membership and does not apply across mismatched carriers.
After the resulting `$fn_eq(f, g)` is stored, inference materializes `f = g` in
the ordinary known-equality class; equality verification does not separately
scan for `$fn_eq` facts.

At outer round 0, checked-definition equality replay considers the original
objects together with every available representative from their stored
equality classes. For each representative pair it may unfold one checked outer
definition on either side. Each comparison has at most one unfolded side; it
never compares two freshly unfolded results or unfolds another definition at a
child. When the unfolded result and the other representative have the same
supported constructor, the central constructor matcher compares them
componentwise. Each comparison node first tries syntactic identity (including
binder alpha-equivalence where applicable), an already stored non-forall
equality class, pure numeric computation, bounded obligation-free rational
expression normalization, capture-avoiding beta reduction of one complete
anonymous-function application layer, and constructor descent. Extra curried
application layers are preserved when the substituted result is callable. The
normalization and beta-reduction matchers are terminating and create no proof
obligations; they handle shapes such as `a * t + 0 = a * t` and expose
`fn(x R) R {f(x) * g(x)}(a)` as `f(a) * g(a)` without opening the ordinary
builtin dispatcher. The replay-depth guard prevents comparison from
instantiating known `forall` facts or reopening checked-definition replay.
Consequently a representative `a * t` can prove `a * t + 0`, but a comparison
cannot silently use another mathematical builtin rule or unfold a second named
function.

For example, after the first two conclusions below have been verified and
stored, the last comparison beta-reduces both sides transiently. Multiplication
congruence then checks exactly the two stored leaf equalities; the intermediate
product equality is not added to the environment:

```litex
forall f, g fn(x R) R, a R:
    forall x R:
        f(x) = f(-x)
        g(x) = g(-x)
    =>:
        f(a) = f(-a)
        g(a) = g(-a)
        fn(x R) R {f(x) * g(x)}(a) = fn(x R) R {f(x) * g(x)}(-a)
```

Removing either stored leaf equality makes the final line unknown; beta
reduction itself does not instantiate the preceding `forall`.

The ordinary known-only equality route can still check identity, direct
lookup/calculation, and stored equality classes. Separately, the full equality
route reuses the constructor matcher while recursively allowing bounded builtin
and known-equality child proofs. Function applications align argument groups
from right to left and then compare the remaining function prefixes. Thus
several arguments may change in one equality, and
`f(a, b) = g(1, 2)(a, b)` is accepted exactly when the paired arguments and the
remaining equality `f = g(1, 2)` can be proved. A non-equality fact lookup may
transport through known-only congruence, but it does not launch the fuller
child-proof route implicitly.

For nonzero facts, a known strict premise `x > 0` proves `sqrt(x) != 0`.
Nonnegativity alone is deliberately insufficient because `sqrt(0) = 0`.

Rules that genuinely need a universal, existential, or compound premise are
called explicitly through reserved builtin theorem names. Their handlers use
the ordinary full verifier for the requirement and store the conclusion only
after it succeeds:

| Explicit call | Conclusion shape |
|---|---|
| `by thm fn_set_member(f, F)` | `f $in F` |
| `by thm set_builder_member(x, B)` | `x $in B` |
| `by thm defined_set_member(x, S)` | `x $in S` after one stored set-valued definition |
| `by thm struct_member(x, S)` | `x $in S` |
| `by thm cart_member_from_coordinates(x, C)` | `x $in C` |
| `by thm general_cart_member(x, G)` | `x $in G` |
| `by thm general_cart_nonempty_by_choice_from_family(G)` | `$is_nonempty_set(G)` |
| `by thm general_cart_nonempty_by_choice_from_pointwise(G)` | `$is_nonempty_set(G)` |
| `by thm sum_le_sum_from_pointwise(L, R)` | `L <= R` |
| `by thm finite_set_sum_le_from_pointwise(L, R)` | `L <= R` |
| `by thm finite_set_summand_le_sum(L, R)` | `L <= R` |
| `by thm tuple_equal_from_coordinates(L, R)` | `L = R` |
| `by thm finite_set_sum_substitution(L, R)` | `L = R` |
| `by thm sum_over_bijective_finite_set_enumerations(L, R)` | `L = R` |

These names are bare global reserved names. They cannot be rebound by user
objects, parameters, theorems, or axioms, and a qualified spelling is rejected.
Detailed output marks the route with `"theorem_source": "builtin_rule"`, shows
`requirement_checks`, and preserves `axiom_of_choice` provenance on the two
general-cart nonemptiness interfaces.

This section catalogues public rule families. It does not promise that every
mathematically equivalent spelling is recognized. When a goal is `unknown`,
write a smaller intermediate fact that exposes a supported shape.

### Common rule families

| Family | Typical supported work |
|---|---|
| Exact evaluation | Concrete rational arithmetic and comparisons |
| Algebraic normalization | Polynomial identities and normalized numeric expressions |
| Equality matching | Reflexivity, symmetry, transitivity, substitution, and known-value resolution |
| Order | Real signs, monotonicity, inequality combination, real powers, and real absolute values |
| Membership | Standard number sets, displayed sets, ranges, intervals, products, and function values |
| Set relations | Set shape, nonemptiness, finiteness, subset and proper subset patterns |
| Functions | Application equations, pointwise equality, global function equality, mapping properties |
| Finite aggregates | Sizes, extrema, indexed sums/products, finite-set sums/products, pointwise product distribution, and bijective reindexing |
| Modular arithmetic | Concrete remainders, congruence-preserving operations, and nested-remainder absorption when the outer modulus divides the inner modulus |
| Structured objects | Tuples, Cartesian products, sequences, matrices, structs, and templates |

```litex
2 + 3 * 4 = 14

forall a, b Q:
    a - b = 4
    a * b = 1
    =>:
        (a + b)^2 = (a - b)^2 + 4 * (a * b) = 20
```

A builtin rule is not an unrestricted solver:

```text
forall x R:
    x = 0
```

This is `unknown`; the conclusion is false for arbitrary real `x`, and no
builtin pattern closes it.

### Equality rules

Equality rules cover these main shapes:

- exact numeric evaluation and normalization;
- polynomial normalization over supported number domains;
- replacement of subexpressions by known equal values;
- reflexivity, symmetry, transitivity, and equality chains;
- function application equations and structural equality;
- standard facts for `abs`, powers, logarithms, finite aggregates, and `%`;
- equality from both weak-order directions;
- equality of materialized template values when their resolved objects agree.
- complex coordinate reconstruction and extensionality, plus the native
  imaginary-unit identities.

```litex
forall x, y R:
    x = y
    =>:
        2 * x + 1 = 2 * y + 1

forall a, b R:
    a <= b
    b <= a
    =>:
        a = b
```

Large algebraic jumps may still be `unknown`. Expose the identity and the
numeric simplifications separately:

```text
(3 - 2 * sqrt(2)) * (3 + 2 * sqrt(2)) = 1
```

If this does not close in the current context, write the checkable chain
`= 3^2 - (2 * sqrt(2))^2 = 9 - 8 = 1` and establish any missing square-root
fact first.

### Order and comparison rules

Order rules include concrete comparisons, standard bounds from numeric sets,
sign propagation through arithmetic, monotonicity, combination of
inequalities, power order on supported domains, and absolute-value bounds.
Every ordered comparison requires both operands to be real; membership in `C`
alone never supplies an order.

```litex
forall x R:
    0 <= x^2
    -x <= abs(x)
    x <= abs(x)

forall a, b, c, d R:
    a <= b
    c <= d
    =>:
        a + c <= b + d
        a - d <= b - c

forall m, n Z:
    =>:
        m <= n
    <=>:
        m < n + 1
```

The last equivalence is an integer-adjacency rule: a strict bound immediately
below the successor `n + 1` is the same as the weak bound at `n`. It requires
both compared objects to be known integers.

Sign conditions matter:

```text
forall a, b, c R:
    a < b
    =>:
        a * c < b * c
```

This is `unknown` because multiplication reverses or collapses order when the
sign of `c` is not known.

### Powers, logarithms, sums, products, and remainder

The checker recognizes standard well-defined power domains, many concrete and
symbolic power identities, logarithm laws under their domain conditions,
finite aggregate expansions, and common congruence patterns. Complex bases
support natural exponents and, when nonzero, integer exponents. Positivity,
monotonicity, roots, logarithms, and even-power absolute-value rules remain
restricted to real bases.

For positive real factors, a real exponent distributes over multiplication in
either equality direction:

```litex
forall a, b R+, x R:
    (a * b)^x = a^x * b^x
```

The positivity condition is semantic, not cosmetic: this rule does not admit
zero or negative factors with an arbitrary real exponent.

```litex
forall m Z:
    m != 0
    =>:
        0 % m = 0

forall a Z:
    a % 2 = (a % 8) % 2
```

The second fact uses `2 | 8`. In general, `(a % m) % d = a % d` is automatic
only when `a` is an integer, `m` and `d` are positive integers, and `m % d = 0`.

Domain obligations are never supplied by an algebra rule:

```text
have x R
log(1, x) = 0
```

This is an `error`: base `1` is outside the logarithm domain, and positivity of
`x` is also missing.

### Membership and type-predicate rules

Membership rules recognize standard number sets, displayed sets, set
operations, ranges, real intervals, comprehensions, products, function return
sets, and finite aggregate codomains. Type-predicate rules recognize set,
nonempty, finite, tuple, and Cartesian-product shapes.

```litex
1 $in N+
not (-1) $in N
i $in C
R $subset C

$is_set(power_set(Z))
$is_nonempty_set(power_set(Z))
$is_finite_set({1, 2})
$is_tuple((1, 2))
$is_cart(cart(R, Z))
```

A familiar name does not provide a missing shape fact:

```text
have A set
$is_finite_set(A)
```

The second line is `unknown`; arbitrary sets need not be finite.

### Inclusion and function rules

Subset verification reduces to universal membership where needed. Proper
inclusion combines ordinary inclusion with inequality. Function equality
reduces to compatible function interfaces and pointwise equality.

A membership goal may also use one directly known inclusion on demand. If
`x $in A` and either `A $subset B`, `B $superset A`, or
`A $in power_set(B)` is known, the verifier can prove `x $in B`. This lookup
does not itself store `x $in B` or traverse a second inclusion edge. Existing
universal-membership facts may still compose several ordinary proof steps.
This rule only answers membership goals; it does not rewrite an order goal
such as `0 < x` into membership in a positive-number set.

```litex
by def {1} $subset {1, 2}

forall B set, A power_set(B), x A:
    x $in B

claim:
    ? forall A, B set:
        A $subset B
        A != B
        =>:
            A $proper_subset B
            B $proper_superset A
    by def A $proper_subset B
    by def B $proper_superset A

by def $fn_eq(fn(x R) R {x}, fn(y R) R {y})
```

`$fn_eq` and `$fn_eq_in` do not have ordinary negated atomic forms. The
mapping predicates `$injective`, `$surjective`, and `$bijective` may be
negated, but the checker does not automatically search for a counterexample.

### Reduced rational fractions (preview)

Litex has a narrow builtin for the standard reduced-fraction representation of
a rational number with positive denominator.

```litex
forall a Q:
    exist! p Z, q N+ st {a = p / q, forall z N+: p % z = 0 and q % z = 0 => {z = 1}}
```

This rule recognizes the displayed representation; it is not a general gcd
construction and does not replace checked source-level arithmetic libraries.

---

## Builtin Inference

After an accepted or trusted fact is stored, builtin inference may add routine
consequences to the same environment. These consequences become ordinary
known information for later statements.

Inference can be transitive: an inferred atomic fact may in turn expose its
own routine consequences. Litex does not impose a global one-layer inference
limit. It only stops a recursive branch when it returns to the same normalized
atomic fact that is already being expanded on the current inference stack;
different newly inferred facts continue normally. This prevents a cyclic
definition graph from repeatedly reopening itself without suppressing ordinary
parameter-type or structure-field inference.

### Verification versus inference

```litex
have n N

0 <= n
```

The `have` statement stores `n $in N`; inference records the standard
nonnegativity consequence. The second line then reuses known information.

Inference does not prove an arbitrary desired consequence:

```text
have n N
n = 0
```

The equality remains `unknown`.

### Facts that trigger inference

Most triggers are atomic facts. A few larger shapes have explicit behavior.

| Stored fact | Typical inferred information |
|---|---|
| Equality | Numeric values, substitutions, simple linear values, tuple/product/function shape |
| Membership | Number-set bounds, enumeration cases, product coordinates, range/interval bounds, comprehension filters |
| Subset or superset | Universal membership consequence |
| Proper inclusion | Ordinary inclusion and set inequality |
| Order against a concrete bound | Selected sign information |
| `exist!` | Equality of any two witnesses satisfying the body |
| `not exist` | Corresponding universal negation form |
| `not forall` | Existential counterexample form |
| Equality chain | Equalities forced by transitivity |

An outer `and`, `or`, or `forall` does not receive the same general extra
inference pass merely because it was stored. Their locally processed atomic
parts may still contribute information when the relevant statement form
stores or assumes them.

### Equality and structural inference

Equality inference remembers usable values and shapes.

```litex
have x R = 2
x + 1 = 3

have t cart(R, Z) = (1, 2)
$is_tuple(t)
tuple_dim(t) = 2
```

Typical consequences include:

- `u - v = 0` gives `u = v` when meaningful;
- `$fn_eq(f, g)` gives the ordinary equality `f = g`;
- an equality to a concrete number enables later numeric substitution;
- supported simple linear equalities record a solved value;
- equality to a tuple or product records its shape and dimension;
- equality to a displayed sequence, matrix, or anonymous function records the
  corresponding structural information;
- a known concrete `prop` call may expose instantiated definition clauses.

Inference is directional bookkeeping, not a license to solve any equation:

```text
have x R
x^2 = 4
x = 2
```

The last line is `unknown`; the stored square equation has two real solutions.

### Membership inference

Membership inference exposes the ordinary information carried by a set.

```litex
have a {1, 2}
a = 1 or a = 2

have i1 Z = 3
i1 $in range(2, 6)
i1 $in Z
2 <= i1 < 6

have u cart(R, Z)
u[1] $in R
u[2] $in Z
```

Main families are:

| Membership | Inferred information |
|---|---|
| `x $in N` | `0 <= x` |
| Positive, negative, or nonzero numeric subsets | Corresponding sign or disequality |
| `x $in {a, b, ...}` | Finite equality disjunction |
| `x $in cart(A, B, ...)` | Tuple shape, dimension, and coordinate memberships |
| `x $in range(a, b)` | Integer membership and half-open bounds |
| `x $in closed_range(a, b)` | Integer membership and closed bounds |
| `x` in a real interval | Real membership and endpoint bounds |
| `x $in {y S: filters}` | `x $in S` and instantiated filters |
| Function-like type membership | Function interface and usable result information |

Membership in a broad set does not imply a narrower property:

```text
have x R
x > 0
```

The second line is `unknown`; `R` contains positive, zero, and negative values.

### Subset, superset, and order inference

```litex
by def {1} $subset {1, 2}

forall x {1}:
    x $in {1, 2}
```

Subset and superset facts retain their reusable universal-membership
interface. Separately, the membership builtin can check one known owner set
against one directly known superset when a membership goal is requested. That
direct-index check is on demand: it does not materialize the lifted membership
or compute a transitive subset closure. Other proof rules can still use its
one-step result as a requirement.

Proper subset additionally gives subset and inequality; proper superset is
dual. Negated proper relations do not select either branch of their
disjunctive meaning.

Selected comparisons with concrete bounds may produce sign facts, for example
`2 <= x` can imply `0 < x`. Do not depend on a particular inferred spelling
when a direct sign statement is important to the proof; write the sign fact
explicitly and let the verifier check it.

### Reading inference output

Detailed output may show inference under `effects` or an environment delta. A
later success can therefore depend on information not repeated in source text.
When auditing a proof, distinguish:

1. the fact the user wrote;
2. the route that verified it;
3. the consequences inference stored afterward.

This distinction is also part of the trusted boundary: builtin inference rules
are checker code, not source-level theorems silently imported from a library.

---

## Appendix

### Preview feature inventory

Preview features are public enough to test, but their syntax or semantics may
change:

- native complex scalars `C`, `C*`, `i`, `re`, `img`, and `C_abs`;
- native positive real constants `e` and `pi`;
- native symbolic real trigonometry `sin`, `cos`, `tan`, and `cot`;
- native `floor`, `ceil`, binary `min`/`max`, and integer `lcm`;
- native real `exp`/`ln`, real `sign`, and natural `factorial`;
- `struct`, struct view objects, and default-view field access;
- proper subset and proper superset relations;
- injective, surjective, and bijective mapping predicates;
- explicit `by def`;
- selected atomic consequences with `by thm name(args) => fact` or its
  bodyless `:` plus `? fact` goal-block spelling;
- untyped object definitions with `let x = value`;
- modules, manifests, flattening, and localized output;
- one-step membership verification through a known subset or superset;
- direct-file `-trust-before-line` development checks;
- reduced rational fraction verification;
- positive nested-`forall` conclusion normalization;
- trusted Zorn, choice, and regularity proof steps.

### Trust and strict mode

| Source of information | Normal run | `-strict` run |
|---|---|---|
| Checked source statement | Verified | Verified |
| `[import]`, `[import std]`, or earlier `-f` project prefix | May be loaded as reported unverified background | Verified |
| `trust` | Accepted and reported as trusted | Rejected |
| `trust have` | Accepted and reported as trusted | Rejected |
| `axiom` | Accepted and reported as trusted | Rejected |
| Trusted preview set-theoretic step | Accepted as an explicit trusted proof step | Rejected |
| `-trust-before-line` file prefix | Accepted and marked `trusted_prefix` statement by statement | Incompatible with `-strict` |

Strict mode reduces user-supplied trust; it does not turn the Litex checker and
its builtin rules into a separately verified small kernel.

### Documentation and test contract

Every `litex` fenced block in this manual is intended to be self-contained and
is run by `cargo test run_examples`. A `text` block is either a deliberately
invalid example, a non-executable shape, or an output sketch; its surrounding
paragraph states the intended reading and, for failures, whether checking
reaches `unknown` or `error`.

The language implementation is the final source of truth when this manual and
the runner disagree. Such disagreement is a documentation or diagnostic bug
to fix, not a reason to reinterpret a failed example silently.

### Bounded maximum existence and definition packaging

Litex recognizes the standard maximum-existence shape for a finite nonempty
subset of `N`. The concrete predicate must state both that the witness belongs
to the set and that every natural member is at most the witness. The rule does
not fire without finite, nonempty, and natural-carrier evidence.

When `by def` folds a concrete proposition, it first checks argument types and
exact already-known definition clauses through bounded known/builtin routes.
Only a missing clause falls back to ordinary proof search. This keeps large
contexts responsive without weakening the requirement that every concrete
definition clause be proved.
