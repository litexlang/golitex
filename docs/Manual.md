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

> **Beta notice:** Litex is still experimental. Syntax, diagnostics, builtin
> rules, and preview features may change. Do not use it for mission-critical
> proof work.

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
rationale belongs in the [FAQ](FAQ.md), [Litex Blueprint](Litex_Blueprint.md),
and [Litex and Lean](Litex_and_Lean.md).

### Trust boundary

Litex is not a replacement for Lean, Coq, or Isabelle. Its checker, builtin
objects, builtin verification and inference rules, imported assumptions, and
every explicit `trust` or `axiom` are relevant to the trusted boundary.
`trust` records an assumption; it is not a proof. The proposed compiler to Lean
is still under development, so current reliability claims must be grounded in
inspectable rules, tests, verifier output, and explicit trust reporting.

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
| `a + b`, `a - b`, `a * b`, `a / b` | Arithmetic operations |
| `a % b` | Euclidean integer remainder |
| `a^b` | Exponentiation |
| `abs(a)`, `sqrt(a)`, `log(base, a)` | Standard numeric objects |
| `sin(a)`, `cos(a)`, `tan(a)`, `cot(a)` | Native symbolic real trigonometric objects |
| `re(z)`, `img(z)`, `C_abs(z)` | Real coordinate, imaginary coordinate, and complex modulus |
| `finite_set_max(S)`, `finite_set_min(S)` | Extremum of a suitable finite set |

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
| Lean extractor | `Real.exp 1` | `Real.pi` |

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

The preview intentionally does not assign every familiar special-angle value;
for example, `sin(pi / 6) = 1 / 2` still needs an explicit source fact.
Complex trigonometry, inverse trigonometric functions, analytic definitions,
and continuity or monotonicity theorems are also outside this interface.

The names `sin`, `cos`, `tan`, and `cot` are hard-reserved. Their bare names
are not first-class function values; higher-order code can use
`fn(x R) R {sin(x)}`. LaTeX emits standard trigonometric notation. The
evaluator and current Python and Lean extractors report native trigonometric
expressions as unsupported rather than choosing a numerical or library
semantics silently.

### Complex scalars (beta preview)

`C` is the largest builtin scalar set. The standard inclusion chain is
`N` through `Z`, `Q`, and `R` into `C`. Arithmetic does not erase narrower
information: an operation whose operands are known integers or reals keeps the
existing narrow result whenever that rule applies, and falls back to `C` only
when a complex carrier is needed.

The native imaginary unit and coordinate interface are symbolic builtin
objects:

```litex
i $in C
i * i = -1
i^2 = -1
i^4 = 1
i^(-1) = -i

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

{x R: 0 <= x} $subset R
```

| Form | Meaning |
|---|---|
| `N+`, `N`, `Z`, `Q`, `R`, `C` | Standard number sets |
| `Q+`, `R+`, `Q_neg`, `Z_neg`, `R_neg` | Signed standard subsets |
| `N+`, `Z+`, `Q+`, `R+` | Preview compact spellings for the corresponding strictly positive sets; `Z+` is `N+` |
| `Z-`, `Q-`, `R-` | Preview compact spellings for the corresponding strictly negative sets |
| `Q_nz`, `Z_nz`, `R_nz` | Nonzero standard subsets |
| `{a, b, ...}` | Displayed finite set |
| `{x S: facts}` | Set comprehension over `S` |
| `union(A, B)`, `intersect(A, B)` | Binary union and intersection |
| `set_minus(A, B)`, `set_diff(A, B)` | Relative complement and symmetric difference |
| `big_union(F)`, `big_intersect(F)` | Union or intersection of a family |
| `power_set(A)` | Set of subsets of `A` |
| `replacement(P, A)` | Replacement set defined by a functional predicate `P` |
| `general_cart(I, S, g)` | Choice functions selecting one value from each factor `g(alpha)` |

The compact suffix must be adjacent to its base. Verifier output normalizes
compact numeric input back to names such as `N+` and `R_neg`.

```litex
have n N+
n $in N+
have z Z-
z $in Z_neg
```

The signs are strict: `+` means greater than zero and `-` means less than zero.
Nonzero sets keep the explicit spellings `Z_nz`, `Q_nz`, and `R_nz`; compact
`*` suffixes are not part of this preview.

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
trust forall! A S => {$is_nonempty_set(A)}
have g fn(alpha I) S

$is_nonempty_set(general_cart(I, S, g))
general_cart(I, S, g) = {f fn(t I) big_union(S): forall! alpha I => {f(alpha) $in g(alpha)}}
```

The `trust` line makes the required factor-nonemptiness background explicit;
the equality shows the canonical mathematical shape of the general product.

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

2 $in range(0, 3)
3 $in closed_range(0, 3)
1 $in '[0, 1]
```

| Form | Meaning |
|---|---|
| `finite_set_size(S)` | Cardinality of a finite set |
| `finite_set_sum(S, f)`, `finite_set_product(S, f)` | Aggregate over a finite set |
| `sum(first, last, f)`, `product(first, last, f)` | Aggregate over a closed integer index range |
| `range(a, b)` | Integers `a <= x < b` |
| `closed_range(a, b)`, `a...b` | Integers `a <= x <= b` |
| `'(a, b)`, `'(a, b]`, `'[a, b)`, `'[a, b]` | Bounded real intervals |
| `'(a,)`, `'[a,)`, `'(,b)`, `'(,b]` | Real rays |

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

```litex
struct Point:
    x R
    y R

have p &Point = (1, 2)

&Point{p}.x = 1
p.y = 2
```

If a selected field is itself declared directly with a struct type, field
notation may continue through that declared view:

```litex
struct Coordinates:
    x R
    y R

struct TaggedPoint:
    point &Coordinates
    tag N

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
p $in &Point
p.x = 1
```

The last line is a parse `error`. Bind `p &Point` or write
`&Point{p}.x` explicitly. Chained notation follows only a field declared
directly as `&Struct<...>`; it does not follow a set alias or search known
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

### Main object criteria

Every row also requires its subobjects to be well-defined.

| Object | Required information |
|---|---|
| A name | The name is builtin, locally introduced, or imported. |
| `a + b`, `a - b`, `a * b`, `abs(a)` | The relevant arguments are real. |
| `a / b` | `a, b $in R` and `b != 0`. |
| `a % b` | `a, b $in Z` and `b != 0`. |
| `a^b` | One of Litex's supported real/integer power-domain combinations holds. |
| `sqrt(a)` | `a $in R` and `0 <= a`. |
| `log(base, a)` | Real arguments, `base > 0`, `a > 0`, and `base != 1`. |
| `finite_set_size(S)` | `S` is finite. |
| `finite_set_max(S)`, `finite_set_min(S)` | `S` is finite, nonempty, and real-valued. |
| A set operation | Its operands have the required set or family-of-sets shape. |
| A set comprehension | The base is a set and every filter fact is well-defined. |
| `replacement(P, A)` | `A` is a set and `P` gives a unique output for each input used. |
| `general_cart(I, S, g)` | `I` is a set, `S` is nonempty, and `g $in fn(alpha I) S`; factor nonemptiness is needed for nonemptiness. |
| `fn(...)` | Parameter domains, conditions, and return set are well-defined. |
| `f(args)` | `f` has a known function set and the arguments satisfy all domains. |
| `fn_range(f)` | `f` has a known function set. |
| Tuple or product projection | The product shape, dimension, and index are valid. |
| Sequence or matrix access | The index lies in the declared bounds. |
| A finite sum or product | Bounds, indexed function, and numeric codomain are suitable. |
| A real interval | Finite endpoints are real and the endpoint ordering is compatible. |
| `&Struct<args>` or field access | The struct, arguments, field, and membership obligations check. |
| `\Template<args>` | The template exists and its parameter obligations check. |

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
```

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
disjunctions, and compact `forall!` conditions. Braces delimit the body:

```litex
forall:
    exist f fn(x R) R st {forall! x R => {f(x) = x}}
    =>:
        exist f fn(x R) R st {forall! x R => {f(x) = x}}
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

An assumption is local; it does not become a global fact:

```text
forall x R:
    x = 2
    =>:
        x + 1 = 3

x = 2
```

The last line is an `error` because the bound `x` no longer exists.

`forall!` is the one-line form used inside braced fact bodies:

```litex
forall! x R => {x = x}
```

### Universal equivalence and negated universals

`forall ... <=>:` stores both directions of an equivalence. The left side is
introduced after `=>:` even when it has no shared assumptions.

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
| Conjunction | `atomic and atomic` |
| Chain | `a <= b = c < d` |
| Disjunction | `branch or branch` |
| Existence | `exist params st {facts}` |
| Unique existence | `exist! params st {facts}` |
| Non-existence | `not exist params st {facts}` |
| Universal implication | `forall params: assumptions =>: conclusions` |
| Universal equivalence | `forall params: =>: left <=>: right` |
| Inline universal | `forall! params => {facts}` |
| Negated universal | `not forall params: facts` |
| Inline negated universal | `not forall! params => {facts}` |

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
{1} $subset {1, 2}
{1, 2} $superset {1}
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

$fn_eq_in(f, g, R)
$fn_eq(f, g)
```

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

$is_zero(0)
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
| `have x S` | Introduce `x $in S`; `S` must be nonempty. |
| `have x S = value` | Introduce `x`, its membership, and its defining equality. |
| `have x S:` followed by facts | Introduce a witness satisfying a supported body. |
| `have A set` | Introduce a set. |
| `have A nonempty_set` | Introduce a nonempty set. |
| `have A finite_set` | Introduce a finite set. |

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

$is_origin(0, 0)
(0, 0) $in &Point
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
    case n > 0: countdown(n - 1)

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

$is_one(1)
stop strategy use_is_one
use strategy use_is_one
```

Strategies are not invoked with `by strategy`:

```text
by strategy use_is_one
```

This is a parse `error`; activation uses `use strategy name`.

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
| Facts and binders | bare fact; `have`; `trust have`; `obtain`; `have by preimage` |
| Definitions | `prop`; `abstract_prop`; `struct`; `template`; all `have fn` forms; symbolic tuple/cart/sequence/matrix forms |
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
| Struct parameter | `struct Group<S nonempty_set>:` | [Struct objects](#struct-objects-and-explicit-or-default-view-field-access-preview) |

### Object syntax index

| Family | Forms | Canonical section |
|---|---|---|
| Names and arithmetic | names, literals, `+ - * / % ^`, `abs`, `sqrt`, `log` | [Names, numbers, and arithmetic](#names-numbers-and-arithmetic) |
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
| Universal | `forall`, `forall!`, `forall ... <=>:`, `not forall` | [Universal facts](#universal-facts) |
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
- `st { ... }` delimits an existential body; `forall! ... => { ... }` is the
  compact universal form inside such bodies.
- `#` starts a line comment. Indentation defines block structure.
- Matrix operators contain an apostrophe: `'+`, `'-`, `'*`, `*'`, and `'^`.

---

## Proof Process

The proof process answers one question: why may the current statement be added
to the verified context? The checker follows a small set of routes and reports
the route that succeeded or the point that failed.

### The core loop

For an ordinary atomic fact, the main order is:

1. Parse the statement and check every object for well-definedness.
2. Try builtin mathematical rules.
3. Try a known fact with the same predicate shape, using known equalities.
4. Try an applicable known `forall` fact and verify its instantiated premises.
5. Try registered predicate properties or enabled strategies where applicable.
6. On success, store the fact and run builtin inference.

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

Do not add a theorem call merely to repeat the same fact after it has already
matched:

```text
by thm positive_is_nonzero(a)
a != 0
```

The second line is usually redundant if `by thm` already stored its
conclusions. Keep an explicit restatement only when a verifier run shows that a
bridge fact is needed.

### Definition folding and `by def` (preview)

A concrete `prop` can normally fold and unfold through ordinary verification.
`by def $P(args)` explicitly checks every instantiated clause when the
dependency should be visible.

Automatic positive-predicate inference exposes the direct clauses of `P`.
When a direct clause is another concrete predicate, Litex stores that clause
but does not recursively unfold it in the same inference step. Use another
`by def` when the nested predicate's own clauses are needed. This keeps
existential definitions such as basis, span, and linear combination from
recursively generating fresh witnesses.

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

`obtain` exposes each direct fact in the existential body. If one of those
facts is a user-defined predicate, Litex does not recursively unfold it; use
`by def` when that predicate's own clauses are needed.

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

have i1 closed_range(1, 3)
by closed_range as cases: i1 $in 1...3
```

Enumeration is not an unbounded decision procedure:

```text
by enumerate finite_set:
    ? forall x N:
        x = 0
```

This is an `error` because `N` is not a finite displayed domain available for
exhaustive enumeration.

The related forms are `by enumerate range`, `by enumerate closed_range`, and
inline `by enumerate finite_set forall! ...`.

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

### Bounded iteration and extensionality

`by for` is a bounded proof shell for integer ranges and supported finite
Cartesian products. `by extension` proves set equality through mutual
membership.

```litex
by for forall! i1 range(0, 3) => {i1 < 3}

by extension {1, 2} = {2, 1}:
    by enumerate finite_set:
        ? forall x {1, 2}:
            x $in {2, 1}
    by enumerate finite_set:
        ? forall x {2, 1}:
            x $in {1, 2}
```

Extensionality still has to prove both membership directions:

```text
by extension 1 = 2
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
            exist f fn(A S) big_union(S) st {forall! A S => {f(A) $in A}}
    by axiom_of_choice: set S
```

These forms are not ordinary derived proofs. Their statement form and output
keep the direct boundary visible; `-strict` rejects them. Litex does not taint
later theorems or facts with transitive trust metadata.

### Reading verifier output

Normal output should identify the statement, its result, nested proof results,
and the reason a fact verified. A builtin route includes a rule description; a
theorem route includes citation information. `-compact` reduces detail.
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
| Finite aggregates | Sizes, extrema, indexed sums/products, finite-set sums/products |
| Modular arithmetic | Concrete remainders and standard congruence-preserving operations |
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
```

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

```litex
forall m Z:
    m != 0
    =>:
        0 % m = 0

```

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
{1} $subset {1, 2}

forall B set, A power_set(B), x A:
    x $in B

forall A, B set:
    A $subset B
    A != B
    =>:
        A $proper_subset B
        B $proper_superset A

$fn_eq(fn(x R) R {x}, fn(y R) R {y})
```

`$fn_eq` and `$fn_eq_in` do not have ordinary negated atomic forms. The
mapping predicates `$injective`, `$surjective`, and `$bijective` may be
negated, but the checker does not automatically search for a counterexample.

### Reduced rational fractions (preview)

Litex has a narrow builtin for the standard reduced-fraction representation of
a rational number with positive denominator.

```litex
forall a Q:
    exist! p Z, q N+ st {a = p / q, forall! z N+: p % z = 0 and q % z = 0 => {z = 1}}
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
{1} $subset {1, 2}

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

- native complex scalars `C`, `i`, `re`, `img`, and `C_abs`;
- native positive real constants `e` and `pi`;
- native symbolic real trigonometry `sin`, `cos`, `tan`, and `cot`;
- compact strict-sign suffixes such as `N+` and `R-`;
- `struct`, struct view objects, and default-view field access;
- proper subset and proper superset relations;
- injective, surjective, and bijective mapping predicates;
- explicit `by def`;
- modules, manifests, flattening, and localized output;
- one-step membership verification through a known subset or superset;
- direct-file `-trust-before-line` development checks;
- reduced rational fraction verification;
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

### Removed or unsupported spellings

| Spelling | Current replacement or explanation |
|---|---|
| `alias prop new <=> old` | Define a concrete `prop` explicitly. |
| `lemma name:` | Use `thm name:`. |
| `max(a, b)`, `min(a, b)` | No current builtin objects; use an explicit definition when needed. |
| `by struct` | Not part of the current struct surface. |
| Bare template instance `T<A>` | Current syntax is `\T<A>`. |
| `[requires]`, `[run]` | Project dependencies and order come from imports and ordered exports. |
| `local import`, `trust import` | Use manifests, or ordinary `import` only in an isolated session. |
| `by strategy name` | Use `use strategy name`. |

### Documentation and test contract

Every `litex` fenced block in this manual is intended to be self-contained and
is run by `cargo test run_examples`. A `text` block is either a deliberately
invalid example, a non-executable shape, or an output sketch; its surrounding
paragraph states the intended reading and, for failures, whether checking
reaches `unknown` or `error`.

The language implementation is the final source of truth when this manual and
the runner disagree. Such disagreement is a documentation or diagnostic bug
to fix, not a reason to reinterpret a failed example silently.
