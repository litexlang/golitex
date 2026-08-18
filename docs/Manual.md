# Manual

Created and maintained by Jiachen Shen.

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
`trust` records an assumption; it is not a proof. A successful Litex check is
therefore a claim relative to the checker, its builtin rules, and any visible
trusted inputs. Use `-strict` when a run must reject user `trust`, `trust have`,
and `axiom` statements.

The Litex-to-Lean compiler provides an additional, independent checking path
for the language subset it supports. It is deliberately fail-closed: an
unsupported Litex construct must be reported instead of being translated with
`sorry` or an implicit project axiom. Compiler coverage changes more quickly
than the language reference, so the active representation, supported examples,
and current boundary live in the [compiler README](../lean/README.md), not in
this manual.

---

## Objects

An **object** is a mathematical value or expression. Objects do not assert
facts by themselves; a predicate or relation turns them into facts.

### Pure-set object model

Litex uses one universe of mathematical objects and chooses a pure-set
foundation: every well-defined Litex object satisfies `$is_set`. Thus a
numeral, a function value, a user-defined set, a function space, and each of
`N`, `Z`, `Q`, `R`, and `C` are all objects. They keep different mathematical
interfaces, but they are not different runtime carrier types.

Membership is a fact between two objects. For example, `1`, `N`, and `R` are
objects; `1 $in N` and `1 $in R` are separate facts about the same `1`.
Likewise, `forall x R` introduces an object `x` together with the fact
`x $in R`; it does not retype `x` as a host-language real number. A function
space `fn(x R) R` and a function belonging to it are also objects, while the
function-space membership records the callable contract.

This is Litex's explicit choice within the pure/impure distinction described
in Tao's *Analysis I*: the book remains agnostic about whether primitive
objects are themselves sets, while Litex adopts the pure interpretation. The
choice is foundational rather than notational. Surface concepts still retain
their ordinary roles: a number is used arithmetically, a function is applied,
and a set is inspected through membership. Set equality is extensional:
`by extension` proves equality from the two membership directions. In the pure
model this is the common object equality principle, not a separate equality
for a host-language `Set` type.

The object universe is not an internal universal set. `Object` is the
meta-level carrier used to implement the language, not an object that can be
written on either side of `$in`. Litex also does not provide unrestricted
comprehension. A set builder has the bounded form `{x S: facts}` over an
already available `S`; replacement and other partial constructors have their
own well-definedness obligations. These restrictions are what separate
"every object is set-coded" from the inconsistent claim that every predicate
defines a set of all objects.

### Names, numbers, and arithmetic

Names refer to builtin objects, earlier declarations, local binders, or
module-qualified declarations. Arithmetic uses ordinary precedence:
parentheses and indexing bind tightly, then powers, multiplication and
division, then addition and subtraction.

User-defined names may begin with a letter or one underscore and may then use
letters, numbers, and underscores. The prefix `__` is reserved for generated
names and is rejected in Litex source. Prefixes such as `h_` and `fn_` remain
ordinary user space.

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
| `quot(a, d)` | Native Euclidean integer quotient for `a $in Z` and `d $in N+` |
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

Exact numeric calls normalize inside ordinary facts or `eval` statements:

```litex
gcd(54, -24) = 6
quot(-7, 3) = -3
-7 % 3 = 2
lcm(12, -18) = 36
lcm(0, 0) = 0
floor(3.75) = 3
ceil(3.25) = 4
min(7, -2) = -2
max(7, -2) = 7
exp(0) = 1
ln(1) = 0
sign(-9) = -1
factorial(10) = 3628800
```

`gcd(a,b)` requires integer arguments that are not both zero. `quot(a,d)` uses
Euclidean division with `d $in N+`, so
`a = d * quot(a,d) + a % d` with a nonnegative remainder. `lcm`, `floor`,
`ceil`, `min`, and `max` have the domains shown in [Main object
criteria](#main-object-criteria).
`exp` is total on `R`; `ln` requires a positive real; `sign` accepts a real;
and `factorial` accepts a natural. Transcendental values such as `exp(2)` and
`ln(2)` remain symbolic rather than being replaced by decimal approximations.
These builtin names are reserved. Their verified algebraic and order laws are
listed under [Native numeric function rules](#native-numeric-function-rules).

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

The symbolic evaluator does not replace these constants with decimal runtime
values.

### Native real trigonometry (beta preview)

`sin(x)`, `cos(x)`, `tan(x)`, and `cot(x)` are dedicated builtin object forms,
not source-defined functions or ordinary function calls. Their arguments are
real angles in radians. `sin` and `cos` are total on `R`; `tan(x)` is
well-defined only when `cos(x) != 0`, and `cot(x)` only when `sin(x) != 0`.

The expressions remain symbolic, while common exact identities verify:

```litex
sin(0) = 0
cos(0) = 1
forall x R:
    sin(x)^2 + cos(x)^2 = 1
```

The preview intentionally does not assign every familiar special-angle value;
for example, `sin(pi / 6) = 1 / 2` still needs an explicit source fact.
Complex trigonometry, inverse trigonometric functions, analytic definitions,
and continuity theorems are also outside this interface.

The names `sin`, `cos`, `tan`, and `cot` are hard-reserved. Their bare names
are not first-class function values; higher-order code can use
`fn(x R) R {sin(x)}`. The evaluator does not assign approximate runtime values
to symbolic trigonometric expressions. The supported exact identities, bounds,
sign intervals, and monotonicity shapes are summarized under [Trigonometric
rules](#trigonometric-rules).

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
be rebound as declarations, parameters, indices, or fields.

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
The body may contain atomic facts, conjunctions, chains, and disjunctions, but
not an anonymous `forall`. Name a quantified condition with `prop`, then use
the resulting atomic prop fact:

```litex
prop below_all_squares(a R):
    forall x R:
        a <= x ^ 2

have lower_bounds set = {a R: $below_all_squares(a)}
```

For a family `g` of nonempty sets indexed by `I`, `general_cart(I, S, g)` is
the set of choice functions selecting an element of each `g(alpha)`:

```litex
have I set
have S nonempty_set
trust forall A S => $is_nonempty_set(A)
have g fn(alpha I) S

by thm general_cart_nonempty_by_choice_from_family(general_cart(I, S, g))
have f general_cart(I, S, g)
$is_choice_function_for(I, S, g, f)
forall alpha I:
    f(alpha) $in g(alpha)
```

The `trust` line makes the required factor-nonemptiness background explicit,
and the named builtin theorem makes the axiom-of-choice step explicit.
The quantified selection condition has the named builtin interface
`$is_choice_function_for(I, S, g, f)`. Its definition is
`forall alpha I: f(alpha) $in g(alpha)`, and `general_cart` has the canonical
atomic-filter expansion

```litex
have I set
have S nonempty_set
trust forall A S => $is_nonempty_set(A)
have g fn(alpha I) S

general_cart(I, S, g) = {f fn(f_index I)big_union(S): $is_choice_function_for(I, S, g, f)}
```

General-cart membership exposes both the named predicate and its pointwise
definition. Conversely, a function with the named predicate is admitted into
the general Cartesian product. No existential or set-builder body stores an
anonymous `forall`.

The family operators and replacement have different proof interfaces; their
similar set-valued syntax does not make them interchangeable:

| Object | Construction requirement | Membership behavior |
|---|---|---|
| `big_union(F)` | `F` must be a well-defined family expression. | `A $in F` and `x $in A` introduce `x $in big_union(F)`. Conversely, known union membership exposes `exist A F st {x $in A}`. |
| `big_intersect(F)` | `F` must be a well-defined family expression. | The current kernel has no matching automatic introduction/elimination package. Supply the needed family-membership theorem or facts explicitly. |
| `replacement(P, A)` | `P` must be a binary user `prop`/`abstract_prop`; the context must already prove that each `x $in A` has at most one set-valued output. | A known relation witness introduces membership. Known membership exposes `exist x A st {$P(x, y)}`, and `have by preimage` gives that witness a name. |

Family-union construction and elimination are both checked facts:

```litex
forall x set, F set, A set:
    A $in F
    x $in A
    =>:
        x $in big_union(F)

forall x set, F set:
    x $in big_union(F)
    =>:
        exist A F st {x $in A}
```

Replacement deliberately requires a previously established functionality
fact. In this example the two `trust` statements declare external background:
the relation has at most one set-valued output, and one particular pair is
related. Everything after those assumptions is checked normally.

```litex
abstract_prop image_rel(x, y)

trust forall x {1, 2}, y, y2 set:
    $image_rel(x, y)
    $image_rel(x, y2)
    =>:
        y = y2

have target set
trust $image_rel(1, target)
1 $in {1, 2}

target $in replacement(image_rel, {1, 2})
have by preimage source from target $in replacement(image_rel, {1, 2})
source $in {1, 2}
$image_rel(source, target)
```

An arbitrary binary relation is not enough: without the exact uniqueness
universal over `A`, even forming `replacement(P, A)` is a well-definedness
`error`, before any membership goal is considered.

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

`fn_range(f)` records the actual image, not merely the declared codomain. The
object is well-defined only when Litex can recover a checked function-set
signature for `f`. A well-defined application belongs to the range; stored
range membership then exposes both codomain membership and an existential
preimage. The range itself is a subset of the declared codomain.

```litex
have fn shift(x Z) Z = x + 1

shift(2) $in fn_range(shift)
fn_range(shift) $in power_set(Z)

have by preimage source from shift(2) $in fn_range(shift)
source $in Z
shift(2) = shift(source)
```

This is not inverse-function computation: the introduced `source` is an
opaque witness satisfying the stored application equality. Litex does not
claim it is unique unless a separate injectivity or uniqueness fact is
available.

### Products, tuples, sequences, and matrices

Cartesian products and indexed data remain ordinary set-theoretic objects.

```litex
(1, 2) $in cart(R, Z)
tuple_dim((1, 2)) = 2
proj(cart(R, Z), 1) = R
(1, 2)[1] = 1

[1, 2, 3] $in finite_seq(N+, 3)
[] $in finite_seq({}, 0)
[[1, 0], [0, 1]] $in matrix(Z, 2, 2)
```

| Form | Meaning |
|---|---|
| `cart(A, B, ...)` | Cartesian product |
| `cart_dim(c)`, `proj(c, i1)` | Product dimension and the `i1`-th factor set |
| `(a, b, ...)`, `tuple_dim(t)` | Tuple and tuple dimension |
| `finite_seq(S, n)`, `seq(S)` | Finite (`n : N`, including zero) or infinite sequence set |
| `[a, b, ...]`, `a[i1]` | Displayed finite sequence and index access |
| `matrix(S, r, c)` | Matrix set |
| `[[...], [...]]` | Displayed matrix |
| `A '+ B`, `A '- B`, `A '* B` | Matrix addition, subtraction, multiplication |
| `c *' A`, `A '^ n` | Scalar multiplication and matrix power |

`[]` is the finite-sequence literal of length zero. Thus
`[] $in finite_seq(S, 0)` for every set `S`, including the empty set; a literal
with a different number of entries than `n` is still rejected.

Dimensions are checked, not inferred from wishful notation:

```text
[[1, 2], [3]] $in matrix(Z, 2, 2)
```

This is an `error` because the displayed rows do not have one common width.

Matrix operators are a separate apostrophe-marked surface. They currently
operate on real matrices. Addition and subtraction require equal dimensions;
multiplication requires matching inner dimensions; scalar multiplication uses
a real scalar; and powers require a square matrix and a positive-natural
exponent. Membership of a symbolic result is requested through the ordinary
function-set builtin interface:

```litex
claim:
    ? forall m, n N+, A, B matrix(R, m, n), c R, i1, j N+:
        i1 <= m
        j <= n
        =>:
            A '+ B $in matrix(R, m, n)
            A '- B $in matrix(R, m, n)
            c *' A $in matrix(R, m, n)
            (A '+ B)(i1, j) = A(i1, j) + B(i1, j)
    by thm fn_set_member(A '+ B, matrix(R, m, n))
    by thm fn_set_member(A '- B, matrix(R, m, n))
    by thm fn_set_member(c *' A, matrix(R, m, n))
    (A '+ B)(i1, j) = A(i1, j) + B(i1, j)

claim:
    ? forall m, n, p N+, A matrix(R, m, n), B matrix(R, n, p):
        A '* B $in matrix(R, m, p)
    by thm fn_set_member(A '* B, matrix(R, m, p))

claim:
    ? forall n, k N+, A matrix(R, n, n):
        A '^ k $in matrix(R, n, n)
        A '^ 1 = A
        A '^ (k + 1) = (A '^ k) '* A
    by thm fn_set_member(A '^ k, matrix(R, n, n))
    A '^ 1 = A
    A '^ (k + 1) = (A '^ k) '* A
```

Concrete matrix literals can also be evaluated with `eval`; symbolic matrix
membership and power equations remain proof facts rather than evaluator
output.

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

The checked equality, partition, congruence, and reindexing laws for these
aggregates are listed in [Powers, logarithms, sums, products, and
remainder](#powers-logarithms-sums-products-and-remainder). In particular,
`reduce` is order-sensitive; arbitrary bijective reindexing belongs to the
associative-commutative `finite_set_reduce` interface instead.

`finite_set_max(S)` and `finite_set_min(S)` are not total default-value
operators. If finiteness, nonemptiness, or `S $subset R` is unavailable, the
object is ill-defined rather than assigned an arbitrary endpoint.

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
called, as in `space.scalars.mul(a, b)` or
`&CallableBox{make_box(f)}.entries(i)`. The selected field's declared carrier
must be a function set. Field access after a call, index, or parenthesized
expression is not currently supported; select that next view explicitly with
`&Struct{expr}.field`.

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
Write an instance as `\name<args>`.

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

Omitting the backslash is a parse `error`.

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
$coprime(14, 25)
not $coprime(14, 21)
```

`$prime(p)` is a native predicate on `N`. It is false at `0` and `1`;
concrete natural literals that fit in `u64` are decided exactly, while larger
literals are left to proof rather than guessed. `by def $prime(p)` exposes the
symbolic trial-divisor contract (`2 <= p` and no divisor in `range(2, p)`). An
arbitrary integer or real argument is still rejected unless its membership in
`N` is known.

`$coprime(a, b)` likewise follows Mathlib's elementary-number-theory surface:
both arguments must belong to `N`, and the predicate means `gcd(a, b) = 1`.
It is total on natural pairs, so `$coprime(0, 1)` holds while
`$coprime(0, 0)` does not. A positive fact exposes both the non-all-zero
condition needed by native `gcd` and the gcd-one equation. Integer or real
arguments require a separate future interface rather than silently changing
this predicate's domain.

The preview predicate `$dvd(x, y)` uses dividend-first order: the nonzero
integer `y` divides the integer `x`. Its domain is `Z × Z*`, and its defining
consequences are `x % y = 0` and `exist a Z st {x = a * y}`. In particular,
`$dvd(0, 0)` is not a well-defined application; the nonzero divisor requirement
keeps the remainder and integer-multiple formulations equivalent.

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
chain, or one flat conjunction. In ordinary operator terms, `and` binds more
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

Existential bodies may contain atomic facts, conjunctions, chains, and
disjunctions. They do not contain anonymous `forall` facts. Put the quantified
condition in a named `prop` and reference it atomically. Braces delimit the
body:

```litex
prop universally_self_equal(x R):
    forall y R:
        x = x

forall:
    exist x R st {$universally_self_equal(x)}
    =>:
        exist x R st {$universally_self_equal(x)}
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

A universal whose parameter domain is a literal empty display, a concretely
empty `range(a,b)`, or a concretely empty `closed_range(a,b)` verifies
vacuously without checking its body. This fast path uses literal endpoint
evaluation; an arbitrary named set is not treated as empty merely because the
user expects it to be.

```litex
forall x {}:
    x != x

forall index range(3, 3):
    index != index
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

A useful way to think about a `setting` is as the standing convention at the
beginning of a mathematics chapter: throughout the chapter, `M` denotes a
space of a certain kind, `f` and `g` denote certain kinds of functions, and
`a`, `b`, and `c` denote certain kinds of numbers. Later statements can then
use this recurring cast of objects and common assumptions without introducing
them again each time. A Litex `setting` makes the same convention explicit,
reusable, and checkable.

```litex
setting EqualPair(X nonempty_set, x, y X):
    x = y

forall [EqualPair], z X:
    z = z

forall [EqualPair] => x = y

forall [EqualPair(Y, a, b)] => a = b
```

This elaborates to the ordinary fact:

```litex
forall X nonempty_set, x, y X, z X:
    x = y
    =>:
        z = z
```

Parameters are declared in parentheses in the `setting` header; the indented
body contains only shared assumptions. A setting with no shared assumptions
omits both the colon and body, for example `setting OneElement(X nonempty_set,
x X)`. A setting does not introduce global objects and does not assert its
assumptions; it only abbreviates the corresponding `forall` prefix. Every use
allocates fresh binders, even when the same setting is used several times.
Extra parameters require a comma after the closing bracket.

The optional argument list renames the freshly declared binders positionally:
`[EqualPair(Y, a, b)]` declares new `Y`, `a`, and `b` parameters and
instantiates the stored parameter types and assumptions with those names. The
arguments are exact bare binder names, not expressions and not references to
outer objects. Their count must equal the setting's parameter count; an active
or otherwise visible name is a collision rather than a shadowed reference.
The bare `[EqualPair]` spelling is shorthand for fresh binders with the
setting's original names.

Settings are supported in block `forall [Name]` headers and in the inline form
`forall [Name] => fact`. The inline form uses exactly the parameters and
shared assumptions stored by the setting; add extra parameters with block
syntax. Goal and negated universal positions use the same expansion paths. A
module-qualified setting may be referenced as `forall [Module::Name]:` or
`forall [Module::Name] => fact`; explicit names may follow the qualified name
in the same way.

Concrete `prop` and `setting` headers also accept setting bundles mixed with
ordinary typed parameters. Each bundle expands to ordinary definition
parameters, and its shared assumptions are inserted in header order before the
explicitly written body:

```litex
setting GroupSetting(A nonempty_set, mul fn(x, y A) A, one A, inv fn(x A) A):
    forall u, v, w A:
        mul(mul(u, v), w) = mul(u, mul(v, w))
    forall u A:
        mul(one, u) = u
        mul(inv(u), u) = one

prop is_group_homomorphism([GroupSetting(A, mul_A, one_A, inv_A)], [GroupSetting(B, mul_B, one_B, inv_B)], f fn(x A) B):
    forall x, y A:
        f(mul_A(x, y)) = mul_B(f(x), f(y))

setting GroupHomomorphismSetting([GroupSetting(A, mul_A, one_A, inv_A)], [GroupSetting(B, mul_B, one_B, inv_B)], f fn(x A) B):
    forall x, y A:
        f(mul_A(x, y)) = mul_B(f(x), f(y))
```

The stored and displayed declarations use the equivalent flat parameter list,
followed by the two instantiated `GroupSetting` condition lists and the
explicit homomorphism condition.

A parameterized `struct` header accepts the same bundles. Its expanded
parameters remain header parameters, while the setting conditions are
prepended to the struct's membership conditions before explicit `<=>:` facts:

```litex
setting GroupSetting(G nonempty_set, mul_G fn(x, y G) G, one_G G, inv_G fn(x G) G):
    forall u, v, w G:
        mul_G(mul_G(u, v), w) = mul_G(u, mul_G(v, w))
    forall u G:
        mul_G(one_G, u) = u
        mul_G(inv_G(u), u) = one_G

struct GroupAction<[GroupSetting(G, mul_G, one_G, inv_G)], V nonempty_set>:
    act fn(g G, v V) V
```

Consequently membership in `&GroupAction<G, mul_G, one_G, inv_G, V>` exposes
the instantiated group laws. `G`, `mul_G`, `one_G`, and `inv_G` are not struct
fields and are not emitted by `unfold`. Setting bundles are not currently
accepted in `abstract_prop` or `template` headers, in struct field lists, or in
object expressions.

An ordinary universal fact may use a one-line form when it has exactly one
premise and one conclusion, or no premise. The conclusion is a bare fact; it
is not wrapped in braces:

```litex
forall x R: x > 0 => x != 0
```

Existential and set-builder property bodies do not admit either block or
one-line `forall`; name the quantified condition with `prop` and use its atomic
`$P(...)` fact there.

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
| Inline universal | `forall params: assumption => conclusion` |
| Negated universal | `not forall params: facts` |
| Inline negated universal | `not forall params: assumption => conclusion` |

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
| `$is_choice_function_for(I, S, g, f)` | `f` selects one member of `g(alpha)` for every `alpha` in `I` |
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

For `have x S = value`, Litex checks `value $in S` before committing `x`. A
carrier-mismatch error names the required carrier,
the narrowest standard numeric carrier currently provable for `value` when one
is available, and confirms that the binding was not stored. For example,
`q * x % p` is declaration-time `Z` data even when `p`, `q`, and `x` are
positive naturals; declaring it directly as `N` is rejected rather than
silently narrowed.

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

The stored case equations are directly usable at arguments whose case can be
proved. Litex instantiates the selected equation and performs nested arithmetic
normalization, so a successor argument does not require separate lines for
`n + 1 > 0` and `(n + 1) - 1 = n`. It still refuses to select a case when its
condition is not known.

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

### Local proof blocks: `claim`, `example`, `sketch`, and `try`

`claim` proves one target and commits that target to the surrounding context.
`example` proves one target but commits nothing; it is the checked,
non-exporting counterpart of Lean's anonymous `example`. Temporary proof steps
remain local in both forms. `sketch` checks a local block without a distinguished
target and commits nothing. `try` checks a candidate block atomically and
commits it only if every step succeeds. A `claim` or `example` target always
appears under its header as an indented `? fact`; header forms such as
`claim fact:` and `example fact:` are not accepted.

```litex
claim:
    ? forall x R:
        x = 2
        =>:
            (x + 1)^2 = 9
    x + 1 = 3
    (x + 1)^2 = 9

example:
    ? 1 + 1 = 2

sketch:
    2 + 2 = 4

try:
    have x R = 1
    x + 1 = 2

x = 1
```

`? fact` is an internal proof target, not a top-level assertion:

```text
? 1 = 1
```

This is a parse `error`. Put the target under `claim`, `example`, `thm`,
`strategy`, or a statement that explicitly expects a goal.

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

A bare `by thm name(args)` stores all instantiated conclusions. A selected
call stores only the requested atomic fact and its ordinary inferred
consequences.

There is no separate `lemma` keyword:

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

[allow bare export]
Part2

[allow bare import std]
basics

[allow bare import]
Algebra
```

Important rules:

1. `[export]` is ordered and each entry names one direct `.lit` file or one
   configured child directory.
2. Direct child `.lit` files and configured submodule directories appear once;
   Markdown and other non-Litex sidecars are not exports. The reserved local
   `.drafts/` directory is excluded from module discovery; every other direct
   child directory must still be exported.
3. Only a `module` imports. `[import]` mounts another module; `[import std]`
   mounts an installed standard package.
4. An optional module-only `[module] flatten = true` removes one file namespace
   layer and requires exactly one `.lit` export.
5. Canonical names follow the mounted module and export path, for example
   `Algebra::chapter::name`.

The three `allow bare` tables are optional, explicit conveniences. Each line is
one name from its matching source table: `[allow bare export]` accepts only an
exported folder/submodule (never a `.lit` file), `[allow bare import std]`
selects an `[import std]` package, and `[allow bare import]` selects an
`[import]` alias. Without these tables, existing projects remain
qualified-only.

For each source file, Litex builds one bare-name index after configured imports
and preceding exports have loaded. An enabled package contributes the terminal
symbols from its entire recursive public `[export]` tree, but not anything from
its private imports. A flattened package behaves the same way: bare `b` and
public `A::b` resolve to the symbol stored in its sole exported file. Re-export
of the same symbol is deduplicated; two different symbols with the same
terminal name make the allow-bare configuration invalid. The stable diagnostic
scan order is export, standard import, then path import; it is not an overwrite
precedence.

Explicit `A::b` always resolves `A` in the module namespace and bypasses the
bare index. Module aliases and symbols are separate, so a local symbol may also
be named `A`; field selection such as `obj.b` likewise remains in the field
namespace. Once external bare `b` is active, however, the source file may not
declare or bind another symbol named `b` at any level. Struct field names are
the exception because they are selected through a struct/field namespace. An
enabled export is unavailable while it is still loading, so an earlier file
cannot cite a later export by its bare name. These permissions inherit into
descendant submodules.

Source-level `import "../Algebra" as Algebra` and `import std basics` are
available only in an isolated source session. Repository module sources use
their manifest; dynamic imports there are rejected. Isolated imports remain
qualified-only and never activate manifest allow-bare tables.

```text
[hierarchy]
submodule

[import std]
basics
```

This manifest is invalid because a `submodule` cannot declare imports.

Project execution, persistent sessions, output modes, graph commands, and the
development-only `-trust-before-line` option are CLI contracts rather than
language syntax. See the [CLI reference](cli.md) for the current command set
and [Setup](Setup.md) for installation and project-running examples.

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

This table is exhaustive at the public statement-family level. Closely related
forms share one row, such as tuple, Cartesian-product, sequence, and matrix
introductions.

| Public form | What is checked before success | What success commits or exposes |
|---|---|---|
| Bare fact | Well-definedness, then known facts/builtin rules/definitions/universals/strategies. | The fact and its ordinary inferred consequences. |
| `let x = value` | `value` is well-defined and `x` is fresh. | One untyped name and `x = value`. |
| `have x S`, `have x S = value`, `have x S: ...` | Nonemptiness or concrete membership, declared carrier, and any witness body. | A fresh object, its carrier facts, equality/body facts, and inference. |
| `trust fact`, `trust have ...` | Parsing, binding, well-definedness, and transactional staging still run; proof truth is assumed. | One trusted transaction. Failure commits nothing. |
| `obtain ... from exist ...` | The source existential is known; names, count, and dependent parameter types match. | Opaque witness names plus their type and direct body facts. |
| `obtain ... from $P(args)` | `$P(args)` is known and its concrete definition has exactly one positive `exist`/`exist!` clause. | The same witness facts after checked definition projection. |
| `obtain ... from thm name(args)` | The named user, imported, or reserved builtin theorem passes the ordinary `by thm` argument/premise checks and has exactly one direct positive `exist`/`exist!` conclusion. | The theorem application remains scoped; only the eliminated witnesses, types, body facts, and `exist!` uniqueness interface escape. |
| `have by preimage ...` | Known membership in `fn_range(f)` or `replacement(P,A)` and matching source shape. | Opaque preimage names and the application/relation witness facts. |
| `have fn ... = ...` | Ordered parameter domains, return carrier, body membership, and side conditions. | A callable function, its signature, and checked defining equation. |
| `have fn ... by cases` | Cases are exhaustive, pairwise disjoint, and every result belongs to the return set. | A callable piecewise function and guarded case equations. |
| `have fn ... by induc` | Integer measure/lower bound and strictly decreasing in-domain recursive calls. | A callable recursive function and checked case equations. |
| `have fn ... by exist!` | The displayed universal unique-existence goal, including uniqueness. | A selected callable function and its defining property. |
| `have tuple/cart/seq/finite_seq/matrix ... for ...` | Symbolic dimensions, index bounds, coordinate carriers, and formulas. | A named indexed object, its type, and coordinate equations. |
| `prop`, `abstract_prop` | Parameter declarations; concrete `prop` clauses must be well-defined. | A foldable concrete definition or an uninterpreted predicate interface. |
| `struct`, `setting`, `template` | Field/setting/template parameters and body contracts. | A named view, reusable binder prefix, or one parameterized definition family. |
| `have algo for ...` | A declared function exists and the implementation agrees on its cases/results. | An executable presentation; it does not replace the mathematical function facts. |
| `claim` | One target is proved in a lexical child scope. | Only the target; helper statements do not escape. |
| `example` | One target is proved in a lexical child scope. | Nothing; the target and helper statements do not escape. |
| `sketch` | Every contained statement checks. | Nothing outside the block. |
| `try` | The whole block succeeds transactionally. | All block effects on success; none on failure. |
| `thm`, `axiom` | `thm` proves its target; `axiom` checks its interface but trusts truth. | A named reusable theorem interface; universal facts also enter ordinary matching. |
| `by thm` | Arity/domains/premises and optional selected atomic target. | All instantiated conclusions, or only the requested atomic selection. |
| `strategy` | The statement proves its restricted atomic universal pattern. | A named user search rule, enabled when first defined. |
| `witness exist/exist!` | Witness count/types/body; `exist!` additionally verifies the generated two-candidate uniqueness universal. | The exact existential fact. Binder names stay local. |
| `witness $P(args)` | The concrete prop has one positive ordinary `exist` clause; ordinary witness checks run after substitution. `exist!` uses explicit `witness exist! ...` followed by `by def`. | `$P(args)` as the primary fact, then definition inference. |
| `witness $is_nonempty_set(S)` | The proposed object is in `S`. | Nonemptiness of `S`. |
| `by cases`, `by contra` | Every branch closes the target, or an explicit contradiction is produced. | The requested target only. |
| Enumeration, induction, `by for`, `by extension` | The target has the exact finite/range/discrete/extensional shape and every generated subgoal closes. | The requested universal/equality/atomic target. |
| `by def` | One positive concrete/builtin definitional target and every defining clause. | The target with explicit definition provenance. |
| Predicate-property registrations | The proof has the exact reflexive/symmetric/transitive/antisymmetric predicate shape. | A reusable property route; antisymmetry may later close equality. |
| `by regularity_axiom` | Its displayed set/nonemptiness obligations. | An explicitly trusted set-theoretic conclusion; strict mode rejects the step. |
| `by axiom_of_choice` | The family is a set and every member is proved nonempty. | Stores `exist f fn(A S)big_union(S) st {$is_choice_function_for(S,S,fn(A S)S {A},f)}`. The existential body is atomic. |
| `by zorn_lemma` | The set, binary relation, exact named upper-bound/maximality definitions, nonemptiness, partial-order laws, and chain-upper-bound obligation. | Stores `exist m S st {$M(m)}` using the supplied named maximality prop. The chain witness likewise uses the supplied atomic upper-bound prop. |
| `import` | Only the isolated-session import grammar and module constraints. | A qualified imported environment; maintained modules use manifests instead. |
| `eval` | The expression belongs to the supported executable subset. | Evaluation output, not a new mathematical proof fact. |
| `clear` | No proof obligation. | Resets the current user environment. |
| `do_nothing` | No proof obligation. | A successful no-op; it never closes an outstanding goal. |
| `use strategy`, `stop strategy` | The named strategy exists. | Changes later user-strategy search, not builtin rules or known facts. |

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
| Named universal prefix | `setting Name(params): ...`, then `forall [Name]`, `forall [Name(fresh_names)]`, or a `prop`/`setting`/`struct` parameter bundle | [Named universal settings](#named-universal-settings) |
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
| Universal | `forall`, `forall [Setting]`, `forall [Setting(fresh_names)]`, `forall ... <=>:`, `not forall` | [Universal facts](#universal-facts) |
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
- `st { ... }` delimits an existential body. Its entries are atomic facts or
  their supported boolean combinations; name a quantified condition with
  `prop` before using it there. The same restriction applies to set builders.
- `#` starts a line comment. Indentation defines block structure.
- Matrix operators contain an apostrophe: `'+`, `'-`, `'*`, `*'`, and `'^`.

### Unicode mathematical input aliases (preview)

Litex accepts the following Unicode mathematical input. Simple aliases are
canonicalized during tokenization; infix set forms are lowered by the parser to
the existing set-object and fact nodes. Stored facts, diagnostics, and verifier
semantics continue to use canonical ASCII Litex syntax.

| Unicode input | Canonical Litex syntax |
|---|---|
| `∀`, `∃`, `∃!` | `forall`, `exist`, `exist!` |
| `≤`, `≥`, `≠` | `<=`, `>=`, `!=` |
| `→`, `↔` | `=>`, `<=>` |
| `∧`, `∨`, `¬` | `and`, `or`, `not` |
| `∈` | `$in` |
| `∉` | `not ... $in ...` |
| `⊆`, `⊇` | `$subset`, `$superset` |
| `⊂`, `⊊`, `⊋` | `$proper_subset`, `$proper_subset`, `$proper_superset` |
| `A ∪ B`, `A ∩ B` | `union(A, B)`, `intersect(A, B)` |
| `A × B` | `cart(A, B)` |
| `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` | `N`, `Z`, `Q`, `R`, `C` |
| `ℕ+`, `ℤ+`, `ℚ+`, `ℝ+` | `N+`, `Z+`, `Q+`, `R+` |
| `ℤ-`, `ℚ-`, `ℝ-` | `Z-`, `Q-`, `R-` |
| `ℤ*`, `ℚ*`, `ℝ*`, `ℂ*` | `Z*`, `Q*`, `R*`, `C*` |
| `π`, `∅` | `pi`, `{}` |

For example, this is the same universal fact as its ASCII spelling:

```litex
∀ x ℝ:
    x ≠ 0
    →:
        x ∈ ℂ
        x ≤ x ∧ x ≥ x
```

Aliases are recognized only as complete tokens and are not rewritten inside
quoted module paths. `⊂` deliberately means strict/proper subset, the same as
`⊊`; non-strict subset remains `⊆`. Unicode compact numeric sets mirror the
existing ASCII keyword family exactly, so `ℕ*` remains unsupported just as
`N*` is unsupported.

`∃!` has exactly the existing unique-existence semantics of `exist!`. In
particular, `witness ∃! ...` must prove both that the supplied witness satisfies
the body and that any two witnesses satisfying the body are equal.

The infix precedence from lower to higher is `∪`, `∩`, `×`, then the existing
arithmetic object operators. Union and intersection associate to the left. A
direct product chain is flattened, so `A × B × C` becomes `cart(A, B, C)`;
parentheses can request nesting. `×` never means numeric multiplication:
`2 × 3` is parsed as `cart(2, 3)` and is rejected because the factors are not
sets. Write `2 * 3` for arithmetic multiplication. The word forms remain
constructor calls such as `union(A, B)`; this preview does not add `A union B`.

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

For an ordinary atomic fact, Litex follows this public progression:

1. Parse the statement and check that every object is well-defined.
2. Reuse an already known fact, including transport through known equalities,
   or evaluate a closed expression directly.
3. Try a bounded builtin mathematical rule or a terminating structural rule.
4. Try an applicable known `forall`, a concrete definition, a registered
   predicate property, or an enabled user strategy.
5. On success, store the fact and run builtin inference on the new information.

This is goal-directed verification, not unrestricted theorem search. A builtin
rule may ask for its documented premises, but it does not silently build an
arbitrary chain of other builtin rules. When a mathematically valid jump is
`unknown`, expose one or two intermediate facts in the source; those facts make
the intended route readable to both the checker and the reader.

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
`$prime`, `$coprime`, `$dvd`, `$injective`, `$surjective`, `$bijective`,
`$fn_eq_in`, and `$fn_eq`.

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
name witnesses from an already known existential, from one concrete prop
definition, or from the sole direct existential conclusion of a named theorem.
Use `have by preimage` to name a preimage from known range or replacement
membership.

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

prop has_copy(a R):
    exist x R st {x = a}

witness $has_copy(2) from 2:
    2 = 2

obtain copy from $has_copy(2)
copy = 2

thm self_exists:
    ? forall a R:
        exist x R st {x = a}
    witness exist x R st {x = a} from a

obtain theorem_copy from thm self_exists(3)
theorem_copy = 3

witness $is_nonempty_set({1, 2}) from 1:
    1 $in {1, 2}
```

`witness $has_copy(2) from 2` is a checked definition-introduction statement.
The concrete proposition must have exactly one positive ordinary `exist`
clause. Litex substitutes the call arguments, verifies the witness types and
body, stores `$has_copy(2)`, and then exposes its instantiated existential
meaning through ordinary definition inference. For `exist!`, use the explicit
`witness exist! ...` route and prove uniqueness before folding the named
predicate with `by def`. Abstract, negative, nonexistential, and multi-clause
definitions do not use this shorthand.

The `obtain ... from $P(args)` shorthand is a checked definition-elimination
step. The source
`$has_copy(2)` must itself verify, and the concrete prop definition must have
exactly one clause whose outer form is positive `exist` or `exist!`. Litex
substitutes the call arguments into that clause and then uses the ordinary
existential eliminator. `abstract_prop`, negated prop facts, `not exist`,
ordinary nonexistential definitions, and multi-clause definitions are rejected.

`obtain names from thm name(args)` performs the ordinary explicit theorem call
inside a temporary child environment, then eliminates its sole direct positive
`exist` or `exist!` conclusion. The theorem may be local, module-qualified and
imported, or a reserved builtin theorem interface. Argument types, theorem
domain facts, and builtin requirements are checked exactly as for `by thm`.
Zero or multiple direct conclusions, a nonexistential conclusion, `not exist`,
or a witness-count mismatch are errors. The intermediate existential does not
enter the parent context; detailed output retains the nested named-theorem
application as the elimination's proof source.

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

by enumerate finite_set:
    ? forall y {1, 2, 3} => y = 1 or y = 2 or y = 3

have i1 closed_range(1, 3)
by closed_range as cases: i1 $in 1...3
```

Finite-set enumeration always takes its target from the first indented
`? forall ...` goal. Proof statements after that goal remain optional.

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

`by for` always takes an indented `? forall ...` goal. Proof statements after
that goal are optional. `by extension` alone also keeps its bodyless one-line
form:

```litex
by for:
    ? forall i1 range(0, 3) => i1 < 3
by extension {1} = {1}
```

Use the block extension form when its proof needs additional statements:

```litex
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

`by regularity_axiom` exposes set-theoretic foundation as an explicit trusted
step:

| Form | Checked obligations | Trusted conclusion |
|---|---|---|
| `by regularity_axiom(A)` | `A` is nonempty | A member of `A` disjoint from `A` |

This form is not an ordinary derived proof. Its statement form and output keep
the direct boundary visible; `-strict` rejects it. Litex does not taint later
theorems or facts with transitive trust metadata.

`by axiom_of_choice` now stores its chooser through the builtin named property:

```litex
have F set
trust forall A F:
    $is_nonempty_set(A)
by axiom_of_choice: set F:
    forall A F:
        $is_nonempty_set(A)

obtain chooser from exist f fn(A F)big_union(F) st {$is_choice_function_for(F, F, fn(A F) F {A}, f)}
forall A F:
    chooser(A) $in A
```

`by zorn_lemma` requires the two quantified conditions that occur below
existentials to be named concrete props. Their signatures and definitions are
checked exactly before any obligation is accepted:

```litex
have S set
abstract_prop leq(x, y)
prop upper_bound(c power_set(S), u S):
    forall x c:
        $leq(x, u)
prop maximal(m S):
    forall x S:
        $leq(m, x)
        =>:
            x = m

by zorn_lemma: set S, prop leq, prop upper_bound, prop maximal:
    trust $is_nonempty_set(S)
    trust:
        forall x S:
            $leq(x, x)
        forall x, y, z S:
            $leq(x, y)
            $leq(y, z)
            =>:
                $leq(x, z)
        forall x, y S:
            $leq(x, y)
            $leq(y, x)
            =>:
                x = y
        forall c power_set(S):
            forall x, y c:
                $leq(x, y) or $leq(y, x)
            =>:
                exist u S st {$upper_bound(c, u)}

obtain m from exist m S st {$maximal(m)}
```

The choice-backed `general_cart_nonempty_by_choice_from_family` and
`general_cart_nonempty_by_choice_from_pointwise` theorem interfaces remain
available when only nonemptiness of a general Cartesian product is needed.

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
| Atomic | Is an equality, membership, sign, domain condition, or matching lemma missing? For a nested function application, `detail` may name the unmatched application, the nearest known prefix equality, and the remaining unapplied argument count. |
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

Automatic rules are intentionally bounded. A direct rule checks its documented
premises; a structural builtin strategy may recurse only through smaller pieces
of the same object shape. Neither route is unrestricted theorem search. The
detailed verifier output shows the rule and its child facts when that boundary
matters.

The catalog below records the public mathematical shapes rather than the
checker dispatch order. For example, `sqrt(t) != 0` requires the strict premise
`t > 0`; `t >= 0` is insufficient because `sqrt(0) = 0`. Likewise, interval
nonemptiness depends on the appropriate strict or weak endpoint comparison.

Rules that genuinely need a universal, existential, or compound premise are
called explicitly through reserved builtin theorem names. Each call verifies
its stated requirements before storing the conclusion:

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
| `by thm rational_has_unique_reduced_fraction(q)` | `exist! p Z, d N+ st {q = p / d, gcd(p, d) = 1}` |
| `by thm subset_of_finite_set_is_finite(A, B)` | `$is_finite_set(A)` after checking `A $subset B` and finite `B` |
| `by thm finite_set_has_bijective_index(s)` | `exist idx finite_seq(s, finite_set_size(s)) st {$bijective(closed_range(1, finite_set_size(s)), s, idx)}` |

These names are bare global reserved names. They cannot be rebound by user
objects, parameters, theorems, or axioms, and a qualified spelling is rejected.
The rational interface has arity one and requires its argument to be known in
`Q`. The finite-set indexing interface likewise stores an existential and
requires finite `s`; its witness is noncanonical. The finite-subset interface
requires an already verified subset premise and does not enable automatic
subset-chain search. Both finite-set names are kernel interfaces, not
`std/basics` exports.

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

#### How to read the catalogue

The tables group rules by their mathematical contract, not by implementation
branches. A listed law describes a recognized source shape and
its required facts; it does not promise that every logically equivalent
reformulation is automatic.

Detailed output distinguishes computation, direct builtin rules, structural
strategies, definition routes, and explicit builtin theorem calls. Consult that
proof tree when a nearby spelling is `unknown`, then state the missing bridge
fact explicitly.

#### Declarative algebra, nonzero, and order schemas

The following table groups the main algebra, nonzero, and order schemas by
their mathematical role. Mirrored strict and weak orientations are described
together.

| Group | Recognized laws and required premises |
|---|---|
| Absolute-value algebra | `abs(x*y) = abs(x)*abs(y)`; `0 <= abs(x)`; `x <= abs(x)`; `-x <= abs(x)`; `-abs(x) <= x`; `abs(x+y) <= abs(x)+abs(y)`; `abs(x-y) <= abs(x)+abs(y)`; `abs(x)-abs(y) <= abs(x-y)` and `<= abs(x+y)`; `x != 0` gives `0 < abs(x)`; nonnegative/nonpositive `x` selects `abs(x)=x` or `abs(x)=-x`. |
| Nonzero closure | Known nonzero real factors give `a*b != 0`; a nonzero numerator and denominator give `a/b != 0`. Division still requires the denominator fact for well-definedness. |
| Order weakening | `a < b` gives `a <= b`, and `a > b` gives `a >= b`. The converse is not available without disequality or another strict premise. |
| Addition | Weak+weak gives weak order; strict+strict gives strict order; weak+strict and strict+weak give strict order. Adding a common left term preserves either order. Nonnegative summands give a nonnegative sum; the sum is positive when both are positive or one is positive and the other nonnegative. `0 <= b` gives `a <= a+b`. |
| Subtraction | `a <= b` and `0 <= c` give `a-c <= b`; `v <= u` gives `0 <= u-v`; `v < u` gives `0 < u-v`. These are real-order rules and do not totalize subtraction in `N`. |
| Multiplication and division signs | Positive factors/quotients are positive; nonnegative factors/quotients are nonnegative. Quotient rules require a positive denominator, not merely a nonzero denominator. |
| Minimum | `min(a,b)` is below both arguments; a known comparison selects the appropriate argument; `min` is commutative, associative, idempotent, monotone, and satisfies `min(a,max(a,b))=a`. |
| Maximum | `max(a,b)` is above both arguments; a known comparison selects the appropriate argument; `max` is commutative, associative, idempotent, monotone, and satisfies `max(a,min(a,b))=a`. |

These are executable instances of four different groups:

```litex
forall x, y R:
    abs(x * y) = abs(x) * abs(y)
    abs(x + y) <= abs(x) + abs(y)
    abs(x) - abs(y) <= abs(x - y)

forall a, b R:
    a != 0
    b != 0
    =>:
        a * b != 0
        a / b != 0

forall a, b, c, d R:
    a <= b
    c < d
    =>:
        a + c < b + d

forall a, b, c, d R:
    a <= c
    b <= d
    =>:
        min(a, b) <= min(c, d)
        max(a, b) <= max(c, d)
```

For example, `a / b != 0` above is not obtained from the multiplication rule
plus another division rule: the declarative quotient schema consumes both
known nonzero premises directly.

#### Declarative set schemas

The declarative set schemas cover the following groups:

| Group | Recognized laws and required premises |
|---|---|
| Union membership and containment | Membership in either operand introduces union membership. Both operands are subsets of the union. If `A $subset S` and `B $subset S`, then `union(A,B) $subset S`. |
| Intersection membership and containment | Membership in the intersection exposes membership in both operands. The intersection is a subset of each operand. A known `A $subset B` reduces `intersect(A,B)` to `A`, with the mirrored form for `B $subset A`. |
| Union/intersection algebra | Both operations are commutative and associative; union is idempotent and has `{}` as a two-sided identity; `intersect(A,union(B,C))` distributes to the union of the two intersections. |
| Relative complement | Membership exposes membership in the left set and nonmembership in the right; `set_minus(A,B) $subset A`; `A \\ (B union C)` and `A \\ (B intersect C)` obey the two relative De Morgan laws. If `B $subset A`, then removing `A \\ B` from `A` recovers `B` in either equality orientation. |
| Finiteness and infiniteness | Union/intersection of finite sets is finite; removing anything from a finite left operand is finite; removing a finite set from an infinite set remains infinite. |
| Nonemptiness | A nonempty union operand makes the union nonempty. `power_set(A)` is nonempty for every set `A`. |
| Power set | `A $subset B` introduces `A $in power_set(B)`; a finite base gives a finite power set. |
| Empty set | `{}` is a subset of every set. |

Representative set algebra and containment rules verify directly:

```litex
forall A, B, D set:
    union(A, B) = union(B, A)
    union(union(A, B), D) = union(A, union(B, D))
    intersect(A, union(B, D)) = union(intersect(A, B), intersect(A, D))
    set_minus(A, union(B, D)) = intersect(set_minus(A, B), set_minus(A, D))

forall A, B, S set:
    A $subset S
    B $subset S
    =>:
        union(A, B) $subset S

forall A, B set:
    B $subset A
    =>:
        set_minus(A, set_minus(A, B)) = B
```

The schemas are directional where their premises are directional. For
example, an intersection equality does not by itself manufacture the subset
premise needed by the corresponding reduction rule.

#### Finite-set cardinality tracer

Finite-set constructors feed a second layer of custom cardinality rules. The
intersection, difference, and union facts appear before the equality because
they are the exact known premises consumed by later one-layer rules:

```litex
forall A, B finite_set:
    $is_finite_set(intersect(A, B))
    $is_finite_set(set_minus(A, B))
    $is_finite_set(union(A, B))
    finite_set_size(union(A, B)) = finite_set_size(A) + finite_set_size(B) - finite_set_size(intersect(A, B))
    finite_set_size(A) = finite_set_size(intersect(A, B)) + finite_set_size(set_minus(A, B))
    intersect(A, B) $subset A
    finite_set_size(intersect(A, B)) <= finite_set_size(A)
    finite_set_size(union(A, B)) <= finite_set_size(A) + finite_set_size(B)

forall A, B finite_set:
    B $subset A
    =>:
        finite_set_size(set_minus(A, B)) = finite_set_size(A) - finite_set_size(B)

forall a, b N:
    a <= b
    =>:
        finite_set_size(closed_range(a, b)) = b - a + 1
        finite_set_size(range(a, b)) = b - a
```

The boundary is semantic: replacing `finite_set` by arbitrary `set` makes
`finite_set_size(...)` ill-defined. The rule does not attempt to prove an
unknown set finite merely because it appears in a cardinality expression.

Runnable examples for these families are indexed in [Litex
Examples](Examples.md). Keeping that evidence map there avoids duplicating a
second, quickly stale list of implementation files in the language reference.

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

Equality routes depend on the outer shape of both sides. The following table
records the public behavior; later subsections expand the power, logarithm,
aggregate, and remainder rows.

| Shape | Recognized equality route |
|---|---|
| Same or known-equal objects | Reflexivity, symmetry, transitivity, equality-chain lookup, replacement of known-equal immediate subobjects, and calculation or rational-expression normalization. Equality is also obtained from both weak-order directions over an ordered numeric carrier. |
| Additive and multiplicative cancellation | `x = y` gives `x-y=0`; `a*b=0` together with either nonzero factor gives the other factor equal to zero; a known `a+b=c` gives `a=c-b`, in either summand order. |
| Division | From `a/b=c` and `b!=0`, Litex proves `a=c*b`. From `a=b*c` and `b!=0`, it proves `a/b=c`. The displayed multiplier and divisor positions must match; the rule does not silently commute a product first. |
| Absolute value and square root | A known sign selects `abs(x)=x` or `abs(x)=-x`; `abs(x)=0` gives `x=0`; even powers may replace a real base by its absolute value. Square-root rules include the principal-root square, special values, product/quotient laws under their domains, and `sqrt(a^2)=a` when `a>=0`. |
| Powers and logarithms | Zero/one, exponent addition, iterated power, product power, negative exponent, roots, and inverse logarithm/power shapes are supported only in the carrier branches listed below. |
| Remainder and divisibility | Special residues, Euclidean-remainder uniqueness, compatible nested moduli, and congruence under matching `+`, `-`, and `*` operands. `gcd(a,b)` divides both inputs, and `(a*b)%a=(a*b)%b=0` when the objects are well-defined. |
| Set and cardinality objects | Union/intersection/difference algebra, intersection reduction from a known subset, cardinality of products, differences, unions and power sets, and empty-set equality from emptiness or zero finite cardinality. |
| Tuples, Cartesian products, and matrices | Tuple reconstruction from Cartesian membership; tuple/cart equality from equal dimensions and projections; canonical `general_cart` expansion; matrix positive-power base and successor equations. |
| Functions and materialized definitions | Application equations, alpha-equivalent anonymous functions, pointwise `$fn_eq_in`/`$fn_eq`, same-signature function-set equality, registered antisymmetry, and equality of materialized template or struct values when their resolved objects agree. |
| Finite aggregates and reductions | Empty, singleton, endpoint, split, insertion/removal, distribution, congruence, and supported reindexing rules described under [Powers, logarithms, sums, products, and remainder](#powers-logarithms-sums-products-and-remainder). |

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

forall a, b, c R:
    b != 0
    a / b = c
    =>:
        a = c * b

forall a, b R:
    a * b = 0
    a != 0
    =>:
        b = 0
```

Structural equality is recursive but bounded. Matching constructors descend
to their immediate children; binder-bearing objects compare alpha-equivalent
binders rather than the printed parameter names. This does not equate two
different mathematical presentations merely because an external theorem
could connect them. For functions, use `$fn_eq_in` or `$fn_eq` when pointwise
equality is the intended interface.

#### Not-equality routes

`a != b` is a positive fact with its own rules; it is not produced merely
because equality verification failed.

| Group | Recognized route |
|---|---|
| Resolution and symmetry | Distinct resolved numeric values, including objects whose known equality representatives resolve to such values; the reverse known fact `b!=a`; and displayed sets with different structural lengths. Native `e`, `pi`, and `i` have their reviewed distinctness/nonzero facts. |
| Order and membership separation | Any known strict real order proves disequality. A value above a known positive lower bound is nonzero. Membership of one object and known nonmembership of the other in the same set prove the objects distinct. A nonempty set is not `{}`. |
| Addition and subtraction | `a!=b` gives `a-b!=0`, and `a-b!=0` gives `a!=b`. Likewise `a!=-b` gives `a+b!=0`, while a nonzero sum gives the corresponding operand-versus-negation fact. The immediate operand positions must match. |
| Products and quotients | Two known nonzero real factors give a nonzero product; a known nonzero product gives both factors nonzero. A well-defined quotient is nonzero from a nonzero numerator; its denominator obligation was already checked. |
| Powers, roots, and absolute value | A supported well-defined power is nonzero from a nonzero base, and positive-base power branches are intrinsically nonzero. `abs(x)!=0` follows from `x!=0`; `sqrt(x)!=0` requires `x>0`, not merely `x>=0`. |
| Sums of real squares | Either nonzero component, or the known two-branch component-nonzero disjunction, gives `a^2+b^2!=0` (also for the matching `a*a+b*b` shape). Conversely, the supported disjunction rule exposes that at least one component is nonzero. |
| Native positive values | Well-defined `exp(x)` and `factorial(n)` are nonzero. Dedicated complex-modulus, sign, and trigonometric nonzero rules use the domains and canonical sign intervals described in their object sections. |

```litex
forall a, b R:
    a != b
    =>:
        a - b != 0

forall a, b R:
    a * b != 0
    =>:
        a != 0 and b != 0

forall a, b R:
    a != 0
    =>:
        a^2 + b^2 != 0
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

Every ordered comparison requires both operands to be real; membership in `C`
alone never supplies an order. The order layer recognizes these contracts:

| Group | Recognized premises and consequences |
|---|---|
| Totality and complements | For reals, the trichotomy permutations and the complementary pairs `<`/`>=`, `>`/`<=`, `<=`/`>=` are exhaustive. Known equality or strict order weakens to `<=`/`>=`; a known negated comparison can supply its exact complementary comparison. |
| Transitivity and differences | Strict/weak real comparisons compose through a shared middle term. `a<=b` is equivalent to `0<=b-a`, and similarly for `<`; the corresponding shifted addition/subtraction forms are recognized. |
| Integer discreteness | For integers, `a<b` gives `a+1<=b`, `a<=b-1`, and `b-a>=1`; `a<b+1` gives `a<=b`. Bounds `n<=x<n+1` or `n<x<=n+1` isolate `n` or `n+1`. |
| Addition and subtraction | Componentwise weak inequalities add; any strict component makes the result strict. Common translation preserves order. Subtraction uses the opposite ordering on the subtrahend. Nonnegative or positive increments give the corresponding one-sided bounds. |
| Products | Same weak signs give a nonnegative product; same strict signs give a positive product; opposite signs give a negative/nonpositive product. Multiplying an inequality preserves its direction for a positive factor and reverses it for a negative factor; weak zero factors only support weak conclusions. |
| Quotients | A positive denominator preserves order and supports cross-multiplication. A negative denominator reverses order. Sign conclusions require the numerator sign and a strictly positive denominator. Rules such as `a<=b/c` consume a positive `c` and the matching multiplied inequality. |
| Powers | Positive real bases with positive real/rational exponent preserve and reflect order. Positive natural exponents are monotone on nonnegative bases; odd exponents are monotone on all reals; even exponents compare absolute values. Negative integer exponents reverse positive-base order. |
| Roots, logarithms, and absolute value | `sqrt(x)` is nonnegative, and positive for positive `x`. A logarithm with base `>1` preserves strict order; a base strictly between `0` and `1` reverses it. Absolute value supplies direct, triangle, and reverse-triangle bounds, including `abs(sum(...,f)) <= sum(...,fn(index Z) R {abs(f(index))})` and the analogous finite-set sum under the matching index/carrier facts. |
| Finite aggregates and extrema | Pointwise weak/strict order on the relevant index set gives sum order. A nonnegative finite-set summand is at most the total. Finite-set extrema bound every member. Finite subset inclusion bounds cardinality, and union cardinality is at most the sum. |
| Native ordered objects | Floor and ceiling preserve weak order but not strict order. `min` and `max` expose argument bounds and componentwise monotonicity. Native `exp`/`ln` and trigonometric order use the dedicated sections below; complex modulus uses the [complex scalar contract](#complex-scalars-beta-preview). |

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

forall a, b, c R:
    a < b
    0 < c
    =>:
        a * c < b * c
        a / c < b / c

forall a, b R+:
    a < b
    =>:
        log(2, a) < log(2, b)
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

### Trigonometric rules

The symbolic trigonometric interface recognizes the following exact families:

| Family | Recognized laws and required domains |
|---|---|
| Core identities | Values at `0` and `pi / 2`, sine and cosine addition and difference formulas, the unit-circle identity, and `tan(x)=sin(x)/cos(x)` or `cot(x)=cos(x)/sin(x)` when the denominator is known nonzero. |
| Symmetry and angles | Odd/even parity, double-angle and cofunction formulas, supported integral and half-integral multiples of `pi`, shifts by `pi` and `pi/2`, and period `2*pi` for sine/cosine or `pi` for tangent/cotangent when defined. |
| Bounds and signs | `-1 <= sin(x), cos(x) <= 1`, `3 < pi < 4`, and the standard sign intervals for sine, cosine, tangent, and cotangent. Open-domain bounds remain necessary for tangent and cotangent. |
| Local order | Sine is monotone on `[-pi/2, pi/2]`, cosine on `[0, pi]`, tangent on `(-pi/2, pi/2)`, and cotangent in the reverse direction on `(0, pi)`. |

These are exact symbolic rules, not numerical approximation. Unlisted special
angles, inverse or complex trigonometry, continuity, and analytic definitions
need explicit source facts or library interfaces.

### Native numeric function rules

| Family | Recognized laws and required domains |
|---|---|
| `exp` and `ln` | `exp(0)=1`, `ln(1)=0`, `exp(x)=e^x`, their inverse laws, and the usual addition/product identities. `exp` maps `R` to `R+` and preserves and reflects order and equality. `ln` has the corresponding behavior on `R+` and agrees with `log(e,x)`. |
| `sign` | Returns `-1`, `0`, or `1`; is odd, multiplicative, and weakly monotone; characterizes zero and nonzero inputs; and satisfies `sign(x)*abs(x)=x`. |
| `factorial` | Maps `N` to `N+`, evaluates finite natural inputs, exposes the successor recurrence, preserves weak order, is strictly increasing past the `0! = 1!` boundary, and gives divisibility from an earlier to a later factorial. |
| `floor` and `ceil` | Return integers, expose their characteristic bounds, preserve weak order, commute with integer translation, and are dual under negation. |
| `min` and `max` | Select an argument from a known comparison, bound both arguments, preserve componentwise weak order, and satisfy the usual commutative, associative, idempotent, and absorption laws. |
| `gcd` and `lcm` | Are symmetric on their domains; `gcd` divides both integer inputs; `lcm` is nonnegative, has the expected common-multiple bounds, and satisfies `lcm(a,b)*gcd(a,b)=abs(a*b)` when the pair is not both zero. |

Symbolic transcendental expressions are not decimal approximations. Every law
still requires its ordinary well-definedness conditions.

### Powers, logarithms, sums, products, and remainder

Power rules first select one supported carrier branch. Complex bases support
natural exponents and, when nonzero, integer exponents. Arbitrary real
exponents require a positive real base; zero is additionally accepted for a
positive real exponent. Integer and positive-natural exponent branches retain
their narrower algebraic carriers. Positivity, monotonicity, roots,
logarithms, and even-power absolute-value rules remain real-only.

| Family | Exact public laws, subject to well-definedness |
|---|---|
| Power identities | `a^0=1`, `a^1=a`, `1^x=1`, and `0^x=0` for positive `x`; `a^(m+n)=a^m*a^n`; `(a^m)^n=a^(m*n)`; `(a*b)^x=a^x*b^x`; `a^(-n)=1/a^n` for nonzero `a` and positive-natural `n`. The exponent-addition, iterated-power, and product-power laws use the carrier branches stated above. |
| Roots and inverse powers | `(sqrt(x))^2=x` for `x>=0`; `sqrt(a^2)=a` for `a>=0`; product and quotient roots require nonnegative inputs and a positive denominator. `x^(1/n)=z` is recognized from `x=z^n`, `n in N+`, and `z>=0`; equal nonzero integer powers of positive bases can recover equality of the bases. |
| Logarithms | With valid positive arguments and a positive base unequal to one: `log(a,1)=0`, `log(a,a)=1`, product, quotient, reciprocal, and power laws; `log(a,a^b)=b`; `a^c=b` and `log(a,b)=c` are inverse shapes; change of base and powered-base formulas are supported when their denominators are well-defined. |
| Integer-range `sum`/`product` | Empty and singleton ranges; last-term recurrence; adjacent partition; constant, pointwise congruence, addition/subtraction/negation and scalar laws; sum shift-reindexing. Products have the analogous singleton, last-term, and adjacent-partition laws. Bounds are closed integer endpoints, and pointwise facts are required on exactly the consumed range. |
| `finite_set_sum` | Empty/displayed/closed-range expansion, constant and pointwise congruence, insertion or disjoint union, pointwise addition, scalar distribution, Cartesian double-sum/Fubini, unique-cover substitution, and bijective re-enumeration. |
| `finite_set_product` | Empty/displayed/closed-range expansion, insert/remove, constant and pointwise congruence, pointwise multiplication, and bijective substitution. |
| `reduce` | Ascending left-fold evaluation for literals; empty range returns the seed; nonempty ranges consume the first or last value; adjacent ordered partition; order-preserving interval translation; pointwise congruence; additive seed `0` and multiplicative seed `1` bridge to `sum` and `product`. |
| `finite_set_reduce` | Empty set returns the seed; displayed-set enumeration, insertion, disjoint union with one seed, closed-range ascending enumeration, congruence, and bijective substitution require an associative-commutative operation. Additive seed `0` and multiplicative seed `1` bridge to the finite-set aggregates. |
| Remainder | `0%m=0` for nonzero integer `m`; `x%1=0`; `1%k=1` for `k>=2`; Euclidean uniqueness; negation normalization; power congruence; matching `+`, `-`, `*` congruence; same-modulus nesting; and `(a%m)%d=a%d` when positive `d` divides positive `m`. |

For positive real factors, a real exponent distributes over multiplication in
either equality direction:

```litex
forall a, b R+, x R:
    (a * b)^x = a^x * b^x
```

The positivity condition is semantic, not cosmetic: this rule does not admit
zero or negative factors with an arbitrary real exponent.

Aggregate rules consume the displayed function and index shape. They do not
silently replace a summand by an extensionally equal function outside the
relevant domain; provide `$fn_eq_in` or the exact pointwise universal. The
subtraction rule also requires one common additive carrier among `Z`, `Q`,
`R`, and `C`, so it does not totalize natural-number subtraction.

```litex
have f fn(index Z) R
have g fn(index Z) R

forall m, n Z:
    m <= n
    =>:
        sum(m, n, fn(difference_index Z) R {f(difference_index) - g(difference_index)}) = sum(m, n, fn(minuend_index Z) R {f(minuend_index)}) - sum(m, n, fn(subtrahend_index Z) R {g(subtrahend_index)})

forall X finite_set, p, q fn(x X) Z:
    finite_set_product(X, fn(x X) Z {p(x) * q(x)}) = finite_set_product(X, p) * finite_set_product(X, q)
```

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

Membership rules are directional introduction or elimination rules. A known
constructor fact is not interchangeable with every logically equivalent
presentation.

| Target family | Recognized construction or elimination |
|---|---|
| Standard numeric carriers | Literal classification; the inclusion chain among signed/nonzero `N`, `Z`, `Q`, `R`, and `C`; arithmetic closure at the narrowest supported carrier; refinement from integer/real carrier plus known sign; nonmembership for resolved literals; `floor`/`ceil` in `Z`, `sign` in `Z`, `factorial(N)` in `N+`, and numeric carriers for gcd/lcm/extrema/aggregates. |
| Displayed sets and builders | Equality with one displayed element introduces membership, and disequality from every element introduces nonmembership. Builder membership requires base membership and all instantiated defining facts; stored builder membership exposes those facts. A builder over a finite base is finite. |
| Binary set operations | Either-side membership introduces union membership; intersection requires both sides; difference requires left membership and right nonmembership. Corresponding stored intersection/difference facts expose their component facts. |
| Family and image operators | `big_union` uses a member-set witness; `replacement` uses its functional relation witness; `fn_range` uses a well-defined application. Stored membership exposes the existential source described in the object section. |
| Ranges and intervals | `range(a,b)` uses integer `a<=i<b`; `closed_range(a,b)` uses `a<=i<=b`. Real intervals require real membership plus their open/closed endpoint bounds. Half-infinite intervals impose only their displayed endpoint bound. |
| Power sets and inclusions | `A $subset B` introduces `A $in power_set(B)`. A displayed set or builder belongs to a power set after its elements/base are contained. One directly known inclusion can lift an element into the target set. |
| Products and indexed objects | Tuple membership checks every component against the corresponding Cartesian factor. General Cartesian membership checks a function into `big_union(S)` plus every indexed factor. Sequence and matrix literals check length/shape and every entry. Projection and index access inherit the selected carrier. |
| Functions and structs | A known function signature or matching anonymous signature supplies function-set membership and the instantiated return carrier of applications. Struct membership checks the named carrier and instantiated equivalent facts. A set-valued function/template definition may be unfolded once for membership. |

The type-predicate layer classifies set structure separately:

| Predicate | Automatic positive cases | Automatic negative/boundary cases |
|---|---|---|
| `$is_nonempty_set(S)` | Standard numeric sets; nonempty displays; every power set; ordered nonempty ranges; a union with a nonempty side; Cartesian/function/sequence/matrix sets with the required nonempty factors or codomain; an equal known-nonempty structural set; positive finite cardinality. | Equality with `{}` and finite cardinality zero imply not nonempty. Nonemptiness is never inferred for an arbitrary declared `set`. |
| `$is_finite_set(S)` | Displays, integer ranges, builders over finite bases, finite-domain function ranges, finite unions/intersections/differences/power sets, and Cartesian products of finite factors. | An infinite set minus a finite set remains infinite. No rule makes an arbitrary set finite from its use in another expression. |
| Empty structure | Empty display; `closed_range(a,b)` when `b<a`; `range(a,b)` when `b<=a`; equality with `{}`; finite cardinality zero. | Ordered endpoints in the opposite direction establish the matching nonempty range. |
| `$is_tuple` / `$is_cart` | Tuple syntax and known tuple objects; `cart(...)` and `cart_dim(...)` syntax. | A similarly printed ordinary set does not become a tuple or Cartesian object without the structural fact. |

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

forall a, b Z:
    a <= b
    =>:
        $is_nonempty_set(closed_range(a, b))
        $is_finite_set(closed_range(a, b))
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

| Interface | Definition or derived builtin consequence |
|---|---|
| `A $subset B` / `B $superset A` | Dual spellings of the same inclusion. Reflexivity, structural constructor containment, one-edge membership lifting, and subset chains are supported. Componentwise Cartesian inclusions, integer range into its numeric carrier, real interval into `R`, `fn_range(f)` into its codomain, and union containment from both operands have dedicated shapes. Proper relations unfold to ordinary inclusion plus inequality. |
| `$fn_eq_in(f,g,S)` | Pointwise equality `forall x S => f(x)=g(x)` on exactly `S`. Aggregate congruence can consume this registered interface. |
| `$fn_eq(f,g)` | Exact pointwise equality over compatible function carriers. It may use the stored pointwise universal plus matching domains/signatures, or mutual function-space membership with pointwise equality. |
| `$injective(A,B,f)` | Definition route: members of `A` with equal images are equal. For finite `A`, injectivity gives `finite_set_size(fn_range(f)) = finite_set_size(A)`. |
| `$surjective(A,B,f)` | Definition route: each member of `B` has a preimage in `A`. A finite source makes the codomain finite and gives `finite_set_size(B) <= finite_set_size(A)`. |
| `$bijective(A,B,f)` | Definition route combines injectivity and surjectivity. For finite source and target, it preserves cardinality; it also enables finite aggregate reindexing. |

Here the definition proofs register the mapping facts, after which the
cardinality rules consume them directly:

```litex
have fn mapping_identity(x {1, 2, 3}) {1, 2, 3} = x

forall x1, x2 {1, 2, 3}:
    mapping_identity(x1) = mapping_identity(x2)
    =>:
        x1 = mapping_identity(x1) = mapping_identity(x2) = x2
by def $injective({1, 2, 3}, {1, 2, 3}, mapping_identity)

claim:
    ? forall y {1, 2, 3}:
        exist x {1, 2, 3} st {y = mapping_identity(x)}
    y = mapping_identity(y)
    witness exist x {1, 2, 3} st {y = mapping_identity(x)} from y
by def $surjective({1, 2, 3}, {1, 2, 3}, mapping_identity)
by def $bijective({1, 2, 3}, {1, 2, 3}, mapping_identity)

finite_set_size(fn_range(mapping_identity)) = finite_set_size({1, 2, 3})
```

The finite mapping rules require the exact finite-set and mapping facts; they
do not infer finiteness from a cardinality expression and do not select an
inverse function globally.

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

### Existential and disjunctive builtin results

`exist`, `exist!`, and `or` have dedicated verifiers. They recognize exact
canonical fact shapes rather than treating an equivalent formula as an atomic
rule target.

| Existential shape | Required known information |
|---|---|
| A real comparison witness | Every non-witness operand is real. The canonical one- or two-parameter body compares the witness by `=`, `!=`, `<`, `>`, `<=`, or `>=`; the witness may occur on either side. |
| `exist x A st {x $in A}` | `$is_nonempty_set(A)`. This proves existence but does not install a global choice object. |
| Rational representations | `q $in Q`. Supported forms are an integer numerator with positive-integer denominator, an integer numerator with nonzero-integer denominator, and the reduced positive-denominator form. The reduced form may be `exist` or `exist!` and may state reducedness by `gcd(p,d)=1` or the canonical common-positive-divisor condition. |
| `exist! q Z st {a = d*q + a%d}` | `a $in Z` and `d $in N+`. Uniqueness is part of this exact Euclidean-quotient rule. |
| `exist k Z st {a=b*k}` | `a,b $in Z`, `b!=0`, and `a%b=0`. |
| `exist n N+ st {1/n < epsilon}` | `epsilon $in R+` (Archimedean reciprocal bound). |
| `exist q Q st {a<q<b}` / `exist r R st {a<r<b}` | `a,b $in R` and `a<b` (rational or real density). |
| Integer interval witness | `a,b $in R` and `b-a>1` for `exist c Z st {a<c<b}`, or `b-a>=1` for the weak-endpoint form. |
| Greatest natural member | The body has the canonical membership-and-upper-bound shape, while `S` is finite, nonempty, and `S $subset N`. |

```litex
forall epsilon R+:
    exist n N+ st {1 / n < epsilon}

forall a, b R:
    a < b
    =>:
        exist q Q st {a < q < b}
        exist r R st {a < r < b}

forall a, b R:
    a < b
    b - a > 1
    =>:
        exist c Z st {a < c < b}

forall a Z, d N+:
    exist! q Z st {a = d * q + a % d}
```

Outside those canonical builtin shapes, ordinary existential proof routes
still apply: cite a known existential, instantiate a known `forall`, use
`witness`, or prove an `exist` plus its generated uniqueness universal to
obtain `exist!`. A direct builtin for `exist` never upgrades an arbitrary
equivalent spelling to `exist!`.

The `or` verifier recognizes these exhaustive forms:

| Disjunction | Requirement |
|---|---|
| `P or not P` | Two exactly complementary atomic facts. |
| Real order alternatives | Real operands; complementary strict/weak pairs, trichotomy permutations, or equality plus strict order when the matching weak comparison is already known. |
| `abs(x)=x or abs(x)=-x` | Canonical two-branch absolute-value split. |
| Complete residues | Every canonical equality `n % k = r` for `r=0,...,k-1`, with a positive literal/canonical modulus shape. |
| Integer successor tail | Known `x,base $in Z` and `x>=base`; the branches list consecutive equalities from `base` followed by the matching strict tail. |
| `a=0 or b=0` | `a,b $in R` and known `a*b=0` (either product order). |
| `a!=0 or b!=0` | A known real square-sum nonzero fact in the supported `a^2+b^2` or `a*a+b*b` shape. |
| `not A or B` | Classical implication packaging: under a temporary local assumption `A`, the ordinary atomic verifier proves `B`. |

```litex
forall a, b R:
    a * b = 0
    =>:
        a = 0 or b = 0

forall a, b R:
    a <= b
    =>:
        a = b or a < b

forall x R:
    abs(x) = x or abs(x) = -x
```

Branch order is flexible only where the matcher explicitly treats it as a
permutation. Adding unrelated branches, changing the bound pattern, or hiding
the operands behind a user predicate can make the direct builtin route
`unknown`; use an ordinary theorem or proof block for that presentation.

### Reduced rational fractions (preview)

Litex has a narrow builtin for the standard reduced-fraction representation of
a rational number with positive denominator. The public named form is:

```litex
have a Q
by thm rational_has_unique_reduced_fraction(a)
exist! p Z, q N+ st {a = p / q, gcd(p, q) = 1}
```

The theorem name is reserved, bare, and has arity one. A non-`Q` argument,
extra argument, or qualified call is rejected without storing a conclusion.
The existential is not proved implicitly: callers must use the explicit
theorem interface. This rule recognizes the displayed representation; it is
not a general gcd construction and does not replace checked source-level
arithmetic libraries.

---

## Builtin Inference

After an accepted or trusted fact is stored, builtin inference may add routine
consequences to the same environment. These consequences become ordinary
known information for later statements.

Inference may chain through newly inferred facts, but it stops cyclic
re-expansion. This supports routine carrier, definition, and structure
consequences without promising arbitrary logical closure.

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
| Equality | Numeric values, simple linear solved values, `u-v=0` equality, tuple/cart/set-builder/sequence/matrix/function structure, and positive-real membership transported from a known power side. |
| `$fn_eq(f,g)` | Ordinary object equality `f=g`, so known-equality congruence can use it. `$fn_eq_in` alone has no such global consequence. |
| Positive concrete or builtin predicate | Instantiated parameter-type and defining clauses. Proper inclusion exposes inclusion plus inequality; `$prime` exposes its lower bound and trial-divisor universal; `$coprime(a,b)` exposes `a != 0 or b != 0` and `gcd(a,b)=1`; `$dvd(x,y)` exposes `x % y = 0` and an integer multiple witness; mapping properties expose their exact definitions. Abstract predicates have no clauses to expose. |
| Membership | Constructor-specific carrier, shape, bound, component, disjunction, or existential information listed below. |
| `$is_cart(C)` | The structural lower bound `2 <= cart_dim(C)`. Other positive/negative type predicates have no general inference branch. |
| Subset or superset | One fresh universal membership consequence in the corresponding direction. A builder on the subset side skips this eager universal because builder membership already exposes its domain and filters. |
| Proper inclusion | Through its builtin definition: ordinary inclusion and set inequality. |
| Order against a resolved concrete bound | Selected sign information, including the equivalent comparison after multiplying both sides by `-1` when that normalized shape is supported. |
| `exist!` | A universal saying any two complete witness tuples satisfying the body are componentwise equal. |
| `not exist` | The corresponding universal De Morgan negation when the body shape is supported. |
| `not forall` | An existential counterexample containing the instantiated domain facts and negation of the conclusions, when those facts can be represented in an existential body. |
| Equality/order chain | Atomic consequences from its transitive closure, followed by the ordinary inference for each consequence. |

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
| `x $in {a}` / `x $in {a, b, ...}` | Atomic equality for a singleton; otherwise the finite equality disjunction. Empty display adds nothing. |
| `x $in union(A,B)` | `x $in A or x $in B` |
| `x $in intersect(A,B)` | Both component memberships |
| `x $in set_minus(A,B)` | `x $in A` and `not x $in B`; a singleton right side also yields the matching disequality |
| `x $in big_union(F)` | `exist A F st {x $in A}` |
| `y $in replacement(P,A)` | `exist x A st {$P(x,y)}` |
| `y $in fn_range(f)` | Membership in the declared codomain plus an existential preimage carrying every instantiated domain condition and `y=f(args)` |
| `A $in power_set(B)` | `A $subset B` |
| `x $in cart(A, B, ...)` | Tuple shape, dimension, and coordinate memberships |
| `f $in general_cart(I,S,g)` | `f $in fn(index I) big_union(S)`, `$is_choice_function_for(I,S,g,f)`, and its pointwise factor-membership universal |
| `x $in range(a, b)` | Integer membership and half-open bounds |
| `x $in closed_range(a, b)` | Integer membership and closed bounds |
| `x` in a real interval | Real membership and endpoint bounds |
| `x $in {y S: filters}` | `x $in S` and instantiated filters |
| Function/sequence/matrix type membership | A callable function interface; sequence and matrix sets are expanded to their corresponding function set, while matrix metadata also records its entry carrier and dimensions. |
| `x $in &Struct<...>` | Instantiated field-carrier and equivalent facts; literal tuples additionally expose component projections. |

Membership inference also transports through concrete equal set
representatives and through one checked set-valued function or template
definition. More deeply hidden membership facts may need to be stated and
verified explicitly.

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
interface. A membership goal may use one directly known inclusion, but Litex
does not automatically materialize every lifted membership or compute an
unbounded transitive subset closure.

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

### Preview labels

A heading marked **preview** documents behavior that is implemented and tested
but whose surface syntax or exact contract may still change. The label stays
beside the canonical explanation instead of being repeated in a separate
inventory that can drift out of sync.

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

Every unskipped `litex` fenced block in this manual is intended to be
self-contained and is run by
`cargo test --release run_docs_markdown_files -- --nocapture`. A skipped
`litex` block carries an adjacent `litex:skip-test` marker and is deliberately
invalid; a `text` block is either another deliberately invalid example, a
non-executable shape, or an output sketch. The surrounding paragraph states
the intended reading and, for failures, whether checking reaches `unknown` or
`error`.

The language implementation is the final source of truth when this manual and
the runner disagree. Such disagreement is a documentation or diagnostic bug
to fix, not a reason to reinterpret a failed example silently.
