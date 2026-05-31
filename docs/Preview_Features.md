# Preview Features

Jiachen Shen and The Litex Team, 2026-05-08. Email: litexlang@outlook.com

Preview features are usable experiments. They are implemented enough to try, but their syntax and semantics may still change. For stable language concepts, read the [Manual](https://litexlang.com/doc/Manual) first.

New preview-related behavior is **appended** under [Recent additions](#recent-additions-append-only) as it lands. The struct material below describes the explicit struct-view redesign: struct definitions name tuple/cartesian-product shapes, and field access must say which struct view is being used.

## Recent additions (append-only)

Short pointers only; fuller syntax and semantics live in the in-repo [Manual](Manual.md) where noted.

### Stoppable imports (2026-05)

`stop import Name` keeps an imported module registered but removes it from ordinary automatic verification. This is useful when a loaded std module has many known facts and `forall` facts that should not be searched for later goals. Std imports must use the std folder name as the module name. Re-importing the same std module is idempotent and re-enables the module if it was stopped; `clear` stops all currently imported modules. Explicit citations such as `by thm Name::theorem(...)` can still cite a stopped module.

### Named theorem calls with `thm` (2026-05)

`thm name:` records a verified `forall` theorem under an explicit name. `thm name1, name2:` records the same theorem under multiple names. Calling `by thm name(args...)` checks the argument types and domain facts, then stores the instantiated then-facts. Defining a theorem does not add it to ordinary automatic forall-pattern matching; use `by thm` when you want the named theorem.

```litex
thm one_succ, succ_one:
    prove:
        forall x R:
            x = 1
            =>:
                x + 1 = 2
    x + 1 = 1 + 1 = 2

by thm one_succ(1)
1 + 1 = 2

by thm succ_one(1)
1 + 1 = 2
```

### Strategy registration with `strategy` (2026-05)

`strategy name:` records a verified `forall` rule for future strategy-driven proof search. The `prove:` block has the same shape as `thm`, but the `forall` conclusion must contain exactly one atomic fact. A successfully defined strategy is enabled immediately for that conclusion predicate, as if `use strategy name` had been run. The proved `forall` is also stored as an ordinary known fact, so later proofs can use normal `forall` instantiation even if strategy search is stopped or another strategy is active for the same predicate. `use strategy name` can still re-enable a stopped strategy, and `stop strategy name` records that the strategy should be stopped for the same predicate.

```litex
prop is_one(x R):
    x = 1

strategy prove_is_one:
    prove:
        forall x R:
            x = 1
            =>:
                $is_one(x)

$is_one(1)
stop strategy prove_is_one
use strategy prove_is_one
```

### Component uniqueness inferred from `exist!` (2026-05)

When an `exist!` fact is recorded, Litex stores a generated uniqueness `forall`. For multiple witness parameters, the stored theorem now concludes component equalities, so it can be used either as one `and` fact or as split then-facts later.

```litex
abstract_prop p(a, b)

know exist! a, b R st {$p(a, b)}

forall a1, b1, a2, b2 R:
    $p(a1, b1)
    $p(a2, b2)
    =>:
        a1 = a2
        b1 = b2
```

### Exact rational `eval` results (2026-05)

`eval` can now keep exact rational results when a concrete division does not terminate as a decimal. The same exact arithmetic is used inside matrix `eval`, so matrices with rational entries can be added, scaled, and multiplied.

```litex
eval 1 + 1 / 3
eval [[1 / 2, 1 / 3], [0, 1]] ** [[1, 0], [1 / 6, 1 / 2]]
```

### Square-root builtin facts (2026-05)

Builtin equality can prove square-root product and quotient steps when the factors are in the principal-root domain, such as `sqrt(x) = sqrt(a) * sqrt(b)` from `x = a * b`, and `sqrt(x) = sqrt(a) / sqrt(b)` from `x = a / b` with `b > 0`. The same group also handles equal square-root arguments and `sqrt(a^2) = a` for nonnegative `a`. Builtin order can prove `sqrt(x) >= 0` from `x >= 0`, plus weak and strict monotonicity of `sqrt` on nonnegative reals.

```litex
prove:
    sqrt(452) = sqrt(4 * 113) = sqrt(4) * sqrt(113) = 2 * sqrt(113)

forall a, b R:
    a >= 0
    b > 0
    =>:
        sqrt(a / b) = sqrt(a) / sqrt(b)

forall a, b R:
    a >= 0
    b >= 0
    a <= b
    =>:
        sqrt(a) <= sqrt(b)
```

### Numeric quotient non-integer detection (2026-05)

When checking `not x $in Z`, a resolved numeric division `a / b` can be rejected as an integer by the existing modulo evaluator: if `a` and `b` resolve to integer numbers, `b != 0`, and `a % b != 0`, Litex proves the quotient is not in `Z`.

```litex
prove:
    1 / 6 $in Q
    6 / 3 $in Z
    not 1 / 6 $in Z
    not 2 / 6 $in Z
```

### `have fn as algo` (2026-05)

`have fn as algo f(...) ...` defines the ordinary function facts first, then automatically generates and verifies the corresponding `algo f(...)`. This is available for direct equality, `by cases`, and `by induc` function definitions. Generated algo cases currently require atomic case conditions.

```litex
prove:
    have fn as algo self_max(x, y R) R by cases:
        case x > y: x
        case x <= y: y

    eval self_max(5, 3)
    self_max(5, 3) = 5
```

### Function application return membership (2026-05)

If a function application is well-defined and the function's known return set is `R`, Litex can verify that application belongs to `R`. This covers builtin objects such as `sqrt(2)` and declared functions such as `sin(0)` after loading `Trig`.

### Real interval objects (2026-05)

Real intervals are available as `oo(a, b)`, `oc(a, b)`, `co(a, b)`, and `cc(a, b)` for open/open, open/closed, closed/open, and closed/closed endpoints. Half-infinite real intervals use one finite endpoint: `info(a)` for `(-infinity, a)`, `infc(a)` for `(-infinity, a]`, `oinf(a)` for `(a, +infinity)`, and `cinf(a)` for `[a, +infinity)`.

The endpoints must be well-defined real objects. The verifier does not require `a < b` for the two-sided interval object itself. Membership unfolds to real membership plus endpoint bounds; for example, `x $in oc(a, b)` infers `x $in R`, `a < x`, and `x <= b`, and those same facts can prove `x $in oc(a, b)`. For half-infinite intervals, `x $in cinf(a)` infers `x $in R` and `a <= x`. Non-emptiness is checked separately: `cc(a, b)` is nonempty from `a <= b`, while `oo(a, b)`, `oc(a, b)`, and `co(a, b)` are nonempty from `a < b`; half-infinite real intervals are nonempty when their finite endpoint is well-defined.

These intervals are continuous real sets. They are separate from integer `range` and `closed_range`, so they do not support `count`, `by for`, or `by closed_range as cases`.

### Dependent function parameter domains (2026-05)

Later function parameter domains may now cite earlier parameters, such as `fn(n N_pos, x closed_range(1, n)) R`. Function return sets remain non-dependent and cannot cite the function parameters. See **Manual — Function types and anonymous functions**.

### Templates (2026-05)

`template name<params: dom_facts>:` defines a parameterized family of objects or functions. The typical use case is when you want to define something uniformly for every set `s`, but `s` itself cannot be an ordinary function input because function inputs must range over a concrete domain object, not over a condition like `$is_set(s)`. After instantiation, `\name<args>` materializes the corresponding object or function. For example, `template const_zero<s set: $is_nonempty_set(s)>: ...` can define a function `\const_zero<s>` on each chosen set `s`, and the instantiated function can be called as `\const_zero<R>(0)`.

### Restriction-only function calls (2026-05)

Multiple `$restrict_fn_in(f, ...)` facts are now remembered as candidate function domains. If `f` has no declared function set, function application well-definedness tries these restrictions. A set-valued RHS such as `$restrict_fn_in(f, s)` is treated as a unary real-valued restriction on `s`.

### Tuple equality from projections (2026-05)

Litex can now prove `t = (a, b, ...)` from tuple shape information and component equalities such as `tuple_dim(t) = 2`, `t[1] = a`, and `t[2] = b`. This also closes goals like `forall t cart(N, N): t = (t[1], t[2])`.

### Finite set count identities (2026-05)

Litex now knows more count identities for finite set operations, including `union`, `set_minus`, and `set_diff`. See **Manual — Counting members**.

### Singleton integer intervals infer equality (2026-05)

Membership in `range(a, b)` and `closed_range(a, b)` now records the element equality directly when the integer interval has exactly one value, such as `range(1, 2)` or `closed_range(1, 1)`. `by closed_range as cases` likewise records the single equality instead of a one-branch `or`. See **Manual — Builtin Inference — Ranges** and **Manual — Closed range as cases**.

### Enumerate integer interval membership (2026-05)

`by enumerate range: x $in range(lo, hi)` and `by enumerate closed_range: x $in lo...hi` expand known integer interval membership into equality cases. Half-open `range(lo, hi)` enumerates through `hi - 1`; `closed_range(lo, hi)` enumerates through `hi`.

### Natural membership from nonnegative integers (2026-05)

Builtin verification can now close `x $in N` from a verified integer expression `x` together with `x >= 0` / `0 <= x`, or together with `x > 0` / `0 < x`. For example, from `a, b $in Z` and `b - a >= 0`, it can verify `b - a $in N`. See **Manual — Builtin Verification Rules — Membership Rules**.

### Structured induction proof blocks (2026-05)

`by induc` and `by strong_induc` can now split their proof into a base block and a step block. Use `prove from n = base:` for the base case, `prove induc:` for ordinary induction steps, and `prove strong_induc:` for strong induction steps. See **Manual — Induction (`by induc`, `by strong_induc`)**.

### `by transitive_prop` (2026-05)

After you prove the standard associativity-shaped `forall` for a binary user-defined `prop` or `abstract_prop`, Litex records that predicate as **transitive**. Storing a same-predicate chain (e.g. `a $p b $p c`) also stores non-adjacent consequences such as `$p(a, c)`. See **Manual — Register a transitive predicate (`by transitive_prop`)**.

### `by reflexive_prop`, `by symmetric_prop`, `by antisymmetric_prop` (2026-05)

These register basic relation properties for user-defined props only, not builtin predicates. Reflexive registrations can close `$p(a, a)`. Symmetric registrations retry positive atoms with the registered argument permutation. Antisymmetric registrations can close `a = b` from `$p(a, b)` and `$p(b, a)`. See the corresponding Manual sections and `examples/01_proof_patterns/by_symmetric_reflexive_antisymmetric_prop.lit`.

### Explicit struct views (2026-05)

Struct usage is being redesigned around explicit views. Bare field access such as `P.x` is not part of the language. A field access must say which struct is being used, such as `&Point{P}.x` or `&Group(R){G}.op`.

The intended model is simple: `&Name(args)` is a set object, and `&Name(args){x}.field` is a named projection after proving `x $in &Name(args)`.

### Design Note: Object Meaning

When designing a new object form in Litex, the first questions are its surface shape and its well-definedness condition. Its mathematical behavior can then be supplied by builtin verification and inference rules. The AST records the shape, well-definedness checks that the expression is legal, and builtin rules explain how the object behaves in proofs.

## Struct Definitions

A `struct` definition declares a record-like shape. Each field has a name and a field type.

```litex
struct Point:
    x R
    y R
```

Structs may also have header parameters. The definition is stored and its field declarations are checked. In the explicit-view design, applying the struct header creates a set object such as `&Group(R)`.

```litex
abstract_prop group_property(s, zero, add, inv)

struct Group(s set):
    zero s
    add fn(x, y s) s
    inv fn(x s) s
    <=>:
        $group_property(s, zero, add, inv)
```

The `<=>:` block is still part of the definition record. Its body may refer to fields by their field names, as in the example above.

## Struct Objects

`&Name(args)` is a set object. It is read as a named set-builder whose base set is the Cartesian product of the instantiated field types.

For example:

```litex
struct Point:
    x R
    y R
```

`&Point` is the named struct set corresponding to `cart(R, R)`.

When there is no `<=>:` block, this struct set is nonempty as soon as every field type is nonempty. For example, `&Point` is nonempty because both fields range over `R`.

For a parameterized struct:

```litex
abstract_prop group_property(s, zero, add, inv)

struct Group(s set):
    zero s
    add fn(x, y s) s
    inv fn(x s) s
    <=>:
        $group_property(s, zero, add, inv)
```

`&Group(R)` is read as a named set-builder like:

```text
{ g $in cart(R, fn(x, y R) R, fn(x R) R) | $group_property(R, g[1], g[2], g[3]) }
```

The field names are a naming rule for tuple projections: `zero` means `g[1]`, `add` means `g[2]`, and `inv` means `g[3]`.

## Explicit Field Access

Field access is explicit:

```text
&Point{P}.x
&Group(R){G}.add
```

The prefix says how the object is being viewed. This avoids the ambiguity of bare `P.x`, because the same tuple could be viewed through different struct definitions. A bare field name is not enough: two structs may use the same field name for different tuple positions.

```litex
struct Point1:
    x R
    y R

struct Point2:
    y R
    x R

(1, 2) $in &Point1
(1, 2) $in &Point2
&Point1{(1, 2)}.x = 1
&Point2{(1, 2)}.x = 2
```

The well-definedness check for:

```text
&Group(R){G}.add
```

reduces to proving:

```text
G $in &Group(R)
```

When `G $in &Group(R)` is known, Litex also stores the facts carried by the struct view: each explicit field access and its corresponding tuple projection belong to the field type, and each `<=>:` fact is instantiated in both forms. One form replaces field names by explicit field accesses, and the other replaces them by tuple projections. When checking tuple membership in a struct object, Litex can use the tuple components directly for the `<=>:` facts.

Once that membership is available, the field access is only a named form of tuple projection:

```text
forall G &Group(R):
    &Group(R){G}.zero = G[1]
    &Group(R){G}.add = G[2]
    &Group(R){G}.inv = G[3]
```

If a parameter is declared with a struct object, the membership fact is available in the local context:

```text
forall G &Group(R):
    &Group(R){G}.add = &Group(R){G}.add
```

Here the parameter declaration provides `G $in &Group(R)`, so the field access is well-defined inside the body.

If the explicit view becomes visually heavy, use a macro to keep the proof readable. The macro does not change the meaning; it only abbreviates the required explicit view.

```text
macro s "&StandardTwoSimplex{s}"

forall s &StandardTwoSimplex:
    @s.x + @s.y + @s.z = 1
```

This is still the same as writing `&StandardTwoSimplex{s}.x`, `&StandardTwoSimplex{s}.y`, and `&StandardTwoSimplex{s}.z`.

## Current Boundaries

These syntax forms are intentionally unavailable:

- `fn(x &Point) Point`
- `P.x`
- `&Point(1, 2)`
- `by struct ...`

Use explicit struct objects and explicit field views instead:

```litex
struct Point:
    x R
    y R

have P &Point = (1, 2)
&Point{P}.x = P[1]
&Point{(1, 2)}.y = 2
```

This design does not add a new logical entity beyond tuples, Cartesian products, and set membership. It lets users introduce an equivalent naming rule for projections while keeping the struct view explicit.
