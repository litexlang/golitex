# Preview Features

Jiachen Shen and The Litex Team, 2026-05-08. Email: litexlang@outlook.com

Preview features are usable experiments. They are implemented enough to try, but their syntax and semantics may still change. For stable language concepts, read the [Manual](https://litexlang.com/doc/Manual) first.

New preview-related behavior is **appended** under [Recent additions](#recent-additions-append-only) as it lands. The struct material below describes the explicit struct-view redesign: struct definitions name tuple/cartesian-product shapes, and field access must say which struct view is being used.

## Recent additions (append-only)

Short pointers only; fuller syntax and semantics live in the in-repo [Manual](Manual.md) where noted.

### Dependent function parameter domains (2026-05)

Later function parameter domains may now cite earlier parameters, such as `fn(n N_pos, x closed_range(1, n)) R`. Function return sets remain non-dependent and cannot cite the function parameters. See **Manual — Function types and anonymous functions**.

### Templates (2026-05)

`template name<params: dom_facts>:` defines a one-result template around a supported `have ...` definition statement. Instantiating `\name{args}` checks that the arguments satisfy the template parameter types and domain facts, then materializes the body definition with the instantiated object as the defined result. Template instances can be ordinary objects, and if the body defines a function, the instance can be used as a function head such as `\const_zero{R}(0)`.

### Tuple equality from projections (2026-05)

Litex can now prove `t = (a, b, ...)` from tuple shape information and component equalities such as `tuple_dim(t) = 2`, `t[1] = a`, and `t[2] = b`. This also closes goals like `forall t cart(N, N): t = (t[1], t[2])`.

### Finite set count identities (2026-05)

Litex now knows more count identities for finite set operations, including `union`, `set_minus`, and `set_diff`. See **Manual — Counting members**.

### Singleton integer intervals infer equality (2026-05)

Membership in `range(a, b)` and `closed_range(a, b)` now records the element equality directly when the integer interval has exactly one value, such as `range(1, 2)` or `closed_range(1, 1)`. `by closed_range as cases` likewise records the single equality instead of a one-branch `or`. See **Manual — Builtin Inference — Ranges** and **Manual — Closed range as cases**.

### Natural membership from nonnegative integers (2026-05)

Builtin verification can now close `x $in N` from a verified integer expression `x` together with `x >= 0` / `0 <= x`, or together with `x > 0` / `0 < x`. For example, from `a, b $in Z` and `b - a >= 0`, it can verify `b - a $in N`. See **Manual — Builtin Verification Rules — Membership Rules**.

### Structured induction proof blocks (2026-05)

`by induc` and `by strong_induc` can now split their proof into a base block and a step block. Use `prove from n = base:` for the base case, `prove induc:` for ordinary induction steps, and `prove strong_induc:` for strong induction steps. See **Manual — Induction (`by induc`, `by strong_induc`)**.

### `by transitive_prop` (2026-05)

After you prove the standard associativity-shaped `forall` for a binary user-defined `prop` or `abstract_prop`, Litex records that predicate as **transitive**. Storing a same-predicate chain (e.g. `a $p b $p c`) also stores non-adjacent consequences such as `$p(a, c)`. See **Manual — Register a transitive predicate (`by transitive_prop`)**.

### `by reflexive_prop`, `by symmetric_prop`, `by antisymmetric_prop` (2026-05)

These register basic relation properties for user-defined props only, not builtin predicates. Reflexive registrations can close `$p(a, a)`. Symmetric registrations retry positive atoms with the registered argument permutation. Antisymmetric registrations can close `a = b` from `$p(a, b)` and `$p(b, a)`. See the corresponding Manual sections and `examples/by_symmetric_reflexive_antisymmetric_prop.lit`.

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
