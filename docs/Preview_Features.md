# Preview Features

Jiachen Shen and The Litex Team, 2026-05-08. Email: litexlang@outlook.com

Preview features are usable experiments. They are implemented enough to try, but their syntax and semantics may still change. For stable language concepts, read the [Manual](https://litexlang.com/doc/Manual) first.

New preview-related behavior is **appended** under [Recent additions](#recent-additions-append-only) as it lands. Older material below still focuses on `struct`, instances, field access, and `by struct`.

## Recent additions (append-only)

Short pointers only; fuller syntax and semantics live in the in-repo [Manual](Manual.md) where noted.

### `by transitive_prop` (2026-05)

After you prove the standard associativity-shaped `forall` for a binary `abstract_prop`, Litex records that predicate as **transitive**. Storing a same-predicate chain (e.g. `a $p b $p c`) also stores non-adjacent consequences such as `$p(a, c)`. See **Manual — Register a transitive predicate (`by transitive_prop`)**.

### `by commutative_prop` (2026-05)

After you prove a `forall` whose dom and then are the **same** positive abstract predicate, with every parameter of the `forall` appearing **exactly once** in each row (a permutation), Litex records one or more **gather** permutations for that predicate name. When a **positive** atomic instance is still unproved after the usual steps, the checker may retry using a **reordered** argument list derived from a stored gather (that retry does not run commutative post-processing again). Arity **≥ 2**; multiple registrations append distinct permutations (arity must stay consistent). Does not apply to negated `$not $p(...)` atoms. See **Manual — Register a commutative predicate (`by commutative_prop`)**. Examples: `examples/by_commutative_prop.lit`, `examples/tmp.lit` (4-ary permutation demo).

### `by … as set` implementation names (2026-05)

User-facing spellings are unchanged (`by fn as set`, `by fn set as set`, `by family as set`, `by tuple as set`, …). Internal statement / `stmt_type_name` labels were aligned (e.g. `ByFnAsSetStmt`, `ByFamilyAsSetStmt`, `ByTupleAsSetStmt`, `ByFnSetAsSetStmt`). The struct bridge remains **`by struct`** with AST name `ByStructStmt` (not an “AsSet” form).

### `struct`, `by struct`, `&Type(...)`, field access (ongoing preview)

The sections **below** on struct definitions, struct parameters, instances, `by struct`, and field-access limits are unchanged; they remain preview rather than fully stable Manual material.

## Struct Definitions

A `struct` definition declares a record-like shape. Each field has a name and a field type.

```litex
struct Point:
    x R
    y R
```

Structs may also have header parameters. The header parameters are checked when the struct type is used.

```litex
abstract_prop group_property(s, zero, add, inv)

struct Group(s set):
    zero s
    add fn(x, y s) s
    inv fn(x s) s
    <=>:
        $group_property(s, zero, add, inv)
```

The `<=>:` block is preview behavior. Its facts are checked and can be released when a name is introduced as a struct parameter. It is not the same thing as proving that every object in a cartesian product is a struct.

## Struct Parameters and Identity

The important rule is:

> `x struct Group(R)` is a special parameter type. It is not the same as proving `x $in struct Group(R)`.

When Litex enters a parameter scope such as:

```litex
struct Point:
    x R
    y R

forall P struct Point:
    P.x $in R
```

the name `P` is registered in the local environment as belonging to `Point`. That environment-level identity is what makes `P.x` well-defined.

This identity is intentionally narrow. It is introduced by parameter binding, not by ordinary facts.

## Field Access

Field access currently has the form:

```text
P.x
```

The left side must be a bare name whose struct identity is known in the environment. Litex then checks that the corresponding struct definition has the requested field.

This is intentionally not equality-based. Even if `x = y` is known, Litex does not infer `x.f = y.f`, and it does not give `y` the struct identity of `x`.

```text
# This is intentionally not supported as a way to open fields.
let x, y:
    x = y
# x.f being meaningful does not make y.f meaningful.
```

Field access on arbitrary object expressions is also not part of this preview feature.

```text
# Not supported in this preview feature.
f(a).x
(1, 2).x
mod::P.x
```

## Struct in Function Parameters

Function spaces and anonymous functions can use struct parameter types.

```litex
struct Point:
    x R
    y R

forall P struct Point:
    '(Q struct Point) R {Q.x}(P) $in R
```

When checking the application above, Litex checks that `P` satisfies the struct parameter type by looking at `P`'s struct identity. It does not prove this by checking `P $in struct Point`.

This distinction is necessary for sound field access. A tuple or function application may be a set-theoretic object, but it does not automatically have fields.

```text
struct Point:
    x R
    y R

# This should fail: the tuple itself has no struct identity.
'(Q struct Point) R {Q.x}((1, 2)) $in R
```

## Struct Instance Objects

A struct instance object writes concrete field values in struct field order.

```litex
struct Point:
    x R
    y R

&Point(1, 2) $in Point
```

For `Point`, `&Point(1, 2)` means a `Point` value whose `x` field is `1` and whose `y` field is `2`. It is a real object, so it can be passed to a function whose parameter type is `struct Point`.

```litex
struct Point:
    x R
    y R

have fn point_add(x, y struct Point) Point = &Point(x.x + y.x, x.y + y.y)

point_add(&Point(1, 2), &Point(3, 4)) = &Point(4, 6)
```

Header arguments are written before field values:

```litex
struct Box(s set):
    value s
    label s

&Box(R)(1, 2) $in Box
```

This feature is still narrow. `&Point(1, 2)` can satisfy a `struct Point` parameter, and field access inside a function body can instantiate through it. But it does not make `(1, 2)` itself a `Point`, and it does not give every object equal to `&Point(1, 2)` global field access.

## Using Tuples with Struct Forall Facts

`by struct` is a narrow bridge from tuple data to a `forall` fact whose parameter is a struct.

```litex
struct Point:
    x R
    y R

forall P struct Point, t R:
    P.x + t $in R

by struct P from (1, 2) as Point, t = 3:
    forall P struct Point, t R:
        P.x + t $in R
```

The statement above instantiates the `forall` fact with:

- `P` from `(1, 2)` as `Point`
- `P.x` as `1`
- `P.y` as `2`
- `t` as `3`

It stores the instantiated then-fact:

```litex
1 + 3 $in R
```

The tuple must match the struct field list. For `Point`, `(1, 2)` means `x = 1` and `y = 2` only inside this `by struct` instantiation. Litex also checks that each tuple component satisfies the corresponding field type.

## Current Boundaries

These limitations are intentional in the preview design:

- `by struct` currently accepts a body containing exactly one `forall` fact.
- `by struct` does not support an arbitrary ordinary fact body.
- `by struct` does not globally register the tuple as a struct instance.
- `&Point(1, 2)` is a struct instance object, but `(1, 2)` is still only a tuple.
- `x $in struct Group(R)` does not open field access.
- `x = y` does not transfer struct identity from `x` to `y`.
- Field access is only `name.field`, not `f(a).field` or `mod::name.field`.
- Structs are not yet documented as stable object/cartesian-product syntax in the main manual.

The guiding principle is that set-theoretic membership and struct identity are different. Ordinary facts can say that an object belongs to a set; only explicit struct parameter binding gives a name field access.
