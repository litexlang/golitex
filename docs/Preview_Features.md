# Preview Features

Jiachen Shen and The Litex Team, 2026-05-08. Email: litexlang@outlook.com

Preview features are usable experiments. They are implemented enough to try, but their syntax and semantics may still change. For stable language concepts, read the [Manual](https://litexlang.com/doc/Manual) first.

New preview-related behavior is **appended** under [Recent additions](#recent-additions-append-only) as it lands. The struct material below describes the explicit struct-view redesign: struct definitions name tuple/cartesian-product shapes, and field access must say which struct view is being used.

## Recent additions (append-only)

Short pointers only; fuller syntax and semantics live in the in-repo [Manual](Manual.md) where noted.

### `by transitive_prop` (2026-05)

After you prove the standard associativity-shaped `forall` for a binary `abstract_prop`, Litex records that predicate as **transitive**. Storing a same-predicate chain (e.g. `a $p b $p c`) also stores non-adjacent consequences such as `$p(a, c)`. See **Manual — Register a transitive predicate (`by transitive_prop`)**.

### `fn_range(f)` and `fn_dom(f)` objects (2026-05)

`fn_range(f)` and `fn_dom(f)` are preview objects for the range and set-theoretic domain of a known function. In the current minimal form, Litex only checks that `f` is already known as a function. These objects do **not** yet have attached mathematical properties: membership properties, graph facts, and domain/range inference are not part of this preview yet.

`fn_dom(f)` should be read as the set-theoretic / graph domain of `f`, not necessarily the exact argument shape accepted by function application. For example, if `f` is known as `fn(x, y R) R`, a future `fn_dom(f)` may describe the product-style input domain, while ordinary calls still use `f(a, b)` rather than passing one tuple argument to `f`.

```litex
have f fn(x R) R
fn_range(f) = fn_range(f)
fn_dom(f) = fn_dom(f)
```

### `$injective(f)`, `$surjective(f)`, and `$bijective(f)` (2026-05)

These function-property predicates are available as dedicated atomic fact forms. In the current version, Litex recognizes and stores their shape, but it does **not** attach builtin verification rules or automatic definitions to them. Users should prove the intended injective, surjective, or bijective facts explicitly when needed.

### `by commutative_prop` (2026-05)

After you prove a `forall` whose dom and then are the **same** positive abstract predicate, with every parameter of the `forall` appearing **exactly once** in each row (a permutation), Litex records one or more **gather** permutations for that predicate name. When a **positive** atomic instance is still unproved after the usual steps, the checker may retry using a **reordered** argument list derived from a stored gather (that retry does not run commutative post-processing again). Arity **≥ 2**; multiple registrations append distinct permutations (arity must stay consistent). Does not apply to negated `$not $p(...)` atoms. See **Manual — Register a commutative predicate (`by commutative_prop`)**. Examples: `examples/by_commutative_prop.lit`, `examples/tmp.lit` (4-ary permutation demo).

### `by … as set` implementation names (2026-05)

User-facing spellings are unchanged (`by fn as set`, `by fn set as set`, `by family as set`, `by tuple as set`, …). Internal statement / `stmt_type_name` labels were aligned (e.g. `ByFnAsSetStmt`, `ByFamilyAsSetStmt`, `ByTupleAsSetStmt`, `ByFnSetAsSetStmt`).

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

The prefix says how the object is being viewed. This avoids the ambiguity of bare `P.x`, because the same tuple could be viewed through different struct definitions.

The well-definedness check for:

```text
&Group(R){G}.add
```

reduces to proving:

```text
G $in &Group(R)
```

When `G $in &Group(R)` is known, Litex also stores the facts carried by the struct view: each explicit field access and its corresponding tuple projection belong to the field type, and each `<=>:` fact is instantiated with field names replaced by explicit field accesses.

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
