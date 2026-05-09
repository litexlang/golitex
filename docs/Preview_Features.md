# Preview Features

Jiachen Shen and The Litex Team, 2026-05-08. Email: litexlang@outlook.com

Preview features are usable experiments. They are implemented enough to try, but their syntax and semantics may still change. For stable language concepts, read the [Manual](https://litexlang.com/doc/Manual) first.

New preview-related behavior is **appended** under [Recent additions](#recent-additions-append-only) as it lands. The struct material below reflects the current reduced state: definitions remain, while usage syntax is removed pending redesign.

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

### Struct usage syntax removed pending redesign (2026-05)

Only `struct Name:` definitions remain. Struct values (`&Point(...)`), field access (`P.x`), struct-typed parameters (`P struct Point`), struct types in `fn` signatures, and `by struct` have been removed from the current surface syntax while their semantics are redesigned.

## Struct Definitions

A `struct` definition declares a record-like shape. Each field has a name and a field type.

```litex
struct Point:
    x R
    y R
```

Structs may also have header parameters. The definition is stored and its field declarations are checked, but there is currently no struct-typed parameter syntax that consumes this header as a type.

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

## Current Boundaries

These syntax forms are intentionally unavailable in the current redesign window:

- `P struct Point`
- `fn(x struct Point) Point`
- `P.x`
- `&Point(1, 2)`
- `by struct ...`

For now, a struct definition is metadata the runtime can parse, check, and store. It does not create a first-class object form, a parameter type, or a field-access expression.
