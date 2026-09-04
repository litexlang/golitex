# Symbol identity and scope

These two binders receive different `SymbolId` values even though alpha-equivalence matches their first parameter slots:

```litex
fn(x R) R {x + 1} = fn(y R) R {y + 1}
```

```text
parse left binder x -> SymbolId(1)
parse right binder y -> SymbolId(2)
bind each body reference to its own SymbolId
alpha-key both first parameter slots as binder #0
```

## What `SymbolId` identifies

`SymbolId` is a binding key for a resolved symbol atom, not a universal ID for
every parsed or runtime object. The identity belongs to the resolved binding,
so two binders with the same source spelling still receive different IDs, and
an unresolved identifier receives no ID until resolution succeeds.

Compound objects do not receive their own `SymbolId`; their identity is formed
recursively from the object constructor and the identities of their children.
Numeric literals use normalized value, operators use constructor/builtin
identity, and facts use `FactId`. This keeps `SymbolId` focused on the one job
that requires binding identity: distinguishing which declaration a symbol atom
refers to.

The following implementation cleanups are intentionally deferred: replacing
alpha-canonical IDs with a separate alpha-slot type, moving builtins out of the
current ID range, replacing `#symbol_id_N` string keys with a typed key, and
renaming or encapsulating the ordinary ToLean `SymbolId -> Lean name` mapping.
Template applications are not included in this identity space: they use their
recursive object structure, while a materialized definition name is the symbol
that receives a `SymbolId`.

## Examples and boundaries

| Operation | Example |
| --- | --- |
| Allocate | `have a R = 1` creates a new symbol binding for `a`. |
| Reject shadowing | `have x R` followed by `forall x R:` is rejected because the local binder reuses visible `x`. |
| Substitute | Instantiating `forall x R:` / `x = x` with `1` maps its binder symbol to object `1`. |
| Reject duplicate definition | Defining `a` twice in the same scope raises a name-used error. |
| Compare binders | `fn(x R) R {x}` and `fn(y R) R {y}` are alpha-equivalent despite different source names. |
| Preserve a direct carrier | After `have point &Point = (1, 2)`, execution records `&Point` on the exact definition of `point`. An exported `main::point.left` resolves that carrier by the same `SymbolId`; it does not infer named-field access from later membership or equality facts. |

Start with [`symbol_registry.rs`](symbol_registry.rs); for example,
`SymbolTable` maps a visible name to a `SymbolBinding` containing its stable
`SymbolId`. `SymbolDefinition` pairs that binding with its definition role and
the optional direct struct carrier recorded by execution. The parser does not
record carrier maps or embed a selected struct in field-access syntax; the
executed definition is cloned or exported with its environment.
