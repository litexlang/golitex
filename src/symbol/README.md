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
