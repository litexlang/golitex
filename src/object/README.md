# Mathematical object model

The source objects `1`, `x + 1`, `sin(x)`, `{1, 2}`, and `fn(x R) R` become distinct `Obj` variants.

## Identity boundary

`Obj` is a structural tree, not a collection of generic AST-node IDs.

- `SymbolId` is the binding key of a resolved symbol atom: an identifier,
  module-qualified identifier, or bound parameter. An unresolved source name
  has no binding key until name resolution succeeds.
- A compound `Obj` owns no separate `SymbolId`. Its canonical identity is a
  recursive structural key made from its constructor and the keys of its child
  objects. A wrapper may still carry the identity of an underlying named or
  interned symbol; that payload identity is not a new node ID for the wrapper.
- `Obj::Number` is identified by its normalized numeric value, so equal numeric
  literals do not become distinct merely because they occur at different source
  positions.
- Operator objects use their constructor/operator identity (`Obj::Add`,
  `Obj::Mul`, and so on; builtin identity remains an implementation detail for
  this round).
- Fact and proof-result identity is carried by `FactId`, not `SymbolId`.

This round records the contract only. The existing alpha-canonical ID range,
builtin ID range, `#symbol_id_N` substitution keys, and ToLean
`SymbolId -> Lean name` mappings remain unchanged.

## Examples and boundaries

| Litex object | Rust shape |
| --- | --- |
| `1` | `Obj::Number`, keyed by normalized numeric value rather than `SymbolId`. |
| `i` | `Obj::ImaginaryUnit`, not an identifier named `i`. |
| `x + 1` | `Obj::Add` with two child objects; its identity is structural and recursive. |
| `sin(x)` | `Obj::Sin`; rational normalization may treat this whole value as an algebraic atom. |
| `arcsin(x)` | `Obj::Arcsin`; well-defined only for real `x` in `[-1, 1]`. |
| `{1, 2}` | `Obj::ListSet`. |
| `{x R: x >= 0}` | `Obj::SetBuilder` with a bound parameter and condition. |
| `fn(x R) R` | `Obj::FnSet`. |
| Two nested binders both written `x` | Distinct free/bound parameter objects keyed by `SymbolId`, not one string-only object. |

[`object.rs`](object.rs) defines the variants above;
[`alpha_equivalence.rs`](alpha_equivalence.rs) makes `forall x R:` / `x = x`
comparable to `forall y R:` / `y = y` up to binder renaming.
