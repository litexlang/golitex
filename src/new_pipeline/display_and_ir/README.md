# IR and display_string

This module owns two views of new_pipeline AST:

| API | Role |
|-----|------|
| `ir` | Typed semantic key (`*IR` newtypes) for lookup / compare |
| `display_string` | User-facing `String` (binder objs use `.surface`; otherwise usually IR spelling) |

Surface spelling (operators, `$in`, precedence parentheses, keywords) follows the
legacy Litex Display contract. FactId and line_file never appear in either view.

For every AST type in this module, these are the **only** two methods.

## Symbol identity (locked)

See [`../identifier_identity.md`](../identifier_identity.md) — the canonical
note on **name is identity**, why `IdentifierId` was removed (false IR-key
misses / true shadowing conflicts), FactIR index / Obj WD ByKnown contracts,
and the do-not-break checklist.

**Name is identity:** the same surface name (plain, `Mod::name`, or
`Mod::Export::name`) always
denotes the same symbol. No shadowing; no same-name nested binders. IR
keys use the surface name spelling directly.

Binder-carrying objects (`SetBuilder`, `FnSet`, `AnonymousFn`) store
`surface` (user letters, display) and `alpha` (`□N`, ops / `ir` / known-memory keys).
Tokenizer rejects source tokens starting with `__` (Lean/codegen reserve).
Do not free-occupy `□N`.

## Typed IR wrappers

| Type | Used for |
|------|----------|
| `ObjIR` | `Obj` and obj leaves |
| `FactIR` | `Fact` / `AtomicFact` and fact leaves |
| `StmtIR` | `Stmt` and statement leaves |
| `ParamIR` | parameter lists / `AtomicName` |

Construction is only through `ir()` in this module
(the `String` field is module-private). Arbitrary `String` values cannot become
IR keys by conversion. When user-facing text is needed, call `display_string()`
on the AST value or on the IR wrapper.

Binder slots use `□N` in `ir` (Litex-internal identity). `__…` is Lean-only and
must not appear in Litex source.

## Two methods only

For each AST type:

```rust
pub fn ir(&self) -> ObjIR { ... } // or Fact/Stmt/Param
pub fn display_string(&self) -> String {
    self.ir().display_string()
}
```

Obj arithmetic precedence parentheses are handled inside `Obj::ir`
(via a local nested function when needed).

## Layout

- `types.rs` — IR newtypes
- `param.rs` / `obj.rs` / `fact.rs` / `stmt.rs` — AST families
