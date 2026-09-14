# IR and display_string

This module owns two views of new_pipeline AST:

| API | Role |
|-----|------|
| `ir` | Typed semantic key (`*IR` newtypes) for cache / lookup / compare |
| `display_string` | User-facing `String` (today: same as IR spelling) |

Surface spelling (operators, `$in`, precedence parentheses, keywords) follows the
legacy Litex Display contract. FactId and line_file never appear in either view.

For every AST type in this module, these are the **only** two methods.

## Symbol identity (locked)

See [`../identifier_identity.md`](../identifier_identity.md).

**Name is identity:** the same surface name (plain or `mod::name`) always
denotes the same symbol. No shadowing; no same-name nested binders. IR cache
keys use the surface name spelling directly.

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

Do not invent further internal-only spellings (no `____binder_…`, no
`_generated_…`).

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
