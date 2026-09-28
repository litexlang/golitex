# IR and display_string

This module owns two views of new_pipeline AST:

| API | Role |
|-----|------|
| `ir` | Typed semantic key (`*IR` newtypes) for lookup / compare |
| `display_string` | User-facing `String` |

Surface spelling (operators, `$in`, precedence parentheses, keywords) follows the
legacy Litex Display contract. FactId and line_file never appear in either view.

For every AST type in this module, these are the **only** two methods.

## Symbol identity

See [`../identifier_identity.md`](../identifier_identity.md).

- **Plain** identifiers: `ir` = `#<IdentifierId>#<name>` (e.g. `#3#x`);
  `display_string` currently follows IR text for most compound facts;
  `readable_string` strips `#id#` wrappers for humans (e.g. `#1#k $in N` →
  `k $in N`). JSON Normal output uses `readable_string`.
- **Qualified** identifiers: IR and display use the same qualified spelling
  (no `IdentifierId`).
- **Binder objs** (`SetBuilder` / `FnSet` / `AnonymousFn`): single body;
  binder slots are `BoundName`, so their IR also embeds `#id#name`.
- No shadowing; no same-name nested binders (parse occupy).
- Tokenizer rejects source tokens starting with `__` (Lean/codegen reserve).

## Typed IR wrappers

| Type | Used for |
|------|----------|
| `ObjIR` | `Obj` and obj leaves |
| `FactIR` | `Fact` / `AtomicFact` and fact leaves |
| `StmtIR` | `Stmt` and statement leaves |
| `ParamIR` | parameter lists / `AtomicName` / `BoundName` |

Construction is only through `ir()` in this module
(the `String` field is module-private). Arbitrary `String` values cannot become
IR keys by conversion. When user-facing text is needed, call `display_string()`
on the AST value or on the IR wrapper.

## Two methods only

For each AST type:

```rust
pub fn ir(&self) -> ObjIR { ... } // or Fact/Stmt/Param
pub fn display_string(&self) -> String {
    self.ir().display_string()
}
```

Exception: plain identifiers and binder-carrying objs override `display_string`
to show surface names while `ir` keeps `#id#name`.

Obj arithmetic precedence parentheses are handled inside `Obj::ir`
(via a local nested function when needed).

## Layout

- `types.rs` — IR newtypes
- `param.rs` / `obj.rs` / `fact.rs` / `stmt.rs` — AST families
