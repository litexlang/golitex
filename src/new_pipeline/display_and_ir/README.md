# IR and display_string

This module owns two views of new_pipeline AST:

| API | Role |
|-----|------|
| `ir` | Typed semantic key (`*IR` newtypes) for cache / lookup / compare |
| `display_string` | User-facing `String` = strip `#<digits>#` tags from the IR |

Surface spelling (operators, `$in`, precedence parentheses, keywords) follows the
legacy Litex Display contract. FactId and line_file never appear in either view.

For every AST type in this module, these are the **only** two methods.

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

## The only unusual part: identifier ids

Almost every character of an internal string is ordinary Litex source spelling.
The **only** deliberate oddity is that each `Identifier` / `IdentifierWithMod`
is tagged with its `IdentifierId`:

```text
internal:  #12#x $in #3#A
display:   x $in A

internal:  M::#12#x
display:   M::x
```

Everything else is meant to look like Litex. Do not invent further internal-only
spellings (no `____binder_…`, no `_generated_…`).

## Why attach an id to every identifier

1. **Same surface name, different bindings stay distinct.**
   Two locals both named `x` in different scopes must not collide in a fact
   cache key. The id is the binding identity; the name is only for humans.

2. **Cache and cite stay exact.**
   `ByCache` / known-fact lookup can key on the IR and know
   that a hit means the same binding, not merely the same spelling.
   Exact FactIR ByCache indexes **AtomicFact only**; binder-heavy composite
   facts are out of scope for this cache.

3. **Module-qualified and local forms can share one identity when they should.**
   A binding keeps one `IdentifierId`. Rendering may show `x` or `M::x`; the
   id tag keeps the semantic key stable when the surface spelling differs.

4. **Display stays readable without a second pretty-printer.**
   User output is just “delete `#<id>#`”. No separate pretty-print grammar is
   required for the common path.

5. **Avoids treating Display as identity.**
   Names alone are not a sound semantic key. Embedding the id in the internal
   string makes that contract explicit instead of hoping two `to_string()`
   results coincide for the right reason.

## Two methods only

For each AST type:

```rust
pub fn ir(&self) -> ObjIR { ... } // or Fact/Stmt/Param
pub fn display_string(&self) -> String {
    self.ir().display_string()
}
```

`display_string` always strips `#<digits>#` from the IR. Obj arithmetic
precedence parentheses are handled inside `Obj::ir`
(via a local nested function when needed).

## Layout

- `types.rs` — IR newtypes
- `helper.rs` — `strip_identifier_id_tags` only
- `param.rs` / `obj.rs` / `fact.rs` / `stmt.rs` — AST families
