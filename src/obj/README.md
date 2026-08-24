# Mathematical objects

The source objects `1`, `x + 1`, `sin(x)`, `{1, 2}`, and `fn(x R) R` become distinct `Obj` variants.

## Examples and boundaries

| Litex object | Rust shape |
| --- | --- |
| `1` | `Obj::Number`. |
| `i` | `Obj::ImaginaryUnit`, not an identifier named `i`. |
| `x + 1` | `Obj::Add` with two child objects. |
| `sin(x)` | `Obj::Sin`; rational normalization may treat this whole value as an algebraic atom. |
| `arcsin(x)` | `Obj::Arcsin`; well-defined only for real `x` in `[-1, 1]`. |
| `{1, 2}` | `Obj::ListSet`. |
| `{x R: x >= 0}` | `Obj::SetBuilder` with a bound parameter and condition. |
| `fn(x R) R` | `Obj::FnSet`. |
| Two nested binders both written `x` | Distinct free/bound parameter objects keyed by `SymbolId`, not one string-only object. |

[`object_types.rs`](object_types.rs) defines the variants above;
[`obj_alpha_key.rs`](obj_alpha_key.rs) makes `forall x R:` / `x = x`
comparable to `forall y R:` / `y = y` up to binder renaming.
