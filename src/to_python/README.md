# Frozen Python extractor

`litex -python -e 'have a R = 1'` emits `a = 1.0`, while `litex -python -e '1 = 1'` emits `# No Python-extractable Litex definitions.`

```text
verify and collect supported statements
  -> numeric `have a R = expression` becomes a Python assignment
  -> supported `algo` definitions become Python functions
  -> add `import math` when an emitted expression needs it
  -> reject explicitly unsupported native-complex or number-theory forms
```

## Examples and boundaries

| Litex input | Python behavior |
| --- | --- |
| `have a R = 1` | Emits `a = 1.0`. |
| `have fn f(x R) R = x + 1` plus `have algo for f(x):`<br>&nbsp;&nbsp;`x + 1` | Emits `def f(x):` followed by `return (x + 1.0)`. |
| `1 = 1` | Emits no definition, only the no-extractable-definitions comment. |
| A fact containing native complex `i` | Rejected by extractor v1. |
| Builtin `gcd`, `quot`, `prime`, `coprime`, or `dvd` in a fact | Rejected by extractor v1 rather than translated approximately. |

This experiment is frozen; for example, adding complex extraction for `have z C = i` requires an explicit decision to resume the v1 surface.

Start with [`to_python_pipeline.rs`](to_python_pipeline.rs); for example, `PythonExtractor::extract_stmt` lists the supported statement families.
