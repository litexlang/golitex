# Python Extractor

`litex -python` is a source translation mode, similar in shape to
`litex -latex`. It first runs the Litex verifier on the input, then emits Python
only for the small executable subset supported by the extractor.

## CLI

```sh
litex -python -f input.lit
litex -python -e "have a R = 1"
litex -python -r repo_dir
```

`-r` reads `repo_dir/main.lit`.

## Supported v1 Subset

The v1 extractor emits Python `float` code for these verified Litex forms:

```litex
have a R = 1
have q Q = 1
have z Z = 3

have fn as algo f(x R) R = x + 1

have fn as algo max2(x, y R) R by cases:
    case x >= y: x
    case x < y: y
```

The generated Python shape is:

```python
a = 1.0
q = 1.0
z = 3.0

def f(x):
    return (x + 1.0)

def max2(x, y):
    if x >= y:
        return x
    elif x < y:
        return y
    raise AssertionError("unreachable verified Litex cases")
```

## Translation Examples

Numeric object definitions become module-level Python assignments:

```litex
have a R = 1
have q Q = 1 / 2
have z Z = 3
```

```python
a = 1.0
q = (1.0 / 2.0)
z = 3.0
```

Single-expression `have fn as algo` definitions become Python functions with a
single `return`:

```litex
have fn as algo f(x R) R = x + 1
```

```python
def f(x):
    return (x + 1.0)
```

Function calls are allowed only when the callee was already extracted earlier:

```litex
have fn as algo f(x R) R = x + 1
have fn as algo g(x R) R = f(x) + 2
```

```python
def f(x):
    return (x + 1.0)

def g(x):
    return (f(x) + 2.0)
```

Case-based `have fn as algo` definitions become `if` / `elif` functions:

```litex
have fn as algo max2(x, y R) R by cases:
    case x >= y: x
    case x < y: y
```

```python
def max2(x, y):
    if x >= y:
        return x
    elif x < y:
        return y
    raise AssertionError("unreachable verified Litex cases")
```

The final `AssertionError` is a defensive Python branch. Litex has already
verified that the supported case split covers the mathematical inputs.

## Selection Rules

`litex -python` automatically scans verified top-level statements.

- Numeric `have obj equal` statements are extraction candidates when their type
  is one of `R`, `Q`, `Z`, `N`, `N_pos`, or the positive/negative/nonzero
  variants of those standard sets.
- `have fn as algo` statements are extraction candidates only when every
  parameter set is exactly `R` and the return set is exactly `R`.
- Ordinary proof statements, claims, theorems, non-numeric object definitions,
  and non-`as algo` function definitions are skipped.
- Standalone `algo` statements are rejected in v1. Use `have fn as algo ...`
  when a function should be translatable.

If a statement is an extraction candidate but uses unsupported syntax, the
extractor reports an error instead of silently skipping it.

## Expression Boundary

Supported expression forms:

- numeric literals
- function parameters
- previously extracted numeric constants
- `+`, `-`, `*`, `/`, `^`
- calls to previously extracted `R^n -> R` functions

Supported case conditions:

- `=`, `!=`, `<`, `<=`, `>`, `>=`

Unsupported in v1:

- function domain restrictions such as `fn(x R: x > 0) R`
- standalone `algo`
- `have fn as algo ... by induc`
- non-`R` function parameters or returns
- sets, membership facts, abstract propositions, tuples, structures, matrices,
  templates, anonymous functions, sums, products, `sqrt`, `log`, `max`, `min`,
  and calls to functions that were not extracted earlier
- imported definitions as Python output

## Correctness Boundary

The extractor relies on Litex verification before emitting Python. The emitted
program structure comes from verified Litex definitions in the supported subset.

The v1 backend uses Python `float`. Litex's proof is about the mathematical
real-number specification; v1 does not prove IEEE-754 rounding behavior, overflow
behavior, or numerical error bounds. Those require a later backend contract,
such as exact rationals, interval arithmetic, or explicit floating-point error
facts in Litex.
