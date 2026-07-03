#  Litex To Python Translator

`litex -python` is a trusted-programming translation mode, similar in shape to
`litex -latex`. It first runs the Litex verifier on the input, then emits Python
only for the small executable subset supported by the extractor.

The point is not just to translate syntax from Litex to Python.  The point is to
change how code is produced: write the executable definition together with the
mathematical facts and safety requirements it must satisfy, verify those facts
first, and only then extract the executable Python.  In this workflow, code is
not merely generated and tested after the fact; it is emitted from a checked
Litex source whose intended constraints were stated in advance.

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

A small scientific-computing kernel has the same shape: define constants,
write a numeric update rule, and reuse earlier extracted functions.

```litex
have dt R_pos = 1 / 100
have fn as algo euler_step(y, dy R) R = y + dt * dy
have fn as algo twice_step(y, dy R) R = euler_step(euler_step(y, dy), dy)
```

```python
dt = (1.0 / 100.0)

def euler_step(y, dy):
    return (y + (dt * dy))

def twice_step(y, dy):
    return euler_step(euler_step(y, dy), dy)
```

## Recursive Algorithm Shape

The v1 Python extractor does not yet emit recursive functions. It rejects
`have fn as algo ... by induc` and standalone `algo` bodies. Litex itself can
already express and evaluate recursive algorithms, so this is a backend
coverage boundary rather than a language-expression boundary.

For example, the Fibonacci sequence can be written as a recursive mathematical
function plus an executable algorithm body:

```litex
have fn fib(n Z: n >= 0) Z by induc n from 0:
    case n = 0: 0
    case n = 1: 1
    case n > 1: fib(n - 1) + fib(n - 2)

algo fib(n):
    case n = 0: 0
    case n = 1: 1
    fib(n - 1) + fib(n - 2)

eval fib(10)
fib(10) = 55
```

A recursive Python backend would lower the same algorithm shape to ordinary
Python recursion:

```python
def fib(n):
    if n == 0:
        return 0
    elif n == 1:
        return 1
    return fib(n - 1) + fib(n - 2)
```

This Python form is not emitted by v1 yet; it is the intended lowering shape
once recursive extraction is implemented.

This is the main reason the Litex-to-programming-language direction should
scale beyond the current extractor subset. The pure mathematical core of an
ordinary program function can be viewed as case analysis plus recursive state
transitions. Conditionals are case splits; loops are recursive updates over an
explicit state; dynamic-programming recurrences are recursive equations with a
chosen evaluation strategy. Litex supports checked case definitions,
decreasing recursive definitions, and executable `algo` bodies, so in principle
the algorithms used in scientific computation can be expressed in Litex once
their data and state are made explicit.

The remaining work is backend engineering and numeric contracts. A future
Python extractor still needs recursive emission, richer data structures,
arrays, matrices, library functions, iterative evaluation strategies, and a
clear contract for exact arithmetic, floating-point arithmetic, or interval
arithmetic.

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
program structure comes from verified Litex definitions in the supported subset,
so the trusted-programming claim is about properties that were actually stated
and checked in the Litex source before extraction.

The v1 backend uses Python `float`. Litex's proof is about the mathematical
real-number specification; v1 does not prove IEEE-754 rounding behavior, overflow
behavior, or numerical error bounds. Those require a later backend contract,
such as exact rationals, interval arithmetic, or explicit floating-point error
facts in Litex.
