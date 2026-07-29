# Litex To Python Frozen Experiment

> **Status: frozen experiment.** The current extractor is preserved as a
> research prototype and compatibility surface. Its supported v1 subset is not
> being expanded. Maintenance is limited to regressions caused by Litex core
> changes and fixes needed to keep the documented subset working.

`litex -python` first runs the Litex verifier on the input, then emits Python
only for the small executable subset supported by the frozen extractor. It is
not a general Litex-to-Python compiler and is not a production backend.

The experiment tests a narrow idea: write an executable definition together
with mathematical facts and requirements, verify the Litex source, and then
extract the supported definition. The generated Python still has the
correctness limits described below.

## CLI

```sh
litex -python -f input.lit
litex -python -e "have a R = 1"
litex -python -r repo_dir
```

`-r` compiles the complete ordered `[export]` table declared in `repo_dir/litex.config`.

## Supported v1 Subset

The v1 extractor emits Python `float` code for these verified Litex forms:

```litex
have a R = 1
have q Q = 1
have z Z = 3

have fn f(x R) R = x + 1
have algo for f(x):
    x + 1

have fn max2(x, y R) R by cases:
    case x >= y: x
    case x < y: y
have algo for max2(x, y):
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

Single-expression `have algo for` implementations become Python functions with a
single `return`:

```litex
have fn f(x R) R = x + 1
have algo for f(x):
    x + 1
```

```python
def f(x):
    return (x + 1.0)
```

Function calls are allowed only when the callee was already extracted earlier:

```litex
have fn f(x R) R = x + 1
have algo for f(x):
    x + 1
have fn g(x R) R = f(x) + 2
have algo for g(x):
    f(x) + 2
```

```python
def f(x):
    return (x + 1.0)

def g(x):
    return (f(x) + 2.0)
```

Case-based `have algo for` implementations become `if` / `elif` functions:

```litex
have fn max2(x, y R) R by cases:
    case x >= y: x
    case x < y: y
have algo for max2(x, y):
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
have dt R+ = 1 / 100
have fn euler_step(y, dy R) R = y + dt * dy
have algo for euler_step(y, dy):
    y + dt * dy
have fn twice_step(y, dy R) R = euler_step(euler_step(y, dy), dy)
have algo for twice_step(y, dy):
    euler_step(euler_step(y, dy), dy)
```

```python
dt = (1.0 / 100.0)

def euler_step(y, dy):
    return (y + (dt * dy))

def twice_step(y, dy):
    return euler_step(euler_step(y, dy), dy)
```

## Preserved Recursive Algorithm Shape

The v1 Python extractor emits `have algo for` bodies with `R` parameters and
an `R` return value, including calls from an implementation to itself.

For example, the Fibonacci sequence can be written as a recursive mathematical
function plus an executable algorithm body:

```litex
have fn fib(n Z: n >= 0) Z by induc n from 0:
    case n = 0: 0
    case n = 1: 1
    case n > 1: fib(n - 1) + fib(n - 2)

have algo for fib(n):
    case n = 0: 0
    case n = 1: 1
    case n > 1: fib(n - 1) + fib(n - 2)

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

This exact Fibonacci source is outside the current v1 boundary because it uses
`Z`. A `have algo for` implementation with the supported `R` signature is
emitted in this same Python shape, including its self-calls.

This example records the direction explored by the prototype; it is not a
promise of continued backend development. Supporting this exact integer
function would require work outside the frozen subset, including `by induc`
lowering and an explicit numeric contract.

## Selection Rules

`litex -python` automatically scans verified top-level statements.

- Numeric `have obj equal` statements are extraction candidates when their type
  is one of `R`, `Q`, `Z`, `N`, `N+`, or the positive/negative/nonzero
  variants of those standard sets.
- `have algo for f(...)` statements are extraction candidates when the already
  declared function has an `R^n -> R` signature.
- Ordinary proof statements, claims, theorems, non-numeric object definitions,
  and function definitions without an implementation are skipped.

If a statement is an extraction candidate but uses unsupported syntax, the
extractor reports an error instead of silently skipping it.

## Expression Boundary

Supported expression forms:

- numeric literals
- function parameters
- previously extracted numeric constants
- `+`, `-`, `*`, `/`, `^`
- calls to previously extracted `R^n -> R` functions, including the function
  currently being emitted for direct self-recursion

Supported case conditions:

- `=`, `!=`, `<`, `<=`, `>`, `>=`

Unsupported in v1:

- function domain restrictions such as `fn(x R: x > 0) R`
- non-`R` function parameters or returns
- native complex objects and genuinely complex-valued expressions, including
  `C`, `i`, `re`, `img`, and `C_abs`
- native trigonometric expressions `sin(x)`, `cos(x)`, `tan(x)`, and `cot(x)`
- sets, membership facts, abstract propositions, tuples, structures, matrices,
  templates, anonymous functions, sums, products, `sqrt`, `log`, `max`, `min`,
  and calls to functions that were not extracted earlier
- imported definitions as Python output

The native complex interface is symbolic in this release. If an extraction
candidate is genuinely complex-valued, the extractor reports it as unsupported;
it does not emit Python `float` code or silently reinterpret the expression
over `R`. The Litex evaluator likewise has no complex runtime value in this
release.

Native trigonometry is symbolic at this boundary as well. The extractor does
not silently choose `math.sin`, a floating-point angle convention, or values
at undefined tangent and cotangent inputs; it reports the expression as
unsupported.

## Correctness Boundary

The extractor relies on Litex verification before emitting Python. The emitted
program structure comes from verified Litex definitions in the supported subset,
so the trusted-programming claim is about properties that were actually stated
and checked in the Litex source before extraction.

The v1 backend uses Python `float`. Litex's proof is about the mathematical
real-number specification; v1 does not prove IEEE-754 rounding behavior,
overflow behavior, or numerical error bounds. The frozen experiment does not
provide an exact-rational, interval-arithmetic, or floating-point error
contract.
