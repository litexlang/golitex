# Objects And Statements

This file is a compact reference for Litex objects and executable statement
forms.  The object entries say what the notation means mathematically.  The
statement entries mirror `docs/cheatsheet.md`: first the well-definedness or
structural checks, then the proof obligation, then the environment effect.

Each `litex` block is intended to run on its own.

## Object Examples

### 1. Numeric Objects And Arithmetic

Mathematical meaning: numeric literals denote numbers in the usual built-in
number systems, and arithmetic expressions denote the corresponding numeric
objects.  Litex uses exact arithmetic for integer and rational calculations.

```litex
sketch:
    1 + 2 = 3
    3 - 1 = 2
    2 * 3 = 6
    6 / 2 = 3
    5 % 2 = 1
    2^3 = 8
    -1 + 2 = 1
```

### 2. Standard Number Sets

Mathematical meaning: `N`, `Z`, `Q`, and `R` are the built-in natural, integer,
rational, and real number sets.  Suffixes such as `_pos`, `_neg`, and `_nz`
name common subsets like positive or nonzero numbers.

```litex
sketch:
    0 $in N
    0 $in Z
    0 $in Q
    0 $in R
    1 $in N_pos
    1 $in R_pos
    -1 $in Z_neg
    1 $in Z_nz
    1 / 6 $in Q
    6 / 3 $in Z
    not 1 / 6 $in Z
    not 0 $in Q_nz
```

### 3. Finite Sets And Set Builders

Mathematical meaning: `{1, 2, 3}` is a displayed finite set, while
`{x R: x > 0}` is the subset of `R` cut out by the predicate `x > 0`.  A set
builder is best read as ordinary set-comprehension notation.

```litex
sketch:
    1 $in {1, 2, 3}
    $is_finite_set({1, 2})
    1 $in {x R: x > 0}

    have positive_reals set = {x R: x > 0}
    1 $in positive_reals
```

### 4. Set Operations

Mathematical meaning: `union`, `intersect`, and `set_minus` are the ordinary
binary union, intersection, and relative complement of sets.  `set_diff` is the
symmetric-difference style object used by the current library.

```litex
sketch:
    2 $in union({1, 2}, {2, 3})
    2 $in intersect({1, 2}, {2, 3})
    2 $in set_minus({1, 2}, {1})
    3 $in set_diff({1, 2}, {2, 3})
    {1, 2} $in power_set({1, 2, 3})
```

### 5. Ranges

Mathematical meaning: `range(a, b)` is the integer-style half-open range from
`a` up to but not including `b`; `closed_range(a, b)` and `a...b` are closed
ranges.  These objects are useful when finite enumeration or indexed data is
intended.

```litex
sketch:
    2 $in range(0, 3)
    3 $in closed_range(0, 3)
    2 $in 0...3
```

### 6. Tuples And Cartesian Products

Mathematical meaning: `(a, b)` is an ordered tuple, and `cart(A, B)` is the
Cartesian product of the factor sets.  Tuple projection uses one-based indexing
with square brackets.

```litex
sketch:
    (1, 2)[1] = 1
    (1, 2)[2] = 2
    (1, 2) $in cart(R, R)
    cart_dim(cart(R, Q)) = 2
    proj(cart(R, Q), 1) = R
```

### 7. Functions And Anonymous Functions

Mathematical meaning: `fn(x R) R` is the set of functions from `R` to `R`, and
`have fn f(x R) R = ...` names one such function.  Anonymous functions such as
`'R(x){x + 1}` are function values written directly at the point of use.

```litex
sketch:
    have fn shift(x R) R = x + 1

    shift $in fn(x R) R
    shift(2) = 3
    'R(x){x + 1}(2) = 3
    $fn_eq('R(x){x}, 'R(y){y})
```

### 8. Function Images

Mathematical meaning: `fn_range(f)` is the image of a function over its whole
domain.  `fn_range_on(f, S)` is the image of a unary function restricted to a
set `S`.

```litex
sketch:
    have fn shift(x R) R = x + 1

    shift(2) $in fn_range(shift)
    fn_range(shift) $subset R

    have by preimage x from shift(2) $in fn_range(shift)
    x $in R
    shift(2) = shift(x)
```

```litex
sketch:
    have a finite_seq(R, 3) = [1, 2, 3]

    a(2) $in fn_range_on(a, 1...3)
    fn_range_on(a, 1...3) $subset R
    $is_finite_set(fn_range_on(a, 1...3))

    have by preimage k from a(2) $in fn_range_on(a, 1...3)
    k $in 1...3
    a(2) = a(k)
```

### 9. Sequences, Finite Sequences, And Matrices

Mathematical meaning: `seq(R)` is the set of positive-integer-indexed real
sequences, `finite_seq(R, n)` is a length-`n` sequence, and `matrix(R, r, c)` is
an `r` by `c` rectangular array.  All three are function-like objects with
index application syntax.

```litex
sketch:
    have a finite_seq(R, 3) = [1, 2, 3]

    a $in fn(x N_pos: x <= 3) R
    a(1) = 1
    a(2) = 2
    a(3) = 3
    finite_seq(R, 3) = fn(x N_pos: x <= 3) R
```

```litex
sketch:
    have s seq(R)
    s(1) $in R

    have M matrix(R, 2, 2) = [[1, 2], [3, 4]]
    M(1, 1) = 1
    M(2, 1) = 3
```

### 10. Struct Objects

Mathematical meaning: a `struct` names a record-shaped subset of tuples, with
typed fields and optional defining conditions.  A value of `&Point` can be read
either by tuple index or by field projection through `&Point{...}.field`.

```litex
sketch:
    struct Point:
        x R
        y R

    (1, 2) $in &Point
    have p &Point = (1, 2)
    &Point{p}.x = p[1]
    &Point{p}.x = 1
    &Point{(1, 2)}.y = 2
```

## Statement Examples

### 1. Ordinary Fact Statement

Purpose: assert a mathematical fact and make it available later.

- Well-definedness / structural checks: the fact and every object inside it
  must be well-defined.
- Truth verification: Litex proves the fact from builtin rules, known facts,
  theorem instances, and local context.
- Environment effects: stores the proved fact and any inferred consequences.

```litex
1 + 1 = 2

forall x R:
    x = x
```

### 2. `know`

Purpose: introduce an assumption without proof, usually for explicit proof debt
or a background interface.

- Well-definedness / structural checks: rejected in strict mode; every assumed
  fact must be well-defined.
- Truth verification: none.
- Environment effects: stores the unsafe assumption and runs inference.

```litex
sketch:
    abstract_prop p(x)
    know $p(0)
    $p(0)
```

### 3. `let`

Purpose: introduce local names together with assumed facts about them.

- Well-definedness / structural checks: rejected in strict mode; parameter
  declarations are checked, and attached facts must be well-defined.
- Truth verification: none for the attached facts.
- Environment effects: stores the names, their type facts, the attached facts,
  and inferred consequences.

```litex
sketch:
    let a R:
        a = 1

    a $in R
    a = 1
```

### 4. Typed `have`

Purpose: introduce an arbitrary object of a nonempty type or set.

- Well-definedness / structural checks: the name must be unused and the type
  object must be well-defined.
- Truth verification: Litex verifies the type or set is nonempty.
- Environment effects: stores the new name, its membership fact, and inferred
  facts.

```litex
sketch:
    have x R
    x $in R
```

### 5. Definitional `have`

Purpose: introduce a name for a specific object.

- Well-definedness / structural checks: the name, declared type, and assigned
  object must be well-defined.
- Truth verification: Litex verifies the assigned object belongs to the
  declared type.
- Environment effects: stores the name, its type fact, the defining equality,
  and any value caches for sequence-like objects.

```litex
sketch:
    have a R = 1
    a $in R
    a = 1
```

### 6. `have by exist`

Purpose: name witnesses from an already known existential fact.

- Well-definedness / structural checks: the existential shape and requested
  witness count must match.
- Truth verification: verifies the source existential fact.
- Environment effects: stores witness names, witness type facts, body facts,
  and inferred consequences.

```litex
sketch:
    witness exist x R st {x = 1} from 1:
        1 = 1

    have by exist x R st {x = 1}: a
    a $in R
    a = 1
```

### 7. `have by preimage`

Purpose: name a preimage witness from a function-image membership fact.

- Well-definedness / structural checks: the source must be a supported range,
  replacement, or restricted-range membership fact, and the witness count must
  match.
- Truth verification: verifies the source membership fact.
- Environment effects: stores preimage names, domain facts, side conditions,
  and the equality connecting the value to the function application.

```litex
sketch:
    have fn shift(x R) R = x + 1

    shift(2) $in fn_range(shift)
    have by preimage x from shift(2) $in fn_range(shift)
    x $in R
    shift(2) = shift(x)
```

### 8. Function Definition

Purpose: define a function by a single expression over its domain.

- Well-definedness / structural checks: checks the function set, parameter
  declarations, body, return set, and function name.
- Truth verification: verifies the body value belongs to the return set for
  every allowed input.
- Environment effects: stores the function name, function type, body data,
  equality to the anonymous function, and inferred facts.

```litex
sketch:
    have fn f(x R) R = x + 1
    f $in fn(x R) R
    f(2) = 3
```

### 9. Case Function Definition

Purpose: define a function by cases on its input domain.

- Well-definedness / structural checks: checks the function set, cases,
  returned expressions, and function name.
- Truth verification: verifies each case returns a value in the return set and
  that the cases cover the domain.
- Environment effects: stores the function name, function type, and generated
  case facts.

```litex
sketch:
    have fn is_zero_indicator(x R) R by cases:
        case x = 0: 1
        case x != 0: 0

    is_zero_indicator(0) = 1
```

### 10. Recursive Function Definition

Purpose: define a function by induction over a decreasing integer-valued
measure.

- Well-definedness / structural checks: checks the function signature,
  induction measure, base and step cases, and recursive calls.
- Truth verification: verifies base and step obligations.
- Environment effects: stores the recursive function definition facts.

```litex
sketch:
    have fn count_from_zero(n Z: n >= 0) R by induc n from 0:
        case n = 0: 0
        case n > 0: count_from_zero(n - 1) + 1

    count_from_zero(0) = 0
```

### 11. Algorithm Definition And Evaluation

Purpose: attach an executable algorithm to a function so Litex can evaluate
calls.

- Well-definedness / structural checks: the target function must already exist
  and the algorithm parameters must match the function set.
- Truth verification: verifies each return expression is valid; if no default
  return exists, verifies case coverage.
- Environment effects: stores the algorithm definition for later `eval`.

```litex
sketch:
    have fn f(x R) R = x + 1

    algo f(x):
        x + 1

    eval f(2)
    f(2) = 3
```

```litex
sketch:
    have fn as algo id_real(x R) R = x

    eval id_real(3)
    id_real(3) = 3
```

### 12. Function From Unique Existence

Purpose: define a function when every input has a unique output satisfying a
property.

- Well-definedness / structural checks: the source `forall` must have the
  expected unique-existence shape.
- Truth verification: verifies the source `forall` or the proof block that
  establishes it.
- Environment effects: stores the function name, function type, property
  `forall`, and uniqueness fact.

```litex
sketch:
    have A set = R
    have B set = R

    have fn f as set:
        prove:
            forall x A:
                exist! y B st {y = x}
        witness exist! y B st {y = x} from x

    forall x A:
        f(x) = x
```

### 13. Symbolic Tuple, Cart, And Matrix Definitions

Purpose: define structured objects by coordinate or projection rules.

- Well-definedness / structural checks: the name must be unused, dimensions
  and coordinate expressions must be well-defined, and the left side must
  describe the object being defined.
- Truth verification: verifies the dimensions are positive and at least two
  when needed, and verifies entry values belong to the declared sets.
- Environment effects: stores tuple/cart/matrix markers, dimension facts, and
  coordinate or projection facts.

```litex
sketch:
    have n N_pos = 3
    2 <= n

    have tuple t for i <= n, t[i] = i
    t[1] = 1

    have cart R3 for i <= n, proj(R3, i) = R
    R3 = cart(R, R, R)
```

```litex
sketch:
    have r N_pos = 2
    have c N_pos = 2

    have matrix M matrix(N_pos, r, c) for i <= r, j <= c, M(i, j) = j
    M $in matrix(N_pos, r, c)
    M(1, 2) = 2
```

### 14. `prop` And `abstract_prop`

Purpose: introduce named predicates for reusable mathematical properties.

- Well-definedness / structural checks: parameter declarations and definition
  facts must be well-defined; names must not conflict.
- Truth verification: `prop` definitions do not prove their body facts, and
  `abstract_prop` has no body to prove.
- Environment effects: stores the concrete or abstract predicate definition.

```litex
sketch:
    prop is_one(x R):
        x = 1

    $is_one(1)

    abstract_prop related(x, y)
    know $related(1, 1)
    $related(1, 1)
```

### 15. `struct`

Purpose: define a record-like structure with typed fields and optional
equivalent facts.

- Well-definedness / structural checks: parameter domains, field types, and
  equivalent facts must be well-defined; the struct name must be unused.
- Truth verification: does not prove the equivalent facts at declaration time.
- Environment effects: stores the struct definition and enables membership and
  field-view facts.

```litex
sketch:
    struct Point:
        x R
        y R

    have p &Point = (1, 2)
    &Point{p}.x = 1
    &Point{p}.y = 2
```

### 16. `template`

Purpose: define a parameterized object or function family.

- Well-definedness / structural checks: template parameters and domains must
  be well-defined, and the body must execute in a local environment.
- Truth verification: the body is verified like ordinary Litex code.
- Environment effects: stores the template definition for later instantiation.

```litex
template<S set>:
    have carrier_alias set = S

\carrier_alias<R> = R

template<S set, z S>:
    have fn const_on_S(x S) S = z

\const_on_S<R, 0> $in fn(x R) R
```

### 17. `thm` And `by thm`

Purpose: store a reusable theorem and instantiate it later.

- Well-definedness / structural checks: the theorem statement must be
  well-defined; theorem names must be unique; theorem-call arguments must
  satisfy parameter types.
- Truth verification: the theorem proof verifies the target, and `by thm`
  verifies instantiated domain facts.
- Environment effects: stores the theorem definition, stores the theorem fact,
  and later stores instantiated conclusions.

```litex
thm add_zero_right:
    ? forall x R:
        x + 0 = x
    x + 0 = x

by thm add_zero_right(2)
2 + 0 = 2
```

### 18. `claim`

Purpose: prove a local target and store it in the current environment.

- Well-definedness / structural checks: the claimed fact must be well-defined.
- Truth verification: the proof block must verify the claimed target or
  then-clauses.
- Environment effects: stores the claimed fact and runs inference.

```litex
claim:
    prove:
        1 + 1 = 2
    1 + 1 = 2
```

### 19. `witness`

Purpose: prove an existential statement by giving explicit witnesses.

- Well-definedness / structural checks: witness count and witness types must
  match the existential target.
- Truth verification: verifies the existential body under the proposed
  witnesses.
- Environment effects: stores the existential fact and inferred consequences.

```litex
sketch:
    witness exist x, y R st {x > y} from 1, 0:
        1 > 0

    exist a, b R st {a > b}
```

### 20. `sketch` And `try`

Purpose: run checked exploratory code without committing it, or run a checked
batch that commits only if every nested statement succeeds.

- Well-definedness / structural checks: each nested statement performs its own
  checks; `try` rejects control statements such as `clear`, `import`, and
  `run_file`.
- Truth verification: nested statements verify normally.
- Environment effects: `sketch` has no outer effect; `try` commits the child
  environment into the parent environment on success.

```litex
sketch:
    have local_value R = 1
    local_value = 1

try:
    have committed_value R = 2
    committed_value = 2

committed_value = 2
```

### 21. Proof-By Statements

Purpose: tell Litex which proof shape to use for a local target.

- Well-definedness / structural checks: the proof statement checks the target,
  the shape-specific parameters, and any nested statements.
- Truth verification: verifies the shape-specific proof obligations, such as
  case coverage, contradiction, or both directions of extension.
- Environment effects: stores the target fact or generated `forall` fact.

```litex
sketch:
    by cases:
        prove:
            1 + 1 = 2
        case 1 + 1 = 2:
            do_nothing
        case 1 + 1 != 2:
            impossible 1 + 1 = 2
```

```litex
sketch:
    by contra:
        prove:
            not exist x R st {x != x}
    have by exist x R st {x != x}: a
    impossible a = a
```

```litex
sketch:
    by enumerate finite_set:
        prove:
            forall x {1, 2}:
                x = 1 or x = 2
```

```litex
sketch:
    by extension:
        prove:
            {1, 2} = {2, 1}
        by enumerate finite_set:
            prove:
                forall x {1, 2}:
                    x $in {2, 1}
        by enumerate finite_set:
            prove:
                forall y {2, 1}:
                    y $in {1, 2}

    {1, 2} = {2, 1}
```

### 22. `eval`

Purpose: compute an evaluable object and store the resulting equality.

- Well-definedness / structural checks: the object must be evaluable.
- Truth verification: no separate proof of the original expression is needed;
  evaluation supplies the equality.
- Environment effects: stores the expression-value equality with an evaluation
  reason.

```litex
eval 1 + 2
1 + 2 = 3
```

### 23. `macro`

Purpose: define a textual abbreviation used before parsing the expanded Litex
code.

- Well-definedness / structural checks: the macro name and replacement text
  must be parseable in later expanded positions.
- Truth verification: none for the macro definition itself.
- Environment effects: stores the macro expansion rule for following
  statements in the same file.

```litex
macro REAL "R"
macro HAVE_FN "have fn"

@HAVE_FN id_real(x @REAL) @REAL = x
id_real(1) = 1
```

### 24. `do_nothing`

Purpose: make an explicit empty proof step.

- Well-definedness / structural checks: none.
- Truth verification: none.
- Environment effects: none.

```litex
do_nothing
```

### 25. Module And File Commands

Purpose: load, stop, or clear external environments.  These examples are syntax
only because they depend on local files or installed modules.

- Well-definedness / structural checks: `import` and `run_file` resolve module
  or file paths; `stop import` requires an already imported module; `clear` has
  no structural checks.
- Truth verification: imported or run files verify normally when loaded.
- Environment effects: module/file commands update the module manager or
  current environment; `clear` removes the current user environment and stops
  imports.

<!-- litex:skip-test -->
```litex
import Nat
stop import Nat
run_file "./some_local_file.lit"
clear
```
