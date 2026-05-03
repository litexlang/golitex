# Builtin Concepts

Try all snippets in browser: https://litexlang.com/doc/Builtin_Features/Builtin_Objects

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Builtin_Features/Builtin_Objects.md


# Objects(Sets)

Everything you write in a formula is built from a fixed menu of expression forms: numbers, identifiers, sets, functions, tuples, sums, and so on. We call these objects (they are not variables because in math anything is constant). And since Litex is set-based, all objects are sets.

The subsections below name each form in ordinary mathematical language and show typical Litex spelling.

### Names and parameters

Objects introduced by `forall`, `have`, `let`, and function parameters are atomic pieces of syntax—not built from smaller operators inside Litex.

```litex
forall x R:
    x = x
```

### Function application

A function (given by `have fn` or by an anonymous head) applied to arguments denotes the value of the map at that point. Arguments may be grouped in several layers (curried style).

```litex
have fn f(x R) R = x + 1
f(2) = 3
```

### Numeric literals

Decimal or integer numerals; they combine with `+`, `-`, `*`, `/`, `%`, `^`, etc.

```litex
1 + 2 = 3
```

### Arithmetic and integer remainder

Binary operations on expressions; `%` is integer remainder when both sides are concrete integers; `^` is exponentiation.

```litex
2 * 3 = 6
5 % 2 = 1
2 ^ 3 = 8
```

### `abs`, `log`, `max`, `min`

Absolute value, logarithm (base and argument follow Litex parsing rules), and binary maximum and minimum.

```litex
forall x R:
    0 <= x
    =>:
        abs(x) = x
```

### Union, intersection, set difference

Set operations \(A \cup B\), \(A \cap B\), and differences such as `set_minus` / `set_diff`. Keyword and infix forms are interchangeable.

```litex
2 $in union({1, 2}, {2, 3})
2 $in intersect({1, 2}, {2, 3})
have t set = set_minus({1, 2}, {1})
```

```litex
1 $in {1} `union {2}
```

### Big union and big intersection (`cup`, `cap`)

Union and intersection over a **family** of sets (often written with an index); in Litex this is `cup(...)` and `cap(...)` on a suitable “set of sets.” Short illustrative proofs often need extra side conditions on the inner sets—see comments in `examples/litex_object_examples.lit`.

### Power set

\(\mathcal{P}(X)\): all subsets of \(X\), for the finite-style uses Litex supports here.

```litex
{1, 2} $in power_set({1, 2, 3})
```

### Enumerated sets

Finite sets written \(\{a, b, \ldots\}\).

```litex
1 $in {1, 2, 3}
```

### Set comprehension

\(\{\, z \in T \mid \text{condition on } z \,\}\).

```litex
have s set = { z N : z > 5 }
```

### Function types and anonymous functions

A **function space** is written `fn(x S) T`; an anonymous function value can be written with a `'…(…){…}` head and applied directly.

```litex
have g set = fn(x R) R
```

```litex
'R(x){x + 1}(2) = 3
```

### Cartesian product and dimension

\(A \times B \times \cdots\); `cart_dim` gives the number of factors when the value is recognized as a product.

```litex
let d set:
    d = cart(R, Q)
$is_cart(d)
cart_dim(d) = 2
```

### Projection from a product

Pick one factor of a Cartesian product.

```litex
proj(cart(R, Q), 1) = R
```

### Tuples and length

Ordered tuples \((a_1,\ldots,a_n)\) and their length.

```litex
(1, 2) = (1, 2)
```

```litex
let e set:
    e = (2, 3)
$is_tuple(e)
tuple_dim(e) = 2
e[1] = 2
```

### Counting members

Size of a finite enumerated set.

```litex
count({1, 2, 3}) = 3
```

### Finite `sum` and `product`

Summation and products over a bounded integer index with one expression body (indexed by a name like `x`).

```litex
sum(1, 3, '(x Z) Z {x}) = sum(1, 2, '(x Z) Z {x}) + '(x Z) Z {x}(3)
```

### Integer intervals as sets

Half-open `range(m, n)` and closed `closed_range(m, n)` as set-valued expressions (membership goals may need surrounding proofs).

```litex
have r set = range(0, 10)
have w set = closed_range(0, 1)
```

```litex
have q set = 0 `closed_range 1
```

### Sequence- and matrix-style index sets

Some indexed objects use **sequence** types or matrix index domains (repeated indices, `closed_range` on each axis) instead of a single `sum` index. Typical patterns appear with `family … fn(i …, j …) …` and `have fn M(i …, j …) …` (see below).

### Choice (`choose`)

From a family of nonempty sets, pick an element from each member once typing guarantees nonemptiness.

```litex
let s nonempty_set:
    forall x s:
        $is_nonempty_set(x)
choose(s) $in s
```

### Standard number sets

Names such as `R`, `Q`, `Z`, `N`, `N_pos`, and related signed or punctured variants.

```litex
0 $in Z
```

### Parametric `family`

A definition `family name(…) = …` is instantiated by `\name(args)` to get a concrete set or function space.

```litex
family fam(s set) = fn(x N_pos) s
forall a \fam(R):
    a $in fn(y N_pos) R
```

### Matrices

Litex supports matrices in three related ways: a constructor **type** `matrix(S, row_count, col_count)`, **literal** rectangular arrays `[[row1], [row2], …]`, and the same **indexed function space** pattern used for “matrices as maps” from a row–column index set into `S`.

**Type and literal.** You can bind a matrix object to a literal and read entries with two indices (like applying a function of two arguments):

```litex
prove:
    matrix(R, 2, 2) = matrix(R, 2, 2)

    have a matrix(R, 2, 2) = [[1, 2], [3, 4]]

    a $in fn (x1 N_pos, x2 N_pos: x1 <= 2, x2 <= 2) R

    a(1, 1) = 1
    a(1, 2) = 2
    a(2, 1) = 3
    a(2, 2) = 4
```

**Matrix algebra (surface operators).** These are **not** the scalar operators `+`, `-`, `*`, `^`. For two matrices of matching shape, `++` is cell-wise sum and `--` cell-wise difference. For compatible sizes, `**` is matrix product (columns of the left match rows of the right). For scalar `c` and matrix `A`, `c *. A` is scalar multiplication. For a square matrix and exponent `n` in `N_pos`, `A ^^ n` is matrix power.

```litex
eval [[1, 0], [0, 1]] ++ [[1, 0], [0, 1]]
```

```litex
eval [[2, 0], [0, 2]] -- [[1, 0], [0, 1]]
```

```litex
eval [[1, 2], [0, 1]] ** [[1, 0], [1, 1]]
```

```litex
eval 3 *. [[1, 2], [4, 5]]
```

```litex
eval [[2, 0], [0, 2]] ^^ 2
```

**Named matrices.** The same operators work on matrix objects (e.g. after `have m matrix(R, 2, 2) = …`).

```litex
have m matrix(R, 2, 2) = [[1, 0], [0, 1]]

eval m ++ m

eval m ** m

eval 2 *. m
```

**Indexed definition (`family` + `have fn`).** You can define the space of all \(m\times n\) matrices over `S` as a binary-indexed function set, then give one `case` per index pair—useful for proofs that branch on \((i,j)\):

```litex
family self_matrix(s set, m, n N_pos) = fn(i closed_range(1, m), j closed_range(1, n)) s
```

Full worked proofs (for example a diagonal matrix claim and `$is_diagonal_matrix`) use the same `family` / `prop` / `claim` layout as in longer packaged examples. A compact illustration (not run as an isolated doc test):

<!-- litex:skip-test -->

```litex
family self_matrix(s set, m, n N_pos) = fn(i closed_range(1, m), j closed_range(1, n)) s

prop is_diagonal_matrix(n N_pos,m \self_matrix(R, n, n)):
    forall i closed_range(1, n), j closed_range(1, n):
        i != j
        =>:
            m(i, j) = 0

claim:
    prove:
        forall M \self_matrix(R, 3, 3):
            M(1, 1) = 1
            M(1, 2) = 0
            M(1, 3) = 0
            M(2, 1) = 0
            M(2, 2) = 1
            M(2, 3) = 0
            M(3, 1) = 0
            M(3, 2) = 0
            M(3, 3) = 1
            =>:
                $is_diagonal_matrix(3, M)

    by for:
        prove:
            forall i closed_range(1, 3), j closed_range(1, 3):
                i != j
                =>:
                    M(i, j) = 0
```
