# Builtin props

Try all snippets in browser: https://litexlang.com/doc/Builtin_Features/Builtin_Props

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Builtin_Features/Builtin_Props.md


An **atomic** proposition is a single goal the checker may treat as one step: no top-level `and` / `or` inside it. This page lists the atomic forms built into Litex’s surface syntax: what each one means in ordinary mathematical language, and how to write it.

Many forms use a leading `$` on a fixed predicate name (membership, set typing, function comparison, …). You can also introduce your own atomic predicates with `abstract_prop` and reuse them as `$name(…)`.

---

## User-defined atomic predicate (`$name(arguments)`)

You declare a schema with `abstract_prop p(…)`. Later, `$p(actuals)` is one atomic fact; its negation is `not $p(actuals)`.

```litex
prove:
    abstract_prop ok(x)
    know $ok(0)
    $ok(0)
```

```litex
prove:
    abstract_prop bad(x)
    know not $bad(1)
    not $bad(1)
```

---

## Equality (`=`) and inequality (`!=`)

**Equal:** the two expressions denote the same value. **Not equal:** they are distinct (often proved via arithmetic or ordering).

```litex
prove:
    1 = 1
    2 != 3
```

---

## Strict and non-strict order; negated comparisons

**Less / greater:** strict order on expressions (typically numbers). **At most / at least:** non-strict order. Prefix with `not` for the negated comparison (e.g. “not less than” is not the same token as \(\ge\), but is the logical negation of `<`).

```litex
prove:
    0 < 1
    2 > 1
    1 <= 1
    2 >= 1
    not 1 < 0
```

---

## Set typing: `Set`, nonempty, finite (and negations)

**`$is_set(A)`:** \(A\) is treated as a set object in the language. **`$is_nonempty_set(A)`:** \(A\) has at least one element (under the checker’s rules for standard sets, enumerations, intervals, products, etc.). **`$is_finite_set(A)`:** \(A\) is finite in the sense Litex axiomatizes. Negations spell **`not $is_set(…)`, `not $is_nonempty_set(…)`, `not $is_finite_set(…)`** when you need them.

```litex
prove:
    $is_set({1, 2})
    $is_nonempty_set({1})
    $is_finite_set({1, 2})
```

```litex
prove:
    not $is_nonempty_set({})
```

---

## Membership (`$in`) and non-membership

**`x $in A`:** the value \(x\) lies in the set \(A\). **`not x $in A`:** \(x\) is not a member (for standard number sets, often after numeric evaluation).

```litex
prove:
    1 $in {1, 2}
    0.5 $in Q
```

```litex
prove:
    not (-1) $in N
```

---

## Cartesian product and tuple shape (`$is_cart`, `$is_tuple`; negations)

**`$is_cart(U)`:** \(U\) is a Cartesian product (or passes the product-shaped typing check). **`$is_tuple(t)`:** \(t\) is an \(n\)-tuple value. Negated forms `not $is_cart(…)` and `not $is_tuple(…)` are available for the corresponding logical negations.

```litex
prove:
    have c set = cart(R, Q)
    $is_cart(c)
```

```litex
prove:
    have u set = (1, 2)
    $is_tuple(u)
```

---

## Subset and superset (and negations)

**`A $subset B`:** every element of \(A\) belongs to \(B\) (\(A \subseteq B\)). **`B $superset A`:** the same inclusion, reversed notation. **`not A $subset B`**, **`not B $superset A`:** negated inclusion claims.

```litex
prove:
    let a, b set:
        a $subset b
    forall x a:
        x $in b
    b $superset a
```

```litex
prove:
    let a, b set:
        not a $subset b
    not b $superset a
```

```litex
{1} $subset {1, 2}
```

---

## Restricting a function to a smaller type (`$restrict_fn_in`)

**`$restrict_fn_in(f, T)`:** the value \(f\) (already a function) is also well-typed as a member of the function space \(T\), typically with a **stronger** domain annotation (narrower domain or extra domain conditions). The negation says \(f\) **cannot** be seen as having that tighter type.

```litex
prove:
    have f fn(x R, y Q) R

    $restrict_fn_in(f, fn(a Q, b Q) R)

    $restrict_fn_in(f, fn(x R, y Q: x < y) R)
```

```litex
prove:
    have g fn(x, y R) R

    $restrict_fn_in(g, fn(x, y R: x < y, x < 0) R)

    $restrict_fn_in(g, fn(p Q, q Q) R)
```

---

## Function equality on a set (`$fn_eq_in`) and global function equality (`$fn_eq`)

**`$fn_eq_in(f, g, S)`:** \(f\) and \(g\) agree at every argument in \(S\) (pointwise equality on that domain). **`$fn_eq(f, g)`:** the two function values have the same declared function type and are equal in the sense of that typing (often reduced to a `forall` over parameters).

```litex
have fn f(x R) R = x
have fn g(x R) R = x

forall x R:
    f(x) = x = g(x)

$fn_eq_in(f, g, R)
```

```litex
$fn_eq_in('R(x){x}, 'R(y){y}, R)
```

```litex
$fn_eq('R(x){x}, 'R(y){y})
```

```litex
have fn f(x R) R = x
have fn g(x R) R = x
forall x R:
    f(x) = x = g(x)
$fn_eq(f, g)
```

---

## Chaining and combinations

Chains such as `0 < 1 < 2` are **chain facts**, not a single `AtomicFact` internally, but they express order in one line. Conjunctions `P and Q` combine atomics. These are common **around** atomic goals in proofs:

```litex
prove:
    0 < 1 < 2
```

```litex
prove:
    1 = 1 and 2 < 3
```

For verification shortcuts on equalities, comparisons, membership, and many `$…` predicates without user `prove` blocks, see [Builtin verification rules](Builtin_Verification_Rules.md).
