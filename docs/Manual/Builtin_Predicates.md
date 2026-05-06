# Builtin Predicates

Try all snippets in browser: https://litexlang.com/doc/Manual/Builtin_Predicates

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Manual/Builtin_Predicates.md

This page lists the **builtin predicates** that Litex recognizes as atomic facts. It follows the atomic fact forms handled by the kernel.

For the general idea of atomic facts, including the idea that a fact is made from a predicate and its arguments, read [Factual Statements](https://litexlang.com/doc/Manual/Factual_Statements). For how these predicates are proved automatically, read [Builtin Verification Rules](https://litexlang.com/doc/Manual/Builtin_Verification_Rules).

---

## Equality and Order

These predicates compare two objects, usually numeric expressions.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `a = b` | `a != b` | `a` and `b` denote the same value. |
| `a < b` | `not a < b` | `a` is strictly less than `b`. |
| `a > b` | `not a > b` | `a` is strictly greater than `b`. |
| `a <= b` | `not a <= b` | `a` is less than or equal to `b`. |
| `a >= b` | `not a >= b` | `a` is greater than or equal to `b`. |

---

## Set Predicates

These predicates say what kind of set-like object Litex is seeing.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `$is_set(A)` | `not $is_set(A)` | `A` is treated as a set object. |
| `$is_nonempty_set(A)` | `not $is_nonempty_set(A)` | `A` has at least one element. |
| `$is_finite_set(A)` | `not $is_finite_set(A)` | `A` is finite in the sense Litex uses for standard finite objects. |

---

## Membership

Membership is the set-theoretic version of a type assertion.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `x $in A` | `not x $in A` | `x` is an element of `A`. |

---

## Shape Predicates

These predicates recognize common data shapes.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `$is_cart(C)` | `not $is_cart(C)` | `C` is a Cartesian product. |
| `$is_tuple(t)` | `not $is_tuple(t)` | `t` is a tuple value. |

---

## Set Inclusion

These predicates express inclusion between sets.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `A $subset B` | `not A $subset B` | Every element of `A` belongs to `B`. |
| `A $superset B` | `not A $superset B` | Every element of `B` belongs to `A`. |

---

## Function Restriction

This predicate says whether a function can be viewed as having a smaller or more constrained function type.

| Predicate | Negated form | Meaning |
|-----------|--------------|---------|
| `f $restrict_fn_in T` | `not f $restrict_fn_in T` | `f` can be restricted to the function space `T`. |

---

## Function Equality

These predicates express equality of functions.

| Predicate | Meaning |
|-----------|---------|
| `$fn_eq_in(f, g, S)` | `f` and `g` agree at every argument in `S`. |
| `$fn_eq(f, g)` | `f` and `g` are globally equal as function values. |

---

## Not Builtin: User Predicates

Calls such as `$p(x)` are also atomic facts, but they are not builtin predicates. They come from user declarations such as `prop p(...)` or `abstract_prop p(...)`, and Litex verifies them from the user's definition or known facts.
