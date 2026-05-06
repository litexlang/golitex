# Litex vs Lean: Set theory

Jiachen Shen and The Litex Team, 2026-05-06. Email: litexlang@outlook.com

Try all snippets in browser: https://litexlang.com/doc/Litex_vs_Lean/Set_Theory

Markdown source: https://github.com/litexlang/golitex/blob/main/docs/Litex_vs_Lean/Set_Theory.md


Top-level goals and multi-line blocks (e.g. `have` / `know` / `prop`) do not need a wrapping `prove:`. Inside `by contra`, `by for`, and `by enumerate finite_set`, the checker still expects a `prove:` sub-block for the proof obligation before `do_nothing` or trailing steps.

---

## Example 1 — membership in a finite list-set

Litex checks list-set membership mechanically.

```litex
1 $in {1, 2}
```

---

## Example 2 — sets of sets (`{{}, {1,2}}`)

Nested list-set literals match the usual “sets whose elements are sets” story at the kernel level.

```litex
{1, 2} $in {{}, {1, 2}}
```

---

## Example 3 — disjunctive characterization of finite enumeration

```litex
forall i {1, 2}:
    i = 1 or i = 2
```

---

## Example 4 — positivity through a set-builder type index

```litex
forall x {y R: y > 0}:
    x > 0
```

---

## Example 5 — unequal cardinalities rule out set equality

Use `by contra` instead of the older top-level `contra … :` spelling.

```litex
by contra:
    prove:
        {1, 2, 3} != {1, 2}
    count({1, 2, 3}) = 3
    count({1, 2}) = 2
    count({1, 2, 3}) = count({1, 2})
    impossible 3 = 2
```

---

## Example 6 — duplicate-free list-sets (`{a,1}` with a symbolic `a`)

If you write `{a, 1}` and have not shown that `a` is apart from literals, a naive equality `{a,1} = {1,a}` will not verify without extra hypotheses. The usual failure mode is that **duplicated parameters must be known distinct** (e.g. unresolved `a ≠ 1`). No runnable snippet here.

---

## Example 7 — spelling `{5,…,7}` with `by for`

Legacy top-level `for i range(...) :` / `prove_for` is spelled with `by for` today.

```litex
by for:
    prove:
        forall i range(5, 8):
            i = 5 or i = 6 or i = 7
    do_nothing
```

---

## Example 8 — inclusion transitivity from two global `forall` facts

```litex
have a nonempty_set, b nonempty_set, c nonempty_set

know forall x a:
    x $in b

know forall x b:
    x $in c

have x a
x $in b
x $in c
```

---

## Example 9 — heavier set builders (minimal sketch)

When commas parse as arity separators in a builder, organize side conditions with patterns like `… and $q(...)` (see language release notes).

```litex
prop p9(x Z):
    x < 100

prop q9(y Q):
    y > 0

know $q9(17)
```

---

## Example 10 — finite enumeration over a tame statement

Parity modulo `%` in list enumerators demands careful integer typing.

```litex
by enumerate finite_set:
    prove:
        forall x {2, 4}:
            x = 2 or x = 4
    do_nothing
```

---

## Example 11 — restriction via inline domain predicates (`fn({ ... })` — codomain parses stricter)

```litex
have fn g(x R: x > 0) R = x + 1

know forall z R:
    z > 0
    =>:
        z + 1 > 1

know forall z R:
    z > 0
    =>:
        z + 1 > 0

g $in fn(x R: x > 0) R
```

---

## Example 12 — constant witness for a strict bound on \((0,\infty)\)

```litex
have fn h(x R) R = 100

know forall z R:
    z > 0
    =>:
        h(z) > 1

h(1) > 1
```

---

## Example 13 — read a total function into a typed function space with a domain restriction

```litex
have fn f_int(x Z: x > 0) R = x + 1

f_int $in fn(x Z: x > 0) R
```

---

## Example 14 — `have` over a small finite set (definitional facts recorded)

```litex
have a_list {1, 2, 3}
```
