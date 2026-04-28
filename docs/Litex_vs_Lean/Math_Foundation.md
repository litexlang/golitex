# Litex vs Lean — Foundations

Mathematicians disagree about foundations—set theory (Bourbaki), category theory (the Grothendieck school), and so on. For teaching readability, Litex uses a naive, typed set-theoretic surface.

Below we first give **group axioms** as a checkable `prop` shape. Topological and metric spaces appear only as sketches (no proof obligations), in a plain Markdown code block for side-by-side comparison with Lean `structure` / `class`.

## Group axioms (runnable)

```litex
prop group_property(s set, zero s, add fn(x, y s) s, inv fn(x s) s):
    forall x, y, z s:
        add(x, add(y, z)) = add(add(x, y), z)
    forall x s:
        add(x, zero) = x
        add(zero, x) = x
        add(x, inv(x)) = zero
        add(inv(x), x) = zero
```

## Topology / metric spaces (sketch, not executed)

Lines starting with `#` below are pseudo-Litex sketches—**do not** put them inside a ` ```litex` fence:

```text
# prop is_topological_space(s set, open_sets power_set(s)):
#     {} $in open_sets
#     s $in open_sets
#     forall x, y open_sets: x \intersect y $in open_sets
#     forall u power_set(open_sets): cup(u) $in open_sets
#
# prop is_metric_space(s set, d fn(s, s) R):
#     forall x, y s: d(x, y) >= 0, d(x, y) = d(y, x)
#     forall x s: d(x, x) = 0
#     forall x, y, z s: d(x, z) <= d(x, y) + d(y, z)
```

In one line: **a structure is roughly a carrier set plus operations / predicates on it**, as in many textbooks.
