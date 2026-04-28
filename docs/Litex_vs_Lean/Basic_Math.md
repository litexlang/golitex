# Litex vs Lean: Basic Math

Narrative in Markdown; runnable Litex lives in fenced ` ```litex` ` blocks below. Lean comparisons stay in prose (Lean uses Mathlib tactics such as `norm_num`, `field_simp`, …).

---

## Example 1 — \(1 + 1 = 2\)

**Task.** State the closed arithmetic fact.

Litex verifies it via built-ins. Lean normally imports arithmetic and finishes with something like `norm_num`.

```litex
1 + 1 = 2
```

---

## Example 2 — Rational identity under a non-vanishing denominator

**Task.** Quantify over real parameters and assume the expanded denominator non-zero; conclude the symmetric fraction simplifies to \(1\).

Older tutorials spelled domain constraints under a `dom:` headline; modern syntax separates premises on their own lines, then uses `=>:` for the consequence.

```litex
prove:
    forall a, b, c, d R:
        a * c + a * d + b * c + b * d != 0
        =>:
            (a + b) * (c + d) / (a * c + a * d + b * c + b * d) = 1
```

---

## Example 3 — Defining primes and fixing a concrete prime (97)

**Task.** Give a predicate-like definition of primality, then check `$is_prime(97)`.

A full divisor walk can be done with `by for` when every branch reduces. A common pattern is to `know` a finite family of modular facts (similar cost to a big `decide` in Lean).

```litex
prove:
    prop is_prime(x N_pos):
        2 <= x
        forall y N_pos:
            2 <= y < x
            =>:
                x % y != 0

    know forall i range(2, 97):
        97 % i != 0

    $is_prime(97)
```

---

## Example 4 — Addition is commutative modulo a nonzero modulus

The commutative law for residues is checked directly here (no separate named “congruence” predicate required for the story).

```litex
prove:
    forall a, b, c Z:
        c != 0
        =>:
            (a + b) % c = (b + a) % c
```

---

## Example 5 — Euler quartic counterexample (existential witness)

**Task.** Record a famous counterexample with `witness exist … from … : …`.

```litex
prove:
    prop euler_counterexample(a, b, c, d N_pos):
        a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4

    witness exist a, b, c, d N_pos st {a ^ 4 + b ^ 4 + c ^ 4 = d ^ 4} from 95800, 217519, 414560, 422481:
        95800 ^ 4 + 217519 ^ 4 + 414560 ^ 4 = 422481 ^ 4
```

---

## Example 6 — Mixed-type function and application

**Task.** Define `f : R × Z → R` by multiplication and check a small instance. Passing a non-integer where `Z` is required fails domain checking (error text omitted here).

```litex
prove:
    have fn f(x R, y Z) R = x * y

    f(1, 2) = 1 * 2 = 2
```

---

## Example 7 — Universal statement over a product of finite list-sets

Use `by enumerate finite_set` to walk the Cartesian product.

```litex
prove:
    by enumerate finite_set:
        prove:
            forall x {4, 17, 6.6}, y {1, 2 * 0.2, 3.0}:
                x > y
        do_nothing
```

---

## Example 8 — `by for` over integer ranges

Older surface syntax used top-level `for …` / `prove_for` spellings; use `by for` with a `forall` over `range` / `closed_range` today. Parity (`% 2`) inside enumerators needs attention to integer typing—see the cheatsheet.

```litex
prove:
    by for:
        prove:
            forall n range(0, 11):
                n < 11
        do_nothing
```

---

## Summary

Lean’s tactic stack is extremely general. Litex leans on algebraic closure and searchable facts for routine arithmetic.
