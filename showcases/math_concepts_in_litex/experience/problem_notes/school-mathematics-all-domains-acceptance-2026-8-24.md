# School mathematics all-domains acceptance

## Task context

- Task: publish the completed high-school book with a domain Introduction and
  expand the standalone school-mathematics showcase to cover every domain.
- Scope: `showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell/`.
- Related source: `scripts/high_school_book/textbook/Introduction.lit`.

## Tracer: trigonometry enters the standalone survey

Before this change, the showcase's implemented scope explicitly omitted
trigonometry. The following commented lines preserve the former Litex opening;
the active lines are the representative interface and use now present in the
registered `main.lit`.

```litex
# # Included: native gcd, linear and quadratic equations, AM-GM, elementary
# # functions and arithmetic sequences, coordinate distance, finite probability,
# # and basic descriptive statistics.
# # Former behavior: there was no trigonometric definition or example.

have fn radians_from_degrees(theta R) R = theta * pi / 180
radians_from_degrees(180) = 180 * pi / 180 = pi
forall x R:
    sin(x)^2 + cos(x)^2 = 1
```

The same file now has one numbered section for each of the eleven directions
in the high-school Introduction. Trigonometry is representative because it was
previously named as out of scope and now has both an applicable function and a
checked identity/example.

## Boundary

This artifact proves breadth of the standalone survey, not complete coverage
of every high-school theorem. In particular, the calculus section checks an
average rate of change and consumes a supplied derivative formula at a
stationary point; the full epsilon-delta derivative relation remains in the
high-school textbook and is not reconstructed here.

## Evidence

Current implementation:
`showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell/main.lit`.

```text
target/release/litex -compact -runner -f showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell/main.lit
target/release/litex -compact -runner -r showcases/math_concepts_in_litex/1_middle_school_math_in_nutshell
```

Both commands returned exit code `0` with top-level runner `success: true` on
2026-08-24. The module contains no direct `trust` or local `axiom`.
