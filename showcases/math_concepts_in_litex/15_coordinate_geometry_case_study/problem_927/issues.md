# Qualified geometry function WD — authoring route closed 2026-10-04

Task: conversation clarification after the closeout retest. Scope: this
original two-export geometry module. Category 1: use the existing explicit
release interface before qualified function definitions are needed.

The maintainer confirmed that cross-file definitions are explicitly released.
The original solution now begins with:

```litex
release obj def geo::vec
release obj def geo::dot
release obj def geo::det
release obj def geo::distance_sq
```

Its original SSS theorem, assumptions and proof are unchanged. Both the file
and repository entries pass under strict. No trust, helper theorem, owner
lookup change or cache-format change was added. The earlier proposed broader
finished-export WD/evidence repair was unnecessary for this authoring contract
and is withdrawn for this case.

Without release, the original inferred equality produced an explicit
`internal_bug` WD diagnostic; that historical output and its live-stack
signature diagnosis remain in the frozen earlier receipt. Hard Runtime errors
still must be forwarded intact. Do not erase the old observation or describe
the current authoring correction as a module-owner implementation repair.

```sh
litex -strict -f showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/problem_927/solution.lit
litex -strict -r showcases/math_concepts_in_litex/15_coordinate_geometry_case_study/problem_927
```

[Current acceptance](../../../../tests/tooling/acceptance/conversation-clarifications-2026-10-04.md).
[Historical error and Detailed diagnostic](../../../../tests/tooling/acceptance/conversation-closeout-retest-2026-10-04.md#qualified).
[Canonical LEG29](../../../../plan/src收尾总清单.md#leg29).
