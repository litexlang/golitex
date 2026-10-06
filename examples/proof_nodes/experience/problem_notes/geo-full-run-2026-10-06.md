# Complete latest geo run

Date: 2026-10-06, Asia/Shanghai.
Status: whole-file execution completed; 223 accepted / 4 failed; not fully verified.

The current-source release includes the user-approved local-alpha-only lookup.
The offline release build passed in about64 seconds. Build time is excluded
from the file timing below. No kernel or mathematical source was changed by
this run task.

## Exact version and command

The old canonical `scripts/geo.lit` was still using `A[1]`; it accepted one
declaration and rejected the removed indexing syntax at line9, in0.077 seconds.
During this task it was renamed externally to `scripts/旧版geo.lit`, with
identical bytes. That rejected parse is not a whole-file performance result.

The first12:41 migrated draft was superseded and its run interrupted after the
120-second heartbeat. The final input is the newer16:59 full version:

[`geometry-candidate-scalar-local.lit`](../../../../tmp/2026-10-05/tuple-cart-exact-functions/geometry-sprint-2026-10-06/geometry-candidate-scalar-local.lit).
Its227 original top-level headers match the canonical source after changing
coordinate indexing spelling. All186 theorem names remain in order. It includes
the previous task's local scalar helper inside the vertical-angle proof and
contains no trust/axiom/unsafe/know/abstract_prop statements. A byte-identical
copy is retained in the run area.

```sh
tmp/2026-10-06/geo-full-run/cargo/release/litex -strict -f tmp/2026-10-06/geo-full-run/geometry-latest.lit
```

The current CLI rejects `-compact -runner`; that rejection is separately
recorded. The supported command returns a parsed normal JSON envelope with
`success`, `session_error`, and `statement_results`; it has no `ok` field.

## Actual result

| Measure | Result |
|---|---|
| Wall time | 410.7856 s (6 min50.79 s) |
| Child CPU, user + system | 405.3893 s |
| Attempted original declarations | 227 /227 |
| Accepted | 223 |
| Failed | 4 |
| CLI exit / envelope success | 1 /false |
| Session error | null |

These are end-to-end cold CLI timings, including rendering the final output.
The small wall/CPU difference indicates this run mostly spent time computing;
it does not identify the remaining hot function. No comparable pre-change
complete-file run was performed, so no causal speedup percentage is claimed.
The timing includes four failed checks and is not an all-success benchmark.

## Failure boundaries

| Item | Latest input line | Theorem |
|---|---|---|
| 209 | 2988 | `collinear_coordinates_imply_affine_parameter` |
| 210 | 3026 | `on_line_implies_affine_parameter` |
| 211 | 3039 | `right_angle_vertex_distinct_from_foot_on_opposite_line` |
| 212 | 3081 | `right_angle_vertex_not_on_opposite_line` |

The first failure is equality search for this first adjacent step in a chain,
inside the `b(1)-a(1)=0` case:

```litex
(p(1)-a(1))*(b(2)-a(2)) = (p(1)-a(1))*(b(2)-a(2))-(p(2)-a(2))*(b(1)-a(1))
```

Items210/211 fail while searching for these membership facts respectively:

```litex
p $in {r cart(R,R): det(vec(a,r),vec(a,b))=0}
foot $in {r cart(R,R): det(vec(a,r),vec(a,b))=0}
```

Item212 cannot release the theorem that item211 failed to record:

```litex
release thm right_angle_vertex_distinct_from_foot_on_opposite_line(...)
```

The last snippet abbreviates the actual arguments; the exact returned source
and failure tree are in the raw JSON. It is a dependency cascade, not another
independently diagnosed kernel defect. No same-source old-search comparison was
run, so these failures are not attributed to the alpha policy change. Repair
and proof migration remain outside this timing request.

The [durable audit](../../../../docs/audits/geo-full-run-2026-10-06.json)
contains input/binary fingerprints, all run receipts, the exact failure goals,
the earlier interrupted-run exclusion and the unchanged-source check. The
frozen source, compiled binary, full input and raw output remain under
`tmp/2026-10-06/geo-full-run/` for reproduction.
