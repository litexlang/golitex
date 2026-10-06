# Bare theorem calls use release thm

> Historical audit: these code fences preserve dated verifier observations,
> including rejected inputs and excerpts that depend on their original context.
> They are evidence, not current standalone tutorial examples. The maintained
> executable language examples are in the Manual, README, and examples corpus.

Recorded on 2026-10-05. This is an equivalent-spelling migration of current
documentation, examples and geometry sources. The parser compatibility alias
remains available. No parser, verifier, AST, runtime, configuration, theorem
statement or proof assumption changed.

## Representative before and current source

The actual example is
[`stored_equality_before_builtin.lit`](../../examples/proof_nodes/equal/by_equivalence_class/stored_equality_before_builtin.lit).
This excerpt uses that file's declarations; it is not a standalone snippet.

<!-- litex:skip-test -->
```litex
# Before:
# by thm dot_symmetric(vec(ga,gb),vec(gc,gd))
# The bare alias parsed as ReleaseThmStmt and stored the theorem conclusion.

# Current:
release thm dot_symmetric(vec(ga,gb),vec(gc,gd))
```

Both versions passed the same captured release executable with `-strict -f`:
exit 0, `success: true`, `session_error: null`, seven successful statements.
The other edited example,
[`geo_coordinate_expansion.lit`](../../examples/proof_nodes/equal/by_known_special_property/geo_coordinate_expansion.lit),
passed its complete ten-statement file before and after the six replacements.

## Scope and source-delta evidence

| Source group | Replacements | Files |
| --- | ---: | ---: |
| examples | 7 | 2 |
| LitexGeo-AutoBuild/shenjiachen current geometry | 402 | 1 |
| scripts/geo.lit and LitexGeo-AutoBuild/LitexGeo/main.lit | 878 | 2 |
| LitexGeo-AutoBuild/IMO/solutions and 新geo的imo的草稿 current sources | 1,504 | 79 |
| upstream Tarski and coordinate geometry sources | 2,617 | 82 |
| Total | 5,408 | 166 |

Every changed `.lit` was compared against a pre-edit snapshot: the only byte
changes are the 5,408 accepted command tokens `by` becoming `release`. All
source lines, arguments, comments and other bytes remain unchanged. The current
scanned authoring scope has zero remaining bare release aliases. All 172 scoped
selected `by thm ... => fact` calls and the colon rejection fixture are preserved.
Historical snapshots, backups, disposable drafts, proof journals, skill corpora
and automatic-build receipts retain their original evidence.

Manual, FAQ and the learner cheatsheet now recommend `release thm` for a bare
call and describe bare `by thm` as compatibility syntax. Their 146 collected
executable documentation fences are byte-identical to the pre-edit fences.
The cheatsheet's selection description now agrees with the existing atomic-only
parser contract; a provable chain target is still rejected.

## Verification and limits

The captured executable is Litex 0.9.200-beta, SHA256
`f2bc67420d47315ea25408a12dd6343c3884fc061af19b9e5d484af4ba8df754`.
It was copied immediately after `cargo build --release` so later shared-worktree
builds cannot alter these results.

The nine focused scenarios passed their expected outcomes both before and after:
two complete edited examples, the actual geometry prefix through
`dot_commutative` (55 complete declarations), the unchanged definitions entrypoint
(40 declarations), a selected theorem example, the existing colon rejection,
a false selected fact, and two existing Manual theorem-interface fences.
An additional selected-chain control was rejected with
`expected a single atomic fact (one operator)`.

The geometry prefix was extracted from the actual source up to, excluding,
`thm dot_add_left`; no theorem or premise was edited in the excerpt. Its four
bare calls were migrated with the same whole-file operation.

A subsequent full strict check of the actual current
`scripts/LitexGeo-AutoBuild/shenjiachen/新geo和geo_definitions/geo.lit`
passed all 227 declarations: exit 0, `success: true`, `session_error: null`,
no failed statements, 2346.642 seconds. Its SHA256 remained
`1e65d971b820a5735da87c4357c58462ddb3f3ed566c6d7832b367b66c055c78` throughout the run, and the frozen executable was unchanged.
This whole-file gate does not certify every older IMO or upstream geometry
consumer. The earlier complete acceptance remains tied to its historical
source/binary hashes; the post-spelling run has a separate receipt.

Exact file hashes, line-level migration records, commands and focused results
are retained in
`tmp/2026-10-05/by-thm-release-doc-examples-geo/manifest.json`,
`source-delta-receipt.json`, `before-checks.json`, `after-checks.json`,
`full-geo-after-receipt.json` and `full-geo-after.stdout.json`.
The task-owned frozen executable ran the exact files with:

```text
tmp/2026-10-05/by-thm-release-doc-examples-geo/litex-current -strict -f examples/proof_nodes/equal/by_equivalence_class/stored_equality_before_builtin.lit
tmp/2026-10-05/by-thm-release-doc-examples-geo/litex-current -strict -f examples/proof_nodes/equal/by_known_special_property/geo_coordinate_expansion.lit
tmp/2026-10-05/by-thm-release-doc-examples-geo/litex-current -strict -f tmp/2026-10-05/by-thm-release-doc-examples-geo/geo-prefix-after.lit
tmp/2026-10-05/by-thm-release-doc-examples-geo/litex-current -strict -f scripts/LitexGeo-AutoBuild/shenjiachen/新geo和geo_definitions/geo_definitions.lit
tmp/2026-10-05/by-thm-release-doc-examples-geo/litex-current -strict -f scripts/LitexGeo-AutoBuild/shenjiachen/新geo和geo_definitions/geo.lit
```
