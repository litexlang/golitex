# Litex Math23K Showcase

This is the small, delivery-oriented subset of the Litex Math23K artifacts.
It intentionally omits the 22,329-row extended compatibility corpus and all
blocked rows.

## Contents

| File | Rows | Purpose |
| --- | ---: | --- |
| `data/core.jsonl` | 300 | Structurally diverse, quality-filtered evaluation set |
| `data/smoke.jsonl` | 30 | Fast regression subset selected from core |
| `metadata/manifest.json` | — | Content hashes, selection boundary, and frozen verifier provenance |
| `LICENSE.md` | — | Artifact license and upstream-rights boundary |

Smoke is a subset of core, so the package contains 300 distinct problems, not
330. Use smoke after an ordinary Litex change and core for broader evaluation
or release-candidate checks.

## Selection boundary

Every delivered row:

- has `status: checkable` in the frozen verification snapshot;
- has no quality flags or proof-debt token;
- does not preassume any requested conclusion;
- has a nonempty proof body with explicit endpoints for every conclusion; and
- represents a distinct normalized structural template in core.

The 30-row smoke tier is selected from core for broad arithmetic and proof-shape
feature coverage. Selection is deterministic for the recorded source snapshot.

## Data format

Each JSONL line is one record. Important fields include `id`, `problem`,
`proof_idea`, `litex_code`, `feature_tags`, `template_id`, `status`, and
`sha256`. The `problem` field is the formal Litex goal, not the original
Chinese Math23K question.

## Verification scope

The recorded strict, isolated verification snapshot used Litex
`0.9.116-beta`, binary SHA-256
`f3600230cb2473a04756051a7eb317fe0fca988d5b0ffb424c09084164eade26`,
with a 30-second per-item timeout. Core passed 300/300 and smoke passed 30/30.

This evidence is binary-specific. Re-run the data against a different Litex
binary before claiming current compatibility; do not silently treat the frozen
status as proof that a later kernel accepts the same artifacts.

## Provenance and limitations

These are Litex conditional-calculation artifacts derived from Math23K
annotated equations. Original Chinese questions and natural-language solutions
are not included. The package is useful for Litex regression and formal-code
experiments, but it is not a source-faithful word-problem translation benchmark.
See `LICENSE.md` for the licensing boundary.
