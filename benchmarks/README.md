# Public Benchmark Slices

This directory is for cleaned, reviewable benchmark slices. It is not a dump of
local translation workspaces.

Litex uses dataset and textbook translation as a pressure test. The goal is not
only to collect successful examples. The goal is to expose what the current
language, standard library, builtin rules, inference rules, diagnostics, and
proof style can or cannot handle.

## Publication Rule

Each public slice should be small enough for a reviewer to inspect directly:
about 20-50 representative items per source.

Do not copy an entire local dataset workspace into this directory. Full
datasets should live in a dedicated dataset repository, Hugging Face dataset,
release artifact, or private/local workspace when licensing or size makes that
more appropriate.

If source text cannot be redistributed, include a reusable mathematical
reformulation and record the license constraint in the notes.

## Slice Layout

Use this shape for each source:

```text
benchmarks/<source>/
  README.md
  current_data.json
  litex_file/
  unfinished/
  experience/
```

`current_data.json` is the public status contract. It should be generated or
updated from the source records and should let a reviewer see the current state
without understanding the private workspace layout.

## Item Contract

Each item should record:

```yaml
id:
source:
topic:
difficulty:
natural_language_idea:
litex_code:
proof_attempt:
status: translated/checkable/blocked
blocker:
notes:
```

Use `checkable` only after the relevant Litex verifier command has been run.
Use `translated` when a Litex formulation exists but fresh verification is not
claimed. Use `blocked` when the current proof attempt has a known missing
capability or proof debt.

Blocker labels should use the shared taxonomy:

- `blocked_by_language`
- `blocked_by_stdlib`
- `blocked_by_infer_rule`
- `blocked_by_kernel`
- `blocked_by_syntax`
- `blocked_by_diagnostics`
- `blocked_by_formulation`

## Relationship To Examples

`examples/` is for polished runnable demonstrations and first-contact learning.
It should stay small and readable.

`benchmarks/` is for evidence. It may include unfinished or blocked items, but
those items must be labeled clearly enough to guide future language, stdlib,
kernel, inference, or diagnostic work.

## Review Expectations

A reviewer should be able to answer:

- Which command verifies each checkable item?
- Which items still contain `know`, `abstract_prop`, or stdlib assumptions?
- Which failures are language gaps, library gaps, rule gaps, kernel gaps,
  syntax gaps, diagnostic gaps, or formulation gaps?
- Which examples should graduate into `examples/` or documentation?

See [`docs/Reviewer_Guide.md`](../docs/Reviewer_Guide.md) for the broader
review protocol.
