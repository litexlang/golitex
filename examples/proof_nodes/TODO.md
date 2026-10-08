# Migration residuals

## Task context

- Task: closed calculation and legacy builtin prop/thm migration requested on 2026-10-03, including explanation of the struct failures.
- Scope: one-field struct representation and symbolic finite-set consumers left after the bounded repairs.
- Related workspace: golitex; [audit](../../docs/audits/builtin-prop-thm-migration-2026-10-03.md), proof journal (historical task record; retired).
- Follow-up: the 2026-10-04 local template/alias repair is verified and archived in the solution record (historical task record; retired).
- User ownership: complete local authoring/Rust repairs; keep unsettled representation or global search-policy changes for discussion.

## kernel_problem

### One-field struct representation

```litex
struct ScalarOps:
    add fn(x, y R) R
```

Observed: parse failure `struct definition expects at least two fields`. The later one-field `Space` is independently affected. Parser and release both enforce the current two-field tuple/cart representation.

Classification: current syntax/representation limit, independent of template field evidence. Owner: representation decision, needs discussion before implementation. Next action: specify the intended one-field representation and its constructor/projection laws; do not remove only the parser guard or add a dummy field. Acceptance: exact single-field source and lawful projection/callable use pass with wrong-field and wrong-type rejection.

### Symbolic chained finiteness and subset cardinality

```litex
forall A, B set, F finite_set:
    A $subset B
    B $subset F
    =>:
        $is_finite_set(A)
```

Observed: strict CLI rejection; the corresponding direct finite upper-set case passes. Additional exact Rust cardinality cases fail at their recorded checkpoint. Existing source-owned Rust failure records (historical task record; retired) preserve the four test failures. A combined CLI proof and its Runtime-based Rust fixture have differed, so source/binary and entry-context comparisons must precede causal claims.

Classification: verification/WD/search composition or harness/environment drift, exact root not established. Repair ownership provisional; global permissions, state lifetime and protected structure changes require discussion. Next action: reproduce the exact Runtime entry and CLI entry at one stable build, retain detailed first-failure evidence, then repair the established local owner. Acceptance: all seven `cargo test --release --lib finite_set_cardinality_rule` tests and the unchanged CLI cases pass, with their existing false-premise, false-equality and scope controls.
