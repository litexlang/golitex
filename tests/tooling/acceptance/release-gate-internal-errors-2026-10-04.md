# Release gate counts and internal errors — 2026-10-04

The maintainer selected strict execution accounting and an explicit internal-bug Error. Multi-language output remains ongoing development owned elsewhere.

## Zero execution must fail

Before, Cargo exit0 alone produced gate success:

```text
running 0 tests
test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 800 filtered out; finished in 0.00s
```

The same output now produces gate Failed with selected=0, executed=0 and `zero tests executed; check the registered Cargo filter`. Both controller and direct paths use the same validator. It pairs every running count with a complete summary, verifies the arithmetic, requires actual passing execution, and rejects failed, ignored/measured, malformed or unfinished targets. Empty bin/doc targets around a genuine passing target are allowed. Reported process exits remain real Cargo exits, even when the gate separately rejects an exit0 run.

16 tooling tests pass. Actual Cargo producer-consumer controls confirm passing1/1, absent-filter0/0 rejection, assertion-failure rejection and ignored1/0 rejection. The independently registered control project is receipt-owned; it is not Litex corpus coverage.

The old `run_docs_markdown_files`, `run_examples_only` and `run_showcases` filters are in memorial sources rather than the current inventory. The stricter gate rejects empty selections. Restore real collectors and verify their file inventory under REL02 before treating deployment as accepted. This repair does not substitute a small smoke suite for those corpora.

## Internal conflicts explicitly identify Litex

The existing merge branch returns:

```rust
Err(RuntimeError::InternalBug(
    "merge_exec_env_from: identifier `x` already defined in parent".into(),
))
```

Its public text is now:

```text
internal_bug: Litex internal bug: merge_exec_env_from: identifier `x` already defined in parent
```

RuntimeError owns this formatting. CLI, REPL, extraction and Normal/Compact/Detailed session_error projections expose the specific cause. The REPL already stops on hard errors; no state, merge, rollback or AST changes were made by this repair. Other session-error strings keep their previous representation, and ordinary failed proofs remain statement failures.

The synthetic invariant fixture merges two independently valid environments with the same identifier. It confirms an actual InternalBug return and projection, but does not claim normal Litex input can cause the conflict. Three release Rust tests pass, covering collision return, all projection levels/extraction, REPL text, and ordinary failure distinctions. Six captured release CLI controls pass, including negative-leading source, false fact, parser/duplicate-name errors, failed-binding correction and invalid launch option.

## Verification identity and limits

Production release build passed. Shared source changed during active language/eval work. The later live obsolete-filter attempt stopped at compile exit101 and was not a zero-test replay; its failed log is retained. Zero-selection accounting was independently verified against real Cargo output. Full all-targets/corpus/textbook/10-language deployment gates were not run by this local diagnostic/tool repair. A concurrent AST file diff only updates eval comments; this task edits no AST or protected state.

[Machine record](release-gate-internal-errors-2026-10-04.json) · [Complete receipt](release-gate-internal-errors-2026-10-04_receipts.zip)
