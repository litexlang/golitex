# Nonempty proof processes — 2026-10-12 acceptance

The parser rejects a claim with only a goal. Previously this reached ordinary
goal verification; the same source now returns a parse error:

```litex
claim:
    ? 1 = 1
```

Current result: `claim: expects a nonempty proof body`, at the claim header.
The checked replacement is an actual process, or a direct fact when no local
proof commands are needed:

```litex
claim:
    ? exist x R st {x = 0}
    witness exist x R st {x = 0} from 0
1 = 1
```

`sketch`, `strategy`, block extensionality, finite enumeration, range proofs,
induction, explicit induction sections and every proof case require processes.
Inline commands remain supported. A witness/Choice/Zorn header can explicitly
omit its optional process; adding its trailing proof colon requires a body.
All comment-only colon bodies, including fact bodies, are rejected by the
tokenizer. `thm` processes remain optional, and unsupported goals still fail
verification. A checked `impossible` closing statement is itself a process step.

## Focused evidence

- `tests/unit/parse/nonempty_proof_bodies.rs`: all five new tests passed.
- `tests/unit/tokenize/nonempty_blocks.rs`: all three new tests passed.
- The registered Rust run passed all 32 parser and 19 tokenizer tests.
- `target/release/litex -lang en -strict -f examples/stmt_nodes/proof_block/nonempty_proof_bodies.lit`: exit 0; `kind: run`, `run_result: "success"`, `session_terminated: false`, `termination: null`.
- 51 release-CLI syntax/proof boundary cases passed; 386 available Stmt checks passed using the existing collector's per-case functions.
- Singleton indexed-intersection enumeration uses `idx = 1` as its process. Repeating `x $in A(idx)` failed; the corrected theorem succeeded in the same Session and its strict file gate passed.
- No mathematical goals were weakened and no Litex trust statements were added. AST and Env/Runtime structures were not changed.

## Broader gate limits

`cargo test --release --all-targets --no-fail-fast` ran the registered targets.
Its first completed library run had 1609 passing and 59 failing tests. Two
remaining goal-only claim/strategy fixtures were migrated; the follow-up
`cargo test --release --lib -- --nocapture` had 1611 passing and 57 failing
tests, with every parser/tokenizer test passing and no missing-process parse
errors in the failures. Other failures involve concurrently edited inference,
WD and Lean compilation contracts; this change does not certify those contracts.

`python3 tests/tooling/run_docs_markdown_files.py` checked 894 fences: 886
passed and 8 failed. Examples include the unchanged `$prime(5)` producing an
inferred-fact WD error and unchanged explicit subset/fn-extension proofs
failing under the concurrent inference changes. The migrated versions of the
failed docs still passed the saved earlier release binary.

`python3 examples/test_statements/run.py --binary target/release/litex --require-no-gaps`
stopped at its inventory audit because seven referenced `bugs/**/repro.lit`
fixtures were already absent. The 386 checks whose files exist were run
without changing the collector or hiding the inventory discrepancy.

61 of the 62 migrated positive example files passed. The remaining
`examples/infer/atomic/set_builder_projection_replay.lit` also passed the
earlier binary with the migrated source, but its unchanged `value > 0`
process currently fails under the concurrent builder-inference changes.
Workspace-local textbook/script corpora and public showcase books were not
migrated in this parser task.

The policy-required `python3 scripts/textbook_gate.py The-Mechanics-of-Litex-Proof`
also ran. It stopped at `scripts/The-Mechanics-of-Litex-Proof/textbook/citation.lit:68`
with `parse_error: unexpected end of tokens`, on a proof case still omitting
its colon/process. This is an expected book migration requirement from the
new case contract, not a passing whole-book check.
