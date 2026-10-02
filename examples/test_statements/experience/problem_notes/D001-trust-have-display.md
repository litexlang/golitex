# D001: trust-have display separator

Task: repair the statement output defect on 2026-10-02.
Scope: TrustHaveStmt rendering and parser replay in golitex.

The [formatter](../../../../src/display_and_ir/stmt.rs) now keeps the space after `have` when displaying a fact body. The old string `trust havetrusted_a R:` failed parsing; the correct `trust have trusted_a R:` executes when replayed in a fresh non-strict runtime.

The existing [TrustHaveStmt fixture](../../trust_have_stmt.lit) covers single names, multiple dependent names, and a natural carrier. Acceptance additionally replays a template body and a bodyless declaration. All five rendered forms parse and execute; each still rejects in strict mode. This is output repair, with no change to trust policy or mathematical proof behavior.

The [round-trip Rust test](../../../../tests/unit/execute/statement_boundaries/tests.rs) protects body/no-body and multiple-name output plus strict controls. [d001_display_acceptance.json](../../proof_journals/d001_display_acceptance.json) contains the exact source, rendered text, fresh-process replay, strict rejection, commands, and release hash. [Prior records](../../proof_journals/k004_k010_d001_prior_records.json) preserve the earlier failed replay. Final focused gate results: [acceptance](../../proof_journals/k004_k010_d001_acceptance.json).

```bash
cargo test --release --lib statement_boundary_tests
python3 examples/test_statements/run.py --leaf TrustHaveStmt
```
