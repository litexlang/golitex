# K008: cart domain excluded from current scope

## Task context

- Task: user explicitly excludes cart support on 2026-10-02 while discussing K005/K008.
- Scope: ByForStmt finite Cartesian-product carrier and issue records.
- Related workspace: golitex.

## Decision

The user does not accept this cart feature for now. K008 is removed from the bug-oriented record folder and owner checklist. It is an explicit current rejection boundary; no Cartesian enumeration capability was added or requested by this cleanup.

## Boundary input

```litex
by for:
    ? forall p cart({1, 2}, {3, 4}):
        p = p
```

Active rejection fixture: [unsupported-cartesian-for-domain.lit](../../boundaries/unsupported-cartesian-for-domain.lit).

```bash
target/release/litex -lang en -strict -f examples/test_statements/boundaries/unsupported-cartesian-for-domain.lit
python3 examples/test_statements/run.py --leaf ByForStmt
```

The direct input must reject with exit 1 and an unsuccessful `by_for` result. The manifest treats that rejection as an expected boundary. Ordinary list-set and integer-range enumeration retain their positive controls.

Historical source, note, and captured output: [k008_prior_record.json](../../proof_journals/k008_prior_record.json).
Current focused acceptance: [k008_scope_verification.json](../../proof_journals/k008_scope_verification.json).

The reusable distinction is between an unsupported chosen interface and a promised capability that fails. This user decision supersedes the original request to support the Cartesian carrier.
