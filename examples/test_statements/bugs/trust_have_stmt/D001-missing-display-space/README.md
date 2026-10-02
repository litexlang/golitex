# D001: Trust-have display omits the space before its first object

Status: open. Primary blocker: `kernel_problem`.

## Task context

- Task: organize statement-suite problems requested on 2026-10-02; discovered while checking captured output.
- Scope: TrustHaveStmt display in the release CLI JSON.
- Related workspace: golitex.

## Reproduction

The existing [trust_have_stmt.lit](../../../trust_have_stmt.lit) case `single-name-and-fact` is the source fixture. This issue reuses that registered input rather than adding a duplicate unlisted `.lit` file.

```litex
trust have trusted_a R:
    trusted_a = 1
trusted_a = 1
```

Run from the repository root without strict mode:

```bash
target/release/litex -lang en -e 'trust have trusted_a R:
    trusted_a = 1
trusted_a = 1'
```

## Actual and desired output

Execution returns exit 0 and `success: true`. The first `statement_results[].statement` string currently reads:

```text
trust havetrusted_a R:
    trusted_a = 1
```

It should preserve the separator between the keyword and object name:

```litex
trust have trusted_a R:
    trusted_a = 1
```

The same missing space occurs in the multiple-name and natural-carrier cases. This is a reproduced formatting defect; no independent failure of the original source's verification is claimed. Replaying the printed statement in a fresh process rejects with exit 1 and a parser error; the corrected string above passes with exit 0. The exact formatter responsible has not been isolated.

Captured JSON, original command, and both replay controls: [observed.json](observed.json). The full report also contains `TrustHaveStmt/multiple-dependent-names` and `TrustHaveStmt/typed-natural`.

Actual replay diagnostic:

```text
Runtime(ParseError(RuntimeParseError { message: "undefined name `havetrusted_a`", line: 1, path: Eval }))
```

## Next action and acceptance

- Inspect the trust-have formatter and its surrounding statement display; retain a separator for one name, multiple names, and nested template bodies.
- Require the first rendered statement to equal the expected string above; check that it parses and executes in a fresh non-strict process.
- Keep the original execution checks and [direct strict rejection](../../../boundaries/strict-trust-have-rejected.lit).
- Check the same formatter in [K006's nested template capture](../../def_template_stmt/K006-strict-template-trust-have/observed.json). The strict trust bypass remains a separate issue.

```bash
python3 examples/test_statements/run.py --leaf TrustHaveStmt
```

The runner currently checks execution, not this display string. A green run does not close D001. Record the display/round-trip check when repairing it, then retain the solution in the suite's experience records and update the index.

Back to [statement folder](../README.md) or [issue index](../../README.md).
