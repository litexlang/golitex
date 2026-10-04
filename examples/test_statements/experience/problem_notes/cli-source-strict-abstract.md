# CLI source operands and strict abstract predicates

Maintainer-authorized update: 2026-10-04. Repair ownership: category 2, local
Rust CLI and strict declaration policy. The changes add no AST/Env/Runtime
fields or state-management contracts and do not change proof search.

## Negative-leading source (BR001 resolved)

```litex
# Before:
# -2 < 0
# `litex -strict -e '-2 < 0'` exited 2 with launch_error.
# Now:
-2 < 0
```

The shell removes quoting before building argv. The scanner now consumes the
complete operand after `-e` as source and skips flag interpretation inside that
operand. `-e '-strict'` therefore reports a Litex ParseError for the undefined
name, rather than enabling strict mode. Actual shared flags outside the operand
still work before or after it. Empty/missing source and unknown/trailing CLI
arguments remain launch errors. `-2 > 0` still fails truth verification.

Persistent tracer: [negative_leading_code.lit](../../../stmt_nodes/fact/negative_leading_code.lit).
The code and live CLI commands were checked separately; the file's comments
do not substitute for executing the exact negative-leading operand.

## Abstract signatures in strict mode

```litex
# Before:
# abstract_prop strict_mark(x)
# Strict rejected the declaration itself.
# Now:
abstract_prop strict_mark(x)
forall x R:
    $strict_mark(x)
    =>:
        $strict_mark(x)
```

Persistent tracer: [strict_abstract_prop.lit](../../../stmt_nodes/definition/strict_abstract_prop.lit).
The strict policy no longer rejects abstract declarations. Registration still
adds only a signature: neither a positive nor a negative instance is proved.
Exact arity and argument WD remain required; `by def` cannot expose a body that
does not exist. User `trust` and `trust have`, including template/nested forms,
are still rejected. Existing nonstrict explicit-trust behavior is retained.

Executable boundaries: [allowed declaration](../../boundaries/strict-abstract-prop-allowed.lit)
and [unproved instances/WD/arity](../../boundaries/strict-abstract-instance-unproved.lit).

## Acceptance

- `cargo build --release --offline`: passed.
- `cargo test --release --offline --lib launch_command_tests`: 8/8.
- `cargo test --release --offline --lib predicate_signature_tests`: 10/10.
- `cargo test --release --offline --lib statement_boundary_tests`: 9/9.
- Production Stmt runner, leaves DefAbstractPropStmt, TrustStmt, TrustHaveStmt,
  DefTemplateStmt: 36/36 checks; zero gaps and unexpected failures.
- Public CLI checks, including both option orders, false mathematics, source
  ParseError, missing/unknown/trailing arguments, both tracer file gates,
  unproved abstract instances and help text: 16/16.
- The shared public release target was rebuilt during concurrent work. Five
  additional controls on that executable passed; the full scoped CLI receipt
  uses the retained verified executable and unchanged task-owned source hashes.

Reproduce the central cases:

```sh
target/release/litex -strict -e '-2 < 0'
target/release/litex -strict -e '-2 > 0'
target/release/litex -strict -f examples/stmt_nodes/definition/strict_abstract_prop.lit
python3 examples/test_statements/run.py --leaf DefAbstractPropStmt --binary target/release/litex
```

The second command intentionally returns failure. Full-kernel, textbooks,
Lean and deployment gates are outside this scoped acceptance. Exact outputs,
before evidence and source/binary identities are in
[the receipt](../../proof_journals/cli_source_strict_abstract_2026-10-04.json).
