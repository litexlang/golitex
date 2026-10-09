# Selected scalar bt rules: scoped acceptance

The user selected two-pair subtraction, absolute square-radius bounds,
positive-denominator quotient upper bounds and exact integer quotient typing.
Factor cancellation was excluded from this task. The existing forward absolute
nonzero rule and its denominator consumer were checked without duplication.

```litex
forall a,b,c,d R:
    a<=b
    c<=d
    =>:
        a-d<=b-c
```

Before this change, that direct target missed `search_proof`; the explicit
`a-d<=b-d<=b-c` chain passed. The new `SubtractionOrderPairs` leaf retains
both actual source comparisons. Checked strict comparisons may satisfy its
weak guards at the same inherited ceiling. Weak premises still do not imply
the false strict target `a-d<b-c`.

The other accepted shapes are `r>=0, x^2<=r^2 => abs(x)<=r`,
`b>0, a<=M*b => a/b<=M` (including its strict counterpart), and
`a,b in Z, b!=0, a%b=0 => a/b in Z`. Quotient comparison accepts either
placement of the source product. Integer quotient typing allows either divisor
sign; it retains the stated nonzero premise and does not assert natural-number
membership. The additional attempt using only `b<0` instead of `b!=0`
missed in this task; no broader nonzero inference change was made.

Implementation is owned by `selected_scalar_bt_rules.rs` and its existing
atomic dispatchers. Every guard is retained in Detailed output. No AST,
Env/Runtime state, transaction, global search ceiling or compiler adapter was
changed by this task. All output locales and explicitly unsupported Lean
compilation were checked.

## Verified scope

An isolated source snapshot of HEAD plus the exact task files passed:

- `cargo test --release --manifest-path tmp/2026-10-09/selected-scalar-bt-rules/overlay/Cargo.toml selected_scalar_bt_rules_tests -- --nocapture`: 6 tests.
- The same command with `abs_positive_square_reflection_tests`,
  `signed_difference_order_tests`, `negative_common_factor_order_tests` and
  `builtin_entry_policy_tests`: 30 additional tests.
- Six dedicated examples under `examples/proof_nodes/atomic/by_builtin_rule/`:
  `subtraction_order_pairs`, `abs_square_radius`, `quotient_scalar_upper_bound`,
  `quotient_scalar_strict_upper_bound`, `exact_integer_quotient` and
  `abs_nonzero_denominator_consumer`. Each ran with the snapshot release binary,
  `-lang en -strict -f <repository-example-path>`, exit 0, `kind: run`,
  `success: true`, and `session_error: null`.
- A live Session replay accepted the primary tracer, rejected its false strict
  counterpart, then accepted the strict-premise weak target in that same Session.

The scoped collector `run_examples_selected_scalar_bt_tracers` executes all six
maintained examples. No full corpus, textbook or release acceptance is claimed.
[Machine receipt](acceptance.json) preserves binary and
task-file hashes, exact file commands, suite counts and the integration boundary.

## Historical working-tree build block

`cargo build --release` currently fails in unrelated concurrent
`src/compile_to_lean/litex_to_lean_compiler.rs` edits. For example, code refers
to `self.scopes` although the current `LitexToLeanCompiler<'a>` has no such
field; other signatures have missing or inconsistent lifetimes. Those files
were not overwritten or repaired by this task. The current worktree binary
has not been refreshed with these new rules.

After those edits build, run `cargo build --release`,
`cargo test --release selected_scalar_bt_rules_tests -- --nocapture`, and the
six root `target/release/litex -lang en -strict -f <example>` gates. Until then,
the implementation had scoped snapshot acceptance and pending working-tree
integration. The reproducible snapshot, journals and logs remain in the one
task-owned draft directory named above.

## Current working-tree acceptance

The current worktree subsequently rebuilt successfully on 2026-10-09. All six
dedicated strict release files passed with `target/release/litex`, and the six
new plus thirty neighboring Rust tests passed on the current source. The paired
receipt's `worktree_integration` records the new binary hash, actual commands,
Normal output and suite counts; it supersedes the historical build block.
The existing explicit unsupported-Lean checks still pass: no new adapter was
added. No full corpus or release-package gate is claimed.

Unrelated source files changed during this verification window. Executable
identity and source limits are recorded; acceptance of these exact cases is
not a claim that an entire immutable checkout or every concurrent change was
audited. The completed execution ledger can now be removed.

## Selected-scope recheck

A further current-source release build and the six selected Rust tests passed.
All six maintained examples passed independent `-lang en -strict -f` gates;
missing-guard and false-conclusion controls remained rejected in the Rust suite.
The paired JSON records this under `latest_selected_scope_recheck`.
