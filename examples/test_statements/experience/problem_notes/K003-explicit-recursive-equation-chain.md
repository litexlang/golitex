# K003: explicit recursive equality chain

## Task context

- Task: user correction on 2026-10-02 during the first three-issue discussion.
- Scope: HaveFnByInducStmt proof authoring and statement-suite classification.
- Related workspace: golitex.

## Decision

The user classifies the unsupported direct proof shortcut as a current Litex proof-search capability limitation, not a bug. K003 is removed from the open bug inventory. No kernel repair is claimed or included in this change.

The original definition, `f(0) = 0`, and `f(1) = 0` passed in the captured baseline, while the final `f(2) = 0` did not. Preserve that historical observation in [k003_prior_classification.json](../../proof_journals/k003_prior_classification.json). The earlier investigation remains in [k003_equality_diagnosis.json](../../proof_journals/k003_equality_diagnosis.json).

## Accepted source

```litex
have fn f(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: f(n - 1)
f(0) = 0
f(1) = 0
f(2) = f(2 - 1) = f(1) = 0
```

Active fixture: [recursive-equation-explicit-chain.lit](../../boundaries/recursive-equation-explicit-chain.lit). It is a normal successful boundary/regression input in the manifest, using strict mode and requiring all four statements to succeed. The original short assertion is retained as a comment in that file.

## Verification

```bash
target/release/litex -lang en -strict -f examples/test_statements/boundaries/recursive-equation-explicit-chain.lit
python3 examples/test_statements/run.py --leaf HaveFnByInducStmt
```

Acceptance result: exit 0, JSON `success: true`, four successful statements. Keep the existing nondecreasing-recursion and wrong-base-carrier rejection controls. K004 later adopted the user's [explicit arithmetic chain](K004-explicit-recursive-increment-chain.md) under the same authoring principle.

Current acceptance capture: [k003_explicit_chain.json](../../proof_journals/k003_explicit_chain.json).

## Authoring lesson

Use the explicit equality chain to expose the recursive equation, normalize its argument, and reuse an already established value. A missing automatic shortcut alone does not establish a verifier defect.
