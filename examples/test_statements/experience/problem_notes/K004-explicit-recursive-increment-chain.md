# K004: explicit recursive increment chain

Task: the user supplied the arithmetic equality chain on 2026-10-02.
Scope: HaveFnByInducStmt proof authoring in golitex.

The supplied proof already succeeds on the baseline release. The former direct final assertion `f(1) = 1` was an automatic proof-search limitation; it is removed from the open bug inventory. No recursive evaluator or arithmetic equality rule was changed for K004.

```litex
have fn f(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: f(n - 1) + 1
f(0) = 0
f(1 - 1) = f(0) = 0
f(1) = f(1 - 1) + 1 = 0 + 1 = 1
```

Active fixture: [recursive-increment-explicit-chain.lit](../../boundaries/recursive-increment-explicit-chain.lit). Strict acceptance requires four successful statements. The chain shows the recursive equation, replaces the child call with its established value, and calculates the sum. Keep the nondecreasing-recursion and bad-base-carrier rejection controls.

Baseline verification: [k004_k010_baseline.json](../../proof_journals/k004_k010_baseline.json). The old input, note, and captured failure are preserved in [prior records](../../proof_journals/k004_k010_d001_prior_records.json); removing the open folder does not erase that historical observation.

```bash
python3 examples/test_statements/run.py --leaf HaveFnByInducStmt
```

Final acceptance and provenance: [focused acceptance](../../proof_journals/k004_k010_d001_acceptance.json).
