# Statement audit: HaveFnByInducStmt

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `trust` (authoring / automation boundary). Explicit countdown chains pass in persistent sessions; strengthened owning files were probed separately and their exact results are retained in `release_basics/proof_journals/authoring-files.json`. This is not evidence of incorrect mathematics. Repair ownership: category 1, preserve the goal and use checked explicit steps; only diagnose local Rust behavior if the explicit route itself fails. Shared search changes require discussion.

## HaveFnByInducStmt/whole-file

```litex
# Stmt: HaveFnByInducStmt
# AST: Stmt::Definition::HaveFnByInducStmt
# Run all scenarios and boundaries: python3 examples/test_statements/run.py --leaf HaveFnByInducStmt

# case: countdown-recursion
have fn ind_count(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: ind_count(n - 1)
ind_count(0) = 0
ind_count(1) = 0
ind_count(2) = ind_count(2 - 1) = ind_count(1) = 0

# case: nonrecursive-step
have fn ind_identity(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: n
ind_identity(3) = 3

# case: recursive-increment
have fn ind_inc(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: ind_inc(n - 1) + 1
ind_inc(0) = 0
ind_inc(1 - 1) = ind_inc(0) = 0
ind_inc(1) = ind_inc(1 - 1) + 1

# case: nested-induction-cases
have fn nested_count(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1:
        case n = 1: 0
        case n != 1: nested_count(n - 1)
nested_count(0) = 0
nested_count(1) = 0
```

Observed: ["success differs from expectation", "exit code differs from expectation", "positive contains an error or no executed statements"]

```json
{
  "kind": "run",
  "success": false,
  "target": "file",
  "path": "/Users/shenjiachen/\u4e3b\u8981\u6587\u4ef6\u5939/GeekGems/litex/golitex/tmp/2026-10-03/src-basic-release-audit/snapshot/examples/test_statements/have_fn_by_induc_stmt.lit",
  "detail": "normal",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "statement": "have fn ind_count(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: ind_count(n - 1)",
      "proof_method": {
        "type": "define_fn",
        "rule_name": "Have function by induction",
        "message": "Define a function by induction on naturals"
      },
      "stores": [
        "ind_count $in fn (n N) N"
      ],
      "infers": [
        "forall n N:\n    n = 0\n    =>:\n        ind_count(n) = 0",
        "forall n N:\n    n >= 1\n    =>:\n        ind_count(n) = ind_count(n - 1)"
      ]
    },
    {
      "success": true,
      "statement": "ind_count(0) = 0",
      "proof_method": {
        "type": "object_definition",
        "rule_name": "Object definition",
        "message": "Equality follows from an object definition"
      },
      "stores": [
        "ind_count(0) = 0"
      ],
      "infers": []
    },
    {
      "success": false,
      "statement": "ind_count(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "ind_count(1) = 0"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": false,
      "statement": "ind_count(2) = ind_count(2 - 1) = ind_count(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "ind_count(2) = ind_count(2 - 1) = ind_count(1) = 0"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": true,
      "statement": "have fn ind_identity(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: n",
      "proof_method": {
        "type": "define_fn",
        "rule_name": "Have function by induction",
        "message": "Define a function by induction on naturals"
      },
      "stores": [
        "ind_identity $in fn (n N) N"
      ],
      "infers": [
        "forall n N:\n    n = 0\n    =>:\n        ind_identity(n) = 0",
        "forall n N:\n    n >= 1\n    =>:\n        ind_identity(n) = n"
      ]
    },
    {
      "success": true,
      "statement": "ind_identity(3) = 3",
      "proof_method": {
        "type": "object_definition",
        "rule_name": "Object definition",
        "message": "Equality follows from an object definition"
      },
      "stores": [
        "ind_identity(3) = 3"
      ],
      "infers": []
    },
    {
   
```

## HaveFnByInducStmt/countdown-recursion

```litex
have fn ind_count(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: ind_count(n - 1)
ind_count(0) = 0
ind_count(1) = 0
ind_count(2) = ind_count(2 - 1) = ind_count(1) = 0
```

Observed: ["success differs from expectation", "exit code differs from expectation", "positive contains an error or no executed statements"]

```json
{
  "kind": "run",
  "success": false,
  "target": "eval",
  "path": null,
  "detail": "normal",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "statement": "have fn ind_count(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: ind_count(n - 1)",
      "proof_method": {
        "type": "define_fn",
        "rule_name": "Have function by induction",
        "message": "Define a function by induction on naturals"
      },
      "stores": [
        "ind_count $in fn (n N) N"
      ],
      "infers": [
        "forall n N:\n    n = 0\n    =>:\n        ind_count(n) = 0",
        "forall n N:\n    n >= 1\n    =>:\n        ind_count(n) = ind_count(n - 1)"
      ]
    },
    {
      "success": true,
      "statement": "ind_count(0) = 0",
      "proof_method": {
        "type": "object_definition",
        "rule_name": "Object definition",
        "message": "Equality follows from an object definition"
      },
      "stores": [
        "ind_count(0) = 0"
      ],
      "infers": []
    },
    {
      "success": false,
      "statement": "ind_count(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "ind_count(1) = 0"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": false,
      "statement": "ind_count(2) = ind_count(2 - 1) = ind_count(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "ind_count(2) = ind_count(2 - 1) = ind_count(1) = 0"
      },
      "stores": [],
      "infers": []
    }
  ],
  "session_error": null
}
```

## boundary/recursive-equation-explicit-chain

```litex
# Task: K003 reclassified as a current proof-search limitation on 2026-10-02.
# Run: target/release/litex -lang en -strict -f examples/test_statements/boundaries/recursive-equation-explicit-chain.lit

have fn f(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: f(n - 1)
f(0) = 0
f(1) = 0
f(2) = f(2 - 1) = f(1) = 0

# Former short assertion: f(2) = 0
# The user classifies the required explicit steps as a current capability limit,
# not a verifier bug. Preserve the accepted chain as normal regression coverage.
```

Observed: ["success differs from expectation", "exit code differs from expectation", "positive contains an error or no executed statements", "statement success sequence differs"]

```json
{
  "kind": "run",
  "success": false,
  "target": "file",
  "path": "/Users/shenjiachen/\u4e3b\u8981\u6587\u4ef6\u5939/GeekGems/litex/golitex/tmp/2026-10-03/src-basic-release-audit/snapshot/examples/test_statements/boundaries/recursive-equation-explicit-chain.lit",
  "detail": "normal",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "statement": "have fn f(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: f(n - 1)",
      "proof_method": {
        "type": "define_fn",
        "rule_name": "Have function by induction",
        "message": "Define a function by induction on naturals"
      },
      "stores": [
        "f $in fn (n N) N"
      ],
      "infers": [
        "forall n N:\n    n = 0\n    =>:\n        f(n) = 0",
        "forall n N:\n    n >= 1\n    =>:\n        f(n) = f(n - 1)"
      ]
    },
    {
      "success": true,
      "statement": "f(0) = 0",
      "proof_method": {
        "type": "object_definition",
        "rule_name": "Object definition",
        "message": "Equality follows from an object definition"
      },
      "stores": [
        "f(0) = 0"
      ],
      "infers": []
    },
    {
      "success": false,
      "statement": "f(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "f(1) = 0"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": false,
      "statement": "f(2) = f(2 - 1) = f(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "f(2) = f(2 - 1) = f(1) = 0"
      },
      "stores": [],
      "infers": []
    }
  ],
  "session_error": null
}
```

Acceptance: unchanged semantic goal with a checked explicit proof, plus wrong-result/domain/rollback controls. A verified explicit proof closes authoring debt without requiring stronger automatic recursion.
