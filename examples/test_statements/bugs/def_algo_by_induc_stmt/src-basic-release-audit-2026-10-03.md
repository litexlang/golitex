# Statement audit: DefAlgoByInducStmt

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `trust` (authoring / automation boundary). Explicit countdown chains pass in persistent sessions; strengthened owning files were probed separately and their exact results are retained in `release_basics/proof_journals/authoring-files.json`. This is not evidence of incorrect mathematics. Repair ownership: category 1, preserve the goal and use checked explicit steps; only diagnose local Rust behavior if the explicit route itself fails. Shared search changes require discussion.

## DefAlgoByInducStmt/whole-file

```litex
# Stmt: DefAlgoByInducStmt
# AST: Stmt::Definition::DefAlgoByInducStmt
# Run all scenarios and boundaries: python3 examples/test_statements/run.py --leaf DefAlgoByInducStmt

# case: countdown-mathematical-equation
algo algo_count(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: algo_count(n - 1)
algo_count(0) = 0
algo_count(1) = 0
algo_count(2) = algo_count(2 - 1) = algo_count(1) = 0

# case: identity-evaluation
algo algo_identity(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: n
eval algo_identity(3)

# case: increment-mathematical-equation
algo algo_inc(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: algo_inc(n - 1) + 1
algo_inc(0) = 0
algo_inc(1 - 1) = algo_inc(0) = 0
algo_inc(1) = algo_inc(1 - 1) + 1

# case: nested-induction-cases
algo nested_algo(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1:
        case n = 1: 0
        case n != 1: nested_algo(n - 1)
nested_algo(0) = 0
nested_algo(1) = 0

# case: recursive-computation
algo compute_count(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: compute_count(n - 1)
eval compute_count(2)
```

Observed: ["success differs from expectation", "exit code differs from expectation", "positive contains an error or no executed statements"]

```json
{
  "kind": "run",
  "success": false,
  "target": "file",
  "path": "/Users/shenjiachen/\u4e3b\u8981\u6587\u4ef6\u5939/GeekGems/litex/golitex/tmp/2026-10-03/src-basic-release-audit/snapshot/examples/test_statements/def_algo_by_induc_stmt.lit",
  "detail": "normal",
  "language": "en",
  "statement_results": [
    {
      "success": true,
      "statement": "algo algo_count(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: algo_count(n - 1)",
      "proof_method": {
        "type": "definition",
        "rule_name": "Define algo by induction",
        "message": "Define an algorithm by induction"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": true,
      "statement": "algo_count(0) = 0",
      "proof_method": {
        "type": "object_definition",
        "rule_name": "Object definition",
        "message": "Equality follows from an object definition"
      },
      "stores": [
        "algo_count(0) = 0"
      ],
      "infers": []
    },
    {
      "success": false,
      "statement": "algo_count(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "algo_count(1) = 0"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": false,
      "statement": "algo_count(2) = algo_count(2 - 1) = algo_count(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "algo_count(2) = algo_count(2 - 1) = algo_count(1) = 0"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": true,
      "statement": "algo algo_identity(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: n",
      "proof_method": {
        "type": "definition",
        "rule_name": "Define algo by induction",
        "message": "Define an algorithm by induction"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": true,
      "statement": "eval algo_identity(3)",
      "proof_method": {
        "type": "command",
        "rule_name": "Eval",
        "message": "Evaluate an exact numeric, function or finite aggregate expression"
      },
      "stores": [],
      "infers": [],
      "evaluated_object": "3"
    },
    {
      "success": true,
      "statement": "algo algo_inc(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: algo_inc(n - 1) + 1",
      "proof_method": {
        "type": "definition",
        "rule_name": "Define algo by induction",
        "message": "Define an algorithm by induction"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": true,
      "statement": "algo_inc(0) = 0
```

## DefAlgoByInducStmt/countdown-mathematical-equation

```litex
algo algo_count(n N) N by induc n from 0:
    case n = 0: 0
    case n >= 1: algo_count(n - 1)
algo_count(0) = 0
algo_count(1) = 0
algo_count(2) = algo_count(2 - 1) = algo_count(1) = 0
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
      "statement": "algo algo_count(n N) N by induc n from 0:\n    case n = 0: 0\n    case n >= 1: algo_count(n - 1)",
      "proof_method": {
        "type": "definition",
        "rule_name": "Define algo by induction",
        "message": "Define an algorithm by induction"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": true,
      "statement": "algo_count(0) = 0",
      "proof_method": {
        "type": "object_definition",
        "rule_name": "Object definition",
        "message": "Equality follows from an object definition"
      },
      "stores": [
        "algo_count(0) = 0"
      ],
      "infers": []
    },
    {
      "success": false,
      "statement": "algo_count(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "algo_count(1) = 0"
      },
      "stores": [],
      "infers": []
    },
    {
      "success": false,
      "statement": "algo_count(2) = algo_count(2 - 1) = algo_count(1) = 0",
      "why_failed": {
        "phase": "search_proof",
        "goal": "algo_count(2) = algo_count(2 - 1) = algo_count(1) = 0"
      },
      "stores": [],
      "infers": []
    }
  ],
  "session_error": null
}
```

Acceptance: unchanged semantic goal with a checked explicit proof, plus wrong-result/domain/rollback controls. A verified explicit proof closes authoring debt without requiring stronger automatic recursion.
