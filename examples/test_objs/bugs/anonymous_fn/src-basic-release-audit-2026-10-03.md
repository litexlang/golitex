# Object audit: anonymous_fn

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `kernel_problem` (provisional), except a documented unsupported signature or checked authoring route is non-kernel debt. Repair ownership: provisional, diagnosing; check explicit existing proof paths before proposing local Rust work. Escalate before changing shared policy or protected state/AST.

## P06

Original fixture: `examples/test_objs/anonymous_fn.lit`.

```litex
sketch:
    let y = 3
    fn(x R) R {x + y}(2) = 2 + y = 2 + 3 = 5
```

Observed: exit 1, success False, session_error None.

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
      "success": false,
      "statement": "sketch",
      "why_failed": {
        "type": "proof_block",
        "rule_name": "Sketch",
        "message": "Run a sketch proof block",
        "phase": "sketch",
        "failure": {
          "step_index": 1,
          "result": {
            "success": false,
            "statement": "fn (x R) R{x + y}(2) = 2 + y = 2 + 3 = 5",
            "why_failed": {
              "phase": "search_proof",
              "goal": "fn (x R) R{x + y}(2) = 2 + y = 2 + 3 = 5"
            },
            "stores": [],
            "infers": []
          }
        }
      },
      "stores": [],
      "infers": []
    }
  ],
  "session_error": null
}
```

Next/acceptance: reproduce the exact mathematical goal with the original scope; inspect WD versus search versus context/output failure; repair only after preserving the nearest false, domain and scope controls.
