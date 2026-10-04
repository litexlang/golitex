# Object audit: intersect

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `kernel_problem` (provisional), except a documented unsupported signature or checked authoring route is non-kernel debt. Repair ownership: provisional, diagnosing; check explicit existing proof paths before proposing local Rust work. Escalate before changing shared policy or protected state/AST.

## P05

Original fixture: `examples/test_objs/intersect.lit`.

```litex
sketch:
    not 1 $in intersect({1, 2}, {2, 3})
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
          "step_index": 0,
          "result": {
            "success": false,
            "statement": "not 1 $in intersect({1, 2}, {2, 3})",
            "why_failed": {
              "phase": "search_proof",
              "goal": "not 1 $in intersect({1, 2}, {2, 3})"
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
