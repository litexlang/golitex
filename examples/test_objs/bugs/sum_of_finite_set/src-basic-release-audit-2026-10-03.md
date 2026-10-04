# Object audit: sum_of_finite_set

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `kernel_problem` (provisional), except a documented unsupported signature or checked authoring route is non-kernel debt. Repair ownership: provisional, diagnosing; check explicit existing proof paths before proposing local Rust work. Escalate before changing shared policy or protected state/AST.

## P103

Original fixture: `examples/test_objs/sum_of_finite_set.lit`.

```litex
sketch:
    have S finite_set
    have c R
    have f,g fn(k S) R
    finite_set_sum(S,fn(k S) R {c}) = finite_set_size(S)*c
    finite_set_sum(S,fn(k S) R {f(k)+g(k)}) = finite_set_sum(S,f)+finite_set_sum(S,g)
    finite_set_sum(S,fn(k S) R {f(k)-g(k)}) = finite_set_sum(S,f)-finite_set_sum(S,g)
    finite_set_sum(S,fn(k S) R {c*f(k)}) = c*finite_set_sum(S,f)
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
          "step_index": 3,
          "result": {
            "success": false,
            "statement": "finite_set_sum(S, fn (k S) R{c}) = finite_set_size(S) * c",
            "why_failed": {
              "phase": "search_proof",
              "goal": "finite_set_sum(S, fn (k S) R{c}) = finite_set_size(S) * c"
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

## P106

Original fixture: `examples/test_objs/sum_of_finite_set.lit`.

```litex
sketch:
    algo flag(x R) R by cases:
        case x = 0: 0
        case x != 0: 1
    finite_set_sum({1/3,2/3},flag) = 2
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
            "statement": "finite_set_sum({1 / 3, 2 / 3}, flag) = 2",
            "why_failed": {
              "phase": "search_proof",
              "goal": "finite_set_sum({1 / 3, 2 / 3}, flag) = 2"
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
