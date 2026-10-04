# Object audit: product

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `kernel_problem` (provisional), except a documented unsupported signature or checked authoring route is non-kernel debt. Repair ownership: provisional, diagnosing; check explicit existing proof paths before proposing local Rust work. Escalate before changing shared policy or protected state/AST.

## P103

Original fixture: `examples/test_objs/product.lit`.

```litex
sketch:
    have n N+
    have c R*
    have f fn(k Z) R
    product(1,n,fn(k Z) R* {c}) = c^n
    product(1,n+1,f) = product(1,n,f)*product(n+1,n+1,f)
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
            "statement": "product(1, n, fn (k Z) R*{c}) = c ^ n",
            "why_failed": {
              "phase": "search_proof",
              "goal": "product(1, n, fn (k Z) R*{c}) = c ^ n"
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

## P104

Original fixture: `examples/test_objs/product.lit`.

```litex
sketch:
    have f fn(k Z) R
    forall a,b,t Z:
        a <= b
        a+t <= b+t
        =>:
            product(a,b,fn(k Z) R {f(k+t)}) = product(a+t,b+t,f)
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
            "statement": "forall a, b, t Z:\n    a <= b\n    a + t <= b + t\n    =>:\n        product(a, b, fn (k Z) R{f(k + t)}) = product(a + t, b + t, f)",
            "why_failed": {
              "phase": "search_proof",
              "goal": "forall a, b, t Z:\n    a <= b\n    a + t <= b + t\n    =>:\n        product(a, b, fn (k Z) R{f(k + t)}) = product(a + t, b + t, f)"
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
