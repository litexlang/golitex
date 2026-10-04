# Object audit: sum

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `kernel_problem` (provisional), except a documented unsupported signature or checked authoring route is non-kernel debt. Repair ownership: provisional, diagnosing; check explicit existing proof paths before proposing local Rust work. Escalate before changing shared policy or protected state/AST.

## P106

Original fixture: `examples/test_objs/sum.lit`.

```litex
sketch:
    algo flag(x R) R by cases:
        case x = 0: 0
        case x != 0: 1
    sum(0,3,flag) = 3
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
            "statement": "sum(0, 3, flag) = 3",
            "why_failed": {
              "phase": "search_proof",
              "goal": "sum(0, 3, flag) = 3"
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

## P107

Original fixture: `examples/test_objs/sum.lit`.

```litex
sketch:
    have n N+
    have c R
    have f,g fn(k Z) R
    sum(1,n,fn(k Z) R {c}) = n*c
    sum(1,n,fn(k Z) R {f(k)+g(k)}) = sum(1,n,f)+sum(1,n,g)
    sum(1,n,fn(k Z) R {f(k)-g(k)}) = sum(1,n,f)-sum(1,n,g)
    sum(1,n,fn(k Z) R {c*f(k)}) = c*sum(1,n,f)
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
            "statement": "sum(1, n, fn (k Z) R{c}) = n * c",
            "why_failed": {
              "phase": "search_proof",
              "goal": "sum(1, n, fn (k Z) R{c}) = n * c"
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

## P108

Original fixture: `examples/test_objs/sum.lit`.

```litex
sketch:
    have n N+
    have f fn(k Z) R
    sum(1,n+1,f) = sum(1,n,f)+sum(n+1,n+1,f)
    sum(1,n,fn(k Z) Z {k+k}) = sum(1,n,fn(j Z) Z {2*j})
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
            "statement": "sum(1, n, fn (k Z) Z{k + k}) = sum(1, n, fn (j Z) Z{2 * j})",
            "why_failed": {
              "phase": "search_proof",
              "goal": "sum(1, n, fn (k Z) Z{k + k}) = sum(1, n, fn (j Z) Z{2 * j})"
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

## P109

Original fixture: `examples/test_objs/sum.lit`.

```litex
sketch:
    have f fn(k Z) R
    forall a,b,t Z:
        a <= b
        a+t <= b+t
        =>:
            sum(a,b,fn(k Z) R {f(k+t)}) = sum(a+t,b+t,f)
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
            "statement": "forall a, b, t Z:\n    a <= b\n    a + t <= b + t\n    =>:\n        sum(a, b, fn (k Z) R{f(k + t)}) = sum(a + t, b + t, f)",
            "why_failed": {
              "phase": "search_proof",
              "goal": "forall a, b, t Z:\n    a <= b\n    a + t <= b + t\n    =>:\n        sum(a, b, fn (k Z) R{f(k + t)}) = sum(a + t, b + t, f)"
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
