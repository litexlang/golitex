# Object audit: finite_set_reduce

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `kernel_problem` (provisional), except a documented unsupported signature or checked authoring route is non-kernel debt. Repair ownership: provisional, diagnosing; check explicit existing proof paths before proposing local Rust work. Escalate before changing shared policy or protected state/AST.

## P01

Original fixture: `examples/test_objs/finite_set_reduce.lit`.

```litex
sketch:
    finite_set_reduce({}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 7) = 7
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
            "statement": "<wd_failed>",
            "why_failed": {
              "phase": "well_defined",
              "verification": {
                "type": "equality",
                "success": false,
                "phase": "well_defined",
                "failure": {
                  "phase": "IteratedOperator",
                  "failure": {
                    "phase": "FiniteSetReduce",
                    "failure": {
                      "phase": "requirement",
                      "obj": "finite_set_reduce({}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 7)",
                      "result": {
                        "type": "forall",
                        "success": false,
                        "phase": "search_proof",
                        "fact": "forall __param_4, __param_5, __param_6 Z:\n    fn (a, b Z) Z{a + b}(__param_4, __param_5) = __param_4 + __param_5\n    fn (a, b Z) Z{a + b}(__param_5, __param_6) = __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_4, __param_5), __param_6) = fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6)\n    fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6) = __param_4 + __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(__param_4, fn (a, b Z) Z{a + b}(__param_5, __param_6)) = fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6) = __param_4 + (__param_5 + __param_6)\n    __param_4 + __param_5 + __param_6 = __param_4 + (__param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(fn (
```

## P02

Original fixture: `examples/test_objs/finite_set_reduce.lit`.

```litex
sketch:
    finite_set_reduce({2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 2
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
            "statement": "<wd_failed>",
            "why_failed": {
              "phase": "well_defined",
              "verification": {
                "type": "equality",
                "success": false,
                "phase": "well_defined",
                "failure": {
                  "phase": "IteratedOperator",
                  "failure": {
                    "phase": "FiniteSetReduce",
                    "failure": {
                      "phase": "requirement",
                      "obj": "finite_set_reduce({2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0)",
                      "result": {
                        "type": "forall",
                        "success": false,
                        "phase": "search_proof",
                        "fact": "forall __param_4, __param_5, __param_6 Z:\n    fn (a, b Z) Z{a + b}(__param_4, __param_5) = __param_4 + __param_5\n    fn (a, b Z) Z{a + b}(__param_5, __param_6) = __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_4, __param_5), __param_6) = fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6)\n    fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6) = __param_4 + __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(__param_4, fn (a, b Z) Z{a + b}(__param_5, __param_6)) = fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6) = __param_4 + (__param_5 + __param_6)\n    __param_4 + __param_5 + __param_6 = __param_4 + (__param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(fn 
```

## P03

Original fixture: `examples/test_objs/finite_set_reduce.lit`.

```litex
sketch:
    finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 3
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
            "statement": "<wd_failed>",
            "why_failed": {
              "phase": "well_defined",
              "verification": {
                "type": "equality",
                "success": false,
                "phase": "well_defined",
                "failure": {
                  "phase": "IteratedOperator",
                  "failure": {
                    "phase": "FiniteSetReduce",
                    "failure": {
                      "phase": "requirement",
                      "obj": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0)",
                      "result": {
                        "type": "forall",
                        "success": false,
                        "phase": "search_proof",
                        "fact": "forall __param_4, __param_5, __param_6 Z:\n    fn (a, b Z) Z{a + b}(__param_4, __param_5) = __param_4 + __param_5\n    fn (a, b Z) Z{a + b}(__param_5, __param_6) = __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_4, __param_5), __param_6) = fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6)\n    fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6) = __param_4 + __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(__param_4, fn (a, b Z) Z{a + b}(__param_5, __param_6)) = fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6) = __param_4 + (__param_5 + __param_6)\n    __param_4 + __param_5 + __param_6 = __param_4 + (__param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(
```

## P04

Original fixture: `examples/test_objs/finite_set_reduce.lit`.

```litex
sketch:
    finite_set_reduce({2, 1}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0) = 3
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
            "statement": "<wd_failed>",
            "why_failed": {
              "phase": "well_defined",
              "verification": {
                "type": "equality",
                "success": false,
                "phase": "well_defined",
                "failure": {
                  "phase": "IteratedOperator",
                  "failure": {
                    "phase": "FiniteSetReduce",
                    "failure": {
                      "phase": "requirement",
                      "obj": "finite_set_reduce({2, 1}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0)",
                      "result": {
                        "type": "forall",
                        "success": false,
                        "phase": "search_proof",
                        "fact": "forall __param_4, __param_5, __param_6 Z:\n    fn (a, b Z) Z{a + b}(__param_4, __param_5) = __param_4 + __param_5\n    fn (a, b Z) Z{a + b}(__param_5, __param_6) = __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_4, __param_5), __param_6) = fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6)\n    fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6) = __param_4 + __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(__param_4, fn (a, b Z) Z{a + b}(__param_5, __param_6)) = fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6) = __param_4 + (__param_5 + __param_6)\n    __param_4 + __param_5 + __param_6 = __param_4 + (__param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(
```

## P05

Original fixture: `examples/test_objs/finite_set_reduce.lit`.

```litex
sketch:
    finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 10) = 13
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
            "statement": "<wd_failed>",
            "why_failed": {
              "phase": "well_defined",
              "verification": {
                "type": "equality",
                "success": false,
                "phase": "well_defined",
                "failure": {
                  "phase": "IteratedOperator",
                  "failure": {
                    "phase": "FiniteSetReduce",
                    "failure": {
                      "phase": "requirement",
                      "obj": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 10)",
                      "result": {
                        "type": "forall",
                        "success": false,
                        "phase": "search_proof",
                        "fact": "forall __param_4, __param_5, __param_6 Z:\n    fn (a, b Z) Z{a + b}(__param_4, __param_5) = __param_4 + __param_5\n    fn (a, b Z) Z{a + b}(__param_5, __param_6) = __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_4, __param_5), __param_6) = fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6)\n    fn (a, b Z) Z{a + b}(__param_4 + __param_5, __param_6) = __param_4 + __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(__param_4, fn (a, b Z) Z{a + b}(__param_5, __param_6)) = fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6)\n    fn (a, b Z) Z{a + b}(__param_4, __param_5 + __param_6) = __param_4 + (__param_5 + __param_6)\n    __param_4 + __param_5 + __param_6 = __param_4 + (__param_5 + __param_6)\n    fn (a, b Z) Z{a + b}
```

## P90

Original fixture: `examples/test_objs/finite_set_reduce.lit`.

```litex
sketch:
    let r = finite_set_reduce({1, 2}, fn(x Z) Z {x}, fn(a, b Z) Z {a + b}, 0)
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
            "statement": "let \u2026",
            "why_failed": {
              "type": "define_obj",
              "rule_name": "Let binding",
              "message": "Bind a name to a well-defined value",
              "phase": "let",
              "failure": {
                "success": false,
                "obj": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0)",
                "phase": "well_defined",
                "failure": {
                  "phase": "IteratedOperator",
                  "failure": {
                    "phase": "FiniteSetReduce",
                    "failure": {
                      "phase": "requirement",
                      "obj": "finite_set_reduce({1, 2}, fn (x Z) Z{x}, fn (a, b Z) Z{a + b}, 0)",
                      "result": {
                        "type": "forall",
                        "success": false,
                        "phase": "search_proof",
                        "fact": "forall __param_5, __param_6, __param_7 Z:\n    fn (a, b Z) Z{a + b}(__param_5, __param_6) = __param_5 + __param_6\n    fn (a, b Z) Z{a + b}(__param_6, __param_7) = __param_6 + __param_7\n    fn (a, b Z) Z{a + b}(fn (a, b Z) Z{a + b}(__param_5, __param_6), __param_7) = fn (a, b Z) Z{a + b}(__param_5 + __param_6, __param_7)\n    fn (a, b Z) Z{a + b}(__param_5 + __param_6, __param_7) = __param_5 + __param_6 + __param_7\n    fn (a, b Z) Z{a + b}(__param_5, fn (a, b Z) Z{a + b}(__param_6, __param_7)) = fn (a, b Z) Z{a + b}(__param_5, __param_6 + __param_7)\n    fn (a, b Z) Z
```

Next/acceptance: reproduce the exact mathematical goal with the original scope; inspect WD versus search versus context/output failure; repair only after preserving the nearest false, domain and scope controls.
