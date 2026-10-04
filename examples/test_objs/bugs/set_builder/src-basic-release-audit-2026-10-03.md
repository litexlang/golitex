# Object audit: set_builder

Task: detailed src basic semantic/functionality audit requested by the maintainer on 2026-10-03.
Scope: the exact source/binary snapshot in `examples/test_statements/release_basics/proof_journals/summary.json`.
These are observed test failures, not counts of independent bugs or verified repairs.

Primary label: `kernel_problem` (provisional), except a documented unsupported signature or checked authoring route is non-kernel debt. Repair ownership: provisional, diagnosing; check explicit existing proof paths before proposing local Rust work. Escalate before changing shared policy or protected state/AST.

## P06

Original fixture: `examples/test_objs/set_builder.lit`.

```litex
sketch:
    let y = 1
    let A = {x R: x > y}
    $is_set(A)
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
            "statement": "let \u2026",
            "why_failed": {
              "type": "define_obj",
              "rule_name": "Let binding",
              "message": "Bind a name to a well-defined value",
              "phase": "let",
              "failure": {
                "success": false,
                "obj": "{x R: x > y}",
                "phase": "well_defined",
                "failure": {
                  "phase": "SetFormer",
                  "failure": {
                    "phase": "SetBuilder",
                    "failure": {
                      "phase": "fact",
                      "failure": {
                        "phase": "predicate_domain",
                        "completed_requirements": [
                          {
                            "requirement": "x $in R",
                            "verify": {
                              "type": "atomic_except_equality",
                              "success": true,
                              "fact": "x $in R",
                              "well_defined": {
                                "well_defined_of_each_parameter": [
                                  {
                                    "type": "by_def",
                                    "family": "Identifier",
                                    "kind": "Identifier",
                                    "obj": "x"
                                  },
                                  {
                                    "type": "by_known",
                        
```

Next/acceptance: reproduce the exact mathematical goal with the original scope; inspect WD versus search versus context/output failure; repair only after preserving the nearest false, domain and scope controls.
